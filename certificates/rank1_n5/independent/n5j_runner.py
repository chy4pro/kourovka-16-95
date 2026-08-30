#!/usr/bin/env python3
"""Sequential, resumable, swap-gated msolve runner for the J5 ideals."""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
RUN_CAPPED = ROOT / "encoders/line/run_capped.py"
PYTHON = Path(os.environ.get("PYTHON", "python3"))
MSOLVE = Path.home() / ".local/bin/msolve"
WALL_SECONDS = 600
MEM_KIB = 2_500_000
SWAP_LIMIT_MIB = 10 * 1024
OPTIONS = ("-g", "2", "-v", "1", "-t", "1")


def swap_used_mib() -> float:
    process = subprocess.run(["/usr/sbin/sysctl", "vm.swapusage"], capture_output=True, text=True)
    if process.returncode:
        raise RuntimeError("cannot read current swap usage: " +
                           (process.stderr.strip() or "sysctl failed"))
    match = re.search(r"used\s*=\s*([0-9.]+)([KMG])", process.stdout)
    if not match:
        raise RuntimeError("cannot parse current swap usage: " + process.stdout.strip())
    value, unit = float(match.group(1)), match.group(2)
    return value * {"K": 1 / 1024, "M": 1, "G": 1024}[unit]


def basis_is_unit(path: Path) -> bool:
    if not path.exists():
        return False
    body = "".join(line for line in path.read_text(errors="replace").splitlines()
                   if not line.startswith("#"))
    return re.sub(r"\s+", "", body).startswith("[1]")


def peak_rss_kib(log: Path) -> int | None:
    match = re.search(r"peak_rss_kib=(\d+)", log.read_text(errors="replace"))
    return int(match.group(1)) if match else None


def msolve_version() -> str:
    version_path = HERE / "msolve_version.txt"
    if version_path.exists():
        return version_path.read_text().strip()
    used = swap_used_mib()
    if used >= SWAP_LIMIT_MIB:
        raise RuntimeError(
            f"swap gate closed before version query: {used:.2f} MiB used >= {SWAP_LIMIT_MIB} MiB")
    environment = dict(os.environ)
    environment["DYLD_LIBRARY_PATH"] = str(Path.home() / ".local/lib")
    log = HERE / "msolve_version.log"
    command = [str(PYTHON), str(RUN_CAPPED), "--wall", str(WALL_SECONDS),
               "--mem", str(MEM_KIB), "--log", str(log), "--",
               str(MSOLVE), "--version"]
    process = subprocess.run(command, env=environment, text=True)
    log_text = log.read_text(errors="replace") if log.exists() else ""
    if process.returncode != 0 or "EXIT code=0" not in log_text:
        raise RuntimeError("capped msolve --version failed")
    payload = [line.strip() for line in log_text.splitlines()
               if line.strip() and not line.startswith(("START ", "CAP ", "COMMAND ", "EXIT "))]
    version = " | ".join(payload)
    if not version:
        raise RuntimeError("msolve --version returned no version text")
    version_path.write_text(version + "\n")
    (HERE / "msolve_version.json").write_text(json.dumps({
        "version": version,
        "swap_used_mib_at_start": used,
        "run_capped": {"wall_seconds": WALL_SECONDS, "memory_kib": MEM_KIB},
        "log": str(log),
    }, indent=2) + "\n")
    return version


def reduce_polynomial_text(polynomial: str, characteristic: int) -> str | None:
    """Reduce an expanded integer polynomial without reparsing huge expressions."""
    if characteristic == 0:
        return polynomial
    terms: list[str] = []
    for raw in polynomial.replace(" - ", " + -").split(" + "):
        body = raw.strip()
        negative = body.startswith("-")
        if negative:
            body = body[1:]
        factors = body.split("*")
        if factors[0].isdigit():
            coefficient = int(factors.pop(0))
        else:
            coefficient = 1
        if negative:
            coefficient = -coefficient
        coefficient %= characteristic
        if coefficient == 0:
            continue
        monomial = "*".join(factors)
        if monomial:
            terms.append(monomial if coefficient == 1 else f"{coefficient}*{monomial}")
        else:
            terms.append(str(coefficient))
    return " + ".join(terms) if terms else None


def write_ideal(path: Path, characteristic: int, variables: list[str],
                polynomials: list[str]) -> list[str]:
    reduced = [value for polynomial in polynomials
               if (value := reduce_polynomial_text(polynomial, characteristic)) is not None]
    assert reduced
    path.parent.mkdir(parents=True, exist_ok=True)
    body = ",\n".join(polynomial.replace("**", "^") for polynomial in reduced)
    path.write_text(",".join(variables) + f"\n{characteristic}\n" + body + "\n")
    return reduced


def run_ideal(tag: str, characteristic: int, variables: list[str],
              polynomials: list[str], output_dir: Path, extra: dict | None = None) -> dict:
    version = msolve_version()
    used = swap_used_mib()
    if used >= SWAP_LIMIT_MIB:
        raise RuntimeError(
            f"swap gate closed: {used:.2f} MiB used >= {SWAP_LIMIT_MIB} MiB")
    source = output_dir / f"{tag}.ms"
    basis = output_dir / f"{tag}.gb"
    log = output_dir / f"{tag}.log"
    metadata = output_dir / f"{tag}.json"
    reduced_polynomials = write_ideal(source, characteristic, variables, polynomials)
    environment = dict(os.environ)
    environment["DYLD_LIBRARY_PATH"] = str(Path.home() / ".local/lib")
    command = [
        str(PYTHON), str(RUN_CAPPED), "--wall", str(WALL_SECONDS),
        "--mem", str(MEM_KIB), "--log", str(log), "--", str(MSOLVE),
        *OPTIONS, "-f", str(source), "-o", str(basis),
    ]
    started = time.time()
    process = subprocess.run(command, env=environment, text=True)
    seconds = time.time() - started
    log_text = log.read_text(errors="replace") if log.exists() else ""
    capped = "UNRESOLVED cap=" in log_text
    exit_match = re.search(r"EXIT code=(-?\d+)", log_text)
    child_returncode = int(exit_match.group(1)) if exit_match else None
    unit = child_returncode == 0 and not capped and basis_is_unit(basis)
    status = ("UNIT" if unit else
              ("UNRESOLVED-due-to-load" if capped else
               ("NONUNIT" if child_returncode == 0 else "ERROR")))
    result = {
        "tag": tag,
        "characteristic": characteristic,
        "variables": variables,
        "integer_generator_count": len(polynomials),
        "generator_count": len(reduced_polynomials),
        "source": str(source),
        "basis": str(basis),
        "log": str(log),
        "msolve_version": version,
        "msolve_options": list(OPTIONS),
        "run_capped": {"wall_seconds": WALL_SECONDS, "memory_kib": MEM_KIB},
        "swap_limit_mib": SWAP_LIMIT_MIB,
        "swap_used_mib_at_start": used,
        "seconds": round(seconds, 3),
        "peak_rss_kib": peak_rss_kib(log) if log.exists() else None,
        "wrapper_returncode": process.returncode,
        "child_returncode": child_returncode,
        "capped": capped,
        "unit": unit,
        "status": status,
        **(extra or {}),
    }
    metadata.write_text(json.dumps(result, indent=2) + "\n")
    return result


def primes_below(limit: int) -> list[int]:
    primes: list[int] = []
    for candidate in range(2, limit):
        if all(candidate % prime for prime in primes if prime * prime <= candidate):
            primes.append(candidate)
    return primes


def ordered_characteristics() -> list[int]:
    priority = [3, 2, 5, 7, 0]
    return priority + [prime for prime in primes_below(2000) if prime not in priority]


def load_polynomials() -> tuple[list[str], list[str]]:
    bundle = json.loads((HERE / "j5_polynomials.json").read_text())
    assert bundle["total_determinants"] == 120 and bundle["nonzero"] == 74
    return bundle["variables"], [row["polynomial"] for row in bundle["determinants"]
                                 if not row["zero"]]


def scan(max_new_runs: int | None = None) -> dict:
    state_path = HERE / "prime_results.json"
    if state_path.exists():
        state = json.loads(state_path.read_text())
    else:
        state = {"order": ordered_characteristics(), "results": [], "blocked_reason": None}
    assert state["order"] == ordered_characteristics()
    completed = {row["characteristic"] for row in state["results"]}
    variables, polynomials = load_polynomials()
    new_runs = 0
    state["blocked_reason"] = None
    for characteristic in state["order"]:
        if characteristic in completed:
            continue
        if max_new_runs is not None and new_runs >= max_new_runs:
            break
        tag = "q" if characteristic == 0 else f"p{characteristic}"
        try:
            result = run_ideal(tag, characteristic, variables, polynomials,
                               HERE,
                               {"ideal": "J5-all-74-nonzero-determinants"})
        except RuntimeError as error:
            state["blocked_reason"] = str(error)
            break
        state["results"].append(result)
        new_runs += 1
        state["completed"] = len(state["results"])
        state["all_unit"] = all(row["status"] == "UNIT" for row in state["results"])
        state["exhaustive"] = len(state["results"]) == len(state["order"])
        state_path.write_text(json.dumps(state, indent=2) + "\n")
        print(json.dumps({key: result[key] for key in (
            "characteristic", "status", "seconds", "peak_rss_kib",
            "swap_used_mib_at_start")}), flush=True)
        if result["status"] != "UNIT":
            break
    state["completed"] = len(state["results"])
    state["all_unit"] = all(row["status"] == "UNIT" for row in state["results"])
    state["exhaustive"] = len(state["results"]) == len(state["order"])
    state["new_runs"] = new_runs
    state_path.write_text(json.dumps(state, indent=2) + "\n")
    return state


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-new-runs", type=int)
    parser.add_argument("--swap-only", action="store_true")
    args = parser.parse_args()
    if args.swap_only:
        print(json.dumps({"swap_used_mib": swap_used_mib(), "limit_mib": SWAP_LIMIT_MIB}))
        return
    state = scan(args.max_new_runs)
    print("SUMMARY " + json.dumps({key: state[key] for key in (
        "completed", "all_unit", "exhaustive", "blocked_reason", "new_runs")}), flush=True)


if __name__ == "__main__":
    try:
        main()
    except RuntimeError as error:
        print(f"ERROR: {error}")
        raise SystemExit(2)

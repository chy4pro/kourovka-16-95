#!/usr/bin/env python3
"""Sequential, resumable DPLL-like msolve search for K6-R2SPLIT.

Every msolve process is launched through problems/k1695/run_capped.py with a
2,500,000 KiB aggregate-RSS cap and a 600 second wall cap.  This script also
refuses to launch when current macOS swap usage cannot be established or is
10 GiB or more.  It never runs two msolve children concurrently.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path

from r2split_encoder import Case, PERMS, all_case_lists, case_list, cycle_type, parse_case, write_msolve

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
RUN_CAPPED = HERE.parent / "line/run_capped.py"
PYTHON = Path(sys.executable)
MSOLVE = Path(os.environ.get("MSOLVE", "msolve"))
MEM_KIB = 2_500_000
WALL_SECONDS = 600
SWAP_LIMIT_MIB = 10 * 1024


def swap_used_mib() -> float:
    proc = subprocess.run(["/usr/sbin/sysctl", "vm.swapusage"], capture_output=True, text=True)
    if proc.returncode:
        raise RuntimeError("cannot read current swap usage: " + (proc.stderr.strip() or "sysctl failed"))
    match = re.search(r"used\s*=\s*([0-9.]+)([KMG])", proc.stdout)
    if not match:
        raise RuntimeError("cannot parse current swap usage: " + proc.stdout.strip())
    value, unit = float(match.group(1)), match.group(2)
    return value * {"K": 1 / 1024, "M": 1, "G": 1024}[unit]


def basis_is_unit(path: Path) -> bool:
    if not path.exists():
        return False
    body = "".join(line for line in path.read_text(errors="replace").splitlines() if not line.startswith("#"))
    return re.sub(r"\s+", "", body).startswith("[1]")


def safe_tag(cases: list[Case], u_chart: int) -> str:
    suffix = "root" if not cases else "__".join(f"s{c.perm_index:02d}_{c.label}" for c in cases)
    tag = f"uc{u_chart}__{suffix}"
    if len(tag) > 180:
        digest = hashlib.sha256(tag.encode()).hexdigest()[:16]
        tag = f"uc{u_chart}__d{len(cases):02d}__{digest}"
    return tag


def run_branch(characteristic: int, cases: list[Case], output_dir: Path, u_chart: int) -> dict:
    used = swap_used_mib()
    if used >= SWAP_LIMIT_MIB:
        raise RuntimeError(f"swap gate closed: {used:.2f} MiB used >= {SWAP_LIMIT_MIB} MiB")
    tag = safe_tag(cases, u_chart)
    ideal_path = output_dir / f"p{characteristic}_{tag}.ms"
    gb_path = ideal_path.with_suffix(".gb")
    log_path = ideal_path.with_suffix(".log")
    meta = write_msolve(ideal_path, characteristic, cases, u_chart)
    env = dict(os.environ)
    env["DYLD_LIBRARY_PATH"] = str(Path.home() / ".local/lib")
    command = [
        str(PYTHON), str(RUN_CAPPED), "--wall", str(WALL_SECONDS), "--mem", str(MEM_KIB),
        "--log", str(log_path), "--", str(MSOLVE), "-g", "2", "-v", "1", "-t", "1",
        "-f", str(ideal_path), "-o", str(gb_path),
    ]
    started = time.time()
    proc = subprocess.run(command, env=env, text=True)
    elapsed = time.time() - started
    log_text = log_path.read_text(errors="replace") if log_path.exists() else ""
    capped = "UNRESOLVED cap=" in log_text
    exit_match = re.search(r"EXIT code=(-?\d+)", log_text)
    child_returncode = int(exit_match.group(1)) if exit_match else None
    unit = child_returncode == 0 and not capped and basis_is_unit(gb_path)
    result = {
        **meta,
        "tag": tag,
        "gb": str(gb_path),
        "log": str(log_path),
        "swap_used_mib_at_start": used,
        "seconds": round(elapsed, 3),
        "wrapper_returncode": proc.returncode,
        "child_returncode": child_returncode,
        "capped": capped,
        "unit": unit,
        "status": "UNIT" if unit else ("OPEN-due-to-load" if capped else "NONUNIT"),
    }
    with ideal_path.with_suffix(".json").open("w") as handle:
        json.dump(result, handle, indent=2)
        handle.write("\n")
    return result


def ordered_permutations(characteristic: int) -> list[int]:
    return sorted(range(len(PERMS)), key=lambda i: (len(case_list(characteristic, i)), cycle_type(PERMS[i]), i))


def probe_sets(characteristic: int) -> list[tuple[str, list[Case]]]:
    if characteristic != 2:
        return []
    trans = [i for i, s in enumerate(PERMS) if cycle_type(s) == (2, 1, 1)]
    doubles = [i for i, s in enumerate(PERMS) if cycle_type(s) == (2, 2)]
    fours = [i for i, s in enumerate(PERMS) if cycle_type(s) == (4,)]
    # Conjugating the R2CHAR2 matrix (8) by coordinate order (1,3,2,4)
    # gives the ticket chart with
    # U rows (11,01,11,01), W rows (10,01,10,01).  Direct row reduction
    # shows rank(AP_sigma-I)<=2 for precisely these listed E_1 cases.
    witness_e1 = [2, 3, 4, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21]
    return [
        ("gf2_witness_E1", [parse_case(2, f"{i}:E_1") for i in witness_e1]),
        ("all_trans_E1", [parse_case(2, f"{i}:E_1") for i in trans]),
        ("all_double_E1", [parse_case(2, f"{i}:E_1") for i in doubles]),
        ("all_four_N", [parse_case(2, f"{i}:N") for i in fours]),
    ]


def run_probes(characteristic: int, output_dir: Path, names: set[str] | None, u_chart: int) -> list[dict]:
    results = []
    for name, cases in probe_sets(characteristic):
        if names is not None and name not in names:
            continue
        result = run_branch(characteristic, cases, output_dir / "probes", u_chart)
        result["probe"] = name
        results.append(result)
        print(json.dumps(result), flush=True)
        if result["capped"]:
            break
    return results


def dpll(characteristic: int, output_dir: Path, max_runs: int, start_depth: int, u_chart: int) -> dict:
    """Resumable depth-first branch/prune search with a per-invocation run budget."""
    order = ordered_permutations(characteristic)
    state_path = output_dir / f"state_p{characteristic}_uc{u_chart}.json"

    def encode_node(node: tuple[int, list[Case], bool]) -> dict:
        return {"depth": node[0], "cases": [c.key for c in node[1]], "needs_test": node[2]}

    def decode_node(node: dict) -> tuple[int, list[Case], bool]:
        return node["depth"], [parse_case(characteristic, key) for key in node["cases"]], node["needs_test"]

    if state_path.exists():
        old = json.loads(state_path.read_text())
        if old["start_depth"] != start_depth or old["permutation_order"] != order:
            raise RuntimeError(f"existing state {state_path} uses different search parameters")
        stack = [decode_node(node) for node in old["pending"]]
        runs = old["results"]
        closed = old["closed_subtrees"]
        complete_leaves = old["complete_nonunit_leaves"]
        open_due_to_load = old["open_due_to_load"]
        known_core_prunes = old.get("known_core_prunes", 0)
    else:
        stack: list[tuple[int, list[Case], bool]] = [(0, [], False)]
        runs: list[dict] = []
        closed = complete_leaves = open_due_to_load = known_core_prunes = 0

    invocation_runs = 0
    blocked_reason = None
    trans_e1 = {(i, "E_1") for i, s in enumerate(PERMS) if cycle_type(s) == (2, 1, 1)} if characteristic == 2 else set()
    while stack:
        depth, prefix, needs_test = stack.pop()
        if needs_test:
            if invocation_runs >= max_runs:
                stack.append((depth, prefix, needs_test))
                break
            chosen = {(case.perm_index, case.label) for case in prefix}
            if trans_e1 and trans_e1 <= chosen:
                closed += 1
                known_core_prunes += 1
                continue
            try:
                result = run_branch(characteristic, prefix, output_dir / "branches", u_chart)
            except RuntimeError as error:
                stack.append((depth, prefix, needs_test))
                blocked_reason = str(error)
                break
            runs.append(result)
            invocation_runs += 1
            print(json.dumps(result), flush=True)
            if result["unit"]:
                closed += 1
                continue
            if result["capped"]:
                open_due_to_load += 1
                continue
        if depth == len(order):
            complete_leaves += 1
            continue
        index = order[depth]
        for case in reversed(case_list(characteristic, index)):
            child = prefix + [case]
            stack.append((depth + 1, child, depth + 1 >= start_depth))
    summary = {
        "characteristic": characteristic,
        "u_chart": u_chart,
        "start_depth": start_depth,
        "permutation_order": order,
        "runs": len(runs),
        "invocation_runs": invocation_runs,
        "closed_subtrees": closed,
        "known_core_prunes": known_core_prunes,
        "complete_nonunit_leaves": complete_leaves,
        "open_due_to_load": open_due_to_load,
        "pending_nodes": len(stack),
        "blocked_reason": blocked_reason,
        "exhaustive": not stack and complete_leaves == 0 and open_due_to_load == 0 and blocked_reason is None,
        "results": runs,
        "pending": [encode_node(node) for node in stack],
    }
    output_dir.mkdir(parents=True, exist_ok=True)
    state_path.write_text(json.dumps(summary, indent=2) + "\n")
    (output_dir / f"search_p{characteristic}_uc{u_chart}.json").write_text(json.dumps(summary, indent=2) + "\n")
    return summary


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--characteristic", "-p", type=int, choices=(2, 3, 5, 7), default=2)
    parser.add_argument("--output-dir", type=Path, default=HERE / "certificates")
    parser.add_argument("--u-chart", type=int, choices=range(6), default=0,
                        help="exact-rank-two cover: invert one of the six U row minors")
    parser.add_argument("--probe", action="append", help="run named small probe (repeatable); 'all' runs all")
    parser.add_argument("--dpll", action="store_true")
    parser.add_argument("--max-runs", type=int, default=1)
    parser.add_argument("--start-depth", type=int, default=1)
    parser.add_argument("--swap-only", action="store_true")
    args = parser.parse_args()
    if args.swap_only:
        print(json.dumps({"swap_used_mib": swap_used_mib(), "limit_mib": SWAP_LIMIT_MIB}))
        return
    if args.probe:
        selected = None if "all" in args.probe else set(args.probe)
        run_probes(args.characteristic, args.output_dir, selected, args.u_chart)
    if args.dpll:
        print(json.dumps(dpll(args.characteristic, args.output_dir, args.max_runs, args.start_depth, args.u_chart), indent=2))
    if not args.probe and not args.dpll:
        parser.error("choose --probe, --dpll, or --swap-only")


if __name__ == "__main__":
    try:
        main()
    except RuntimeError as error:
        print(f"ERROR: {error}", file=sys.stderr)
        raise SystemExit(2)

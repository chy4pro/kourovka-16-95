#!/usr/bin/env python3
"""Independent replay verifier for K6-R2SPLIT-1113 certificates."""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import re
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPRESENTATIVES = (0, 1, 5)
ORDER = (0, 1, 4, 5, 13, 20, 6, 15, 22, 2, 3, 7, 10, 11, 14, 18, 19, 8, 9, 12, 16, 17, 21)
PERMS = tuple(p for p in itertools.permutations(range(4)) if p != tuple(range(4)))
CHARTS = tuple(itertools.combinations(range(4), 2))
U = [[-1, 0], [0, -1], [0, 1], [1, 0]]
A = [[0, 0, 0, 1], [0, 0, 1, 0], [0, 1, 0, 0], [1, 0, 0, 0]]


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def rank_mod(matrix: list[list[int]], p: int) -> int:
    work = [[value % p for value in row] for row in matrix]
    pivot_row = 0
    for column in range(len(work[0])):
        pivot = next((row for row in range(pivot_row, len(work)) if work[row][column]), None)
        if pivot is None:
            continue
        work[pivot_row], work[pivot] = work[pivot], work[pivot_row]
        inverse = pow(work[pivot_row][column], -1, p)
        work[pivot_row] = [(value * inverse) % p for value in work[pivot_row]]
        for row in range(len(work)):
            if row != pivot_row and work[row][column]:
                factor = work[row][column]
                work[row] = [
                    (work[row][j] - factor * work[pivot_row][j]) % p
                    for j in range(len(work[0]))
                ]
        pivot_row += 1
        if pivot_row == len(work):
            break
    return pivot_row


def multiply(left: list[list[int]], right: list[list[int]], p: int) -> list[list[int]]:
    return [[sum(left[i][k] * right[k][j] for k in range(4)) % p
             for j in range(4)] for i in range(4)]


def matrix_power(matrix: list[list[int]], exponent: int, p: int) -> list[list[int]]:
    result = [[int(i == j) for j in range(4)] for i in range(4)]
    for _ in range(exponent):
        result = multiply(result, matrix, p)
    return result


def permutation_matrix(permutation: tuple[int, ...]) -> list[list[int]]:
    return [[int(permutation[j] == i) for j in range(4)] for i in range(4)]


def control_classification(p: int) -> tuple[list[str], list[dict]]:
    identity = [[int(i == j) for j in range(4)] for i in range(4)]
    cases: list[str] = []
    audit: list[dict] = []
    for index, permutation in enumerate(PERMS):
        b = multiply(A, permutation_matrix(permutation), p)
        powers = [[entry for row in matrix_power(b, exponent, p) for entry in row]
                  for exponent in range(4)]
        cyclic_rank = rank_mod([[powers[column][row] for column in range(4)]
                                for row in range(16)], p)
        rank_minus = rank_mod([[(b[i][j] - identity[i][j]) % p for j in range(4)]
                               for i in range(4)], p)
        rank_plus = rank_mod([[(b[i][j] + identity[i][j]) % p for j in range(4)]
                              for i in range(4)], p)
        label = "CYCLIC" if cyclic_rank == 4 else (
            "E_1" if rank_minus <= 2 else ("E_m1" if rank_plus <= 2 else "N"))
        if label != "CYCLIC":
            cases.append(f"{index}:{label}")
        audit.append({
            "permutation": index,
            "cyclic_rank": cyclic_rank,
            "rank_B_minus_I": rank_minus,
            "rank_B_plus_I": rank_plus,
            "classification": label,
        })
    return cases, audit


def cycle_type(permutation: tuple[int, ...]) -> tuple[int, ...]:
    seen: set[int] = set()
    lengths: list[int] = []
    for start in range(4):
        if start in seen:
            continue
        at, length = start, 0
        while at not in seen:
            seen.add(at)
            at = permutation[at]
            length += 1
        lengths.append(length)
    return tuple(sorted(lengths, reverse=True))


def labels(p: int, index: int) -> tuple[str, ...]:
    ctype = cycle_type(PERMS[index])
    roots = ["E_1"]
    if any(length % 2 == 0 for length in ctype):
        roots.append("E_m1")
    if 3 in ctype:
        roots += ["E_omega", "E_omega2"] if p == 11 else ["E_3", "E_9"]
    if 4 in ctype:
        roots += ["E_i", "E_mi"] if p == 11 else ["E_5", "E_8"]
    return tuple(roots + ["N"])


def terse_text(text: str) -> str:
    match = re.fullmatch(r"s(\d+)_[0-9]+:(E_[A-Za-z0-9]+|N)", text)
    assert match, f"unrecognised case {text!r}"
    return f"{int(match.group(1))}:{match.group(2)}"


def terse_cases(row: dict) -> tuple[str, ...]:
    return tuple(terse_text(text) for text in row["cases"])


def basis_starts_unit(path: Path) -> bool:
    body = "".join(line for line in path.read_text(errors="replace").splitlines()
                   if not line.startswith("#"))
    return re.sub(r"\s+", "", body).startswith("[1]")


def verify_result(p: int, row: dict, prefix: tuple[str, ...]) -> None:
    assert terse_cases(row) == prefix
    assert row["characteristic"] == p
    assert row["wrapper_returncode"] == 0 and row["child_returncode"] == 0
    assert not row["capped"]
    source, log, gb = Path(row["path"]), Path(row["log"]), Path(row["gb"])
    assert source.is_file() and log.is_file() and gb.is_file()
    source_text = source.read_text(errors="replace")
    source_lines = source_text.splitlines()
    assert len(source_lines) >= 3 and source_lines[1].strip() == str(p)
    if p == 11 and any("E_omega" in case or "E_omega2" in case for case in prefix):
        assert "omega^2 + omega + 1" in source_text
    if p == 11 and any("E_i" in case or "E_mi" in case for case in prefix):
        assert "ii^2 + 1" in source_text
    log_text = log.read_text(errors="replace")
    assert "UNRESOLVED cap=" not in log_text and "EXIT code=0" in log_text
    if row["status"] == "UNIT":
        assert row["unit"] and basis_starts_unit(gb)
    elif row["status"] == "NONUNIT":
        assert not row["unit"] and not basis_starts_unit(gb)
    else:
        raise AssertionError(f"unexpected status {row['status']}")


def verify_inventory(p: int) -> dict:
    path = HERE / f"inventory_p{p}.json"
    report = json.loads(path.read_text())
    assert report["characteristic"] == p and len(report["permutations"]) == 23
    for index, row in enumerate(report["permutations"]):
        assert row["index"] == index
        assert tuple(row["one_line"]) == tuple(value + 1 for value in PERMS[index])
        assert tuple(row["cycle_type"]) == cycle_type(PERMS[index])
        assert tuple(row["cases"]) == labels(p, index)
    return {"sha256": digest(path), "permutations": 23, "verified": True}


def verify_tree(p: int, chart: int) -> dict:
    path = HERE / "certificates" / f"state_p{p}_uc{chart}.json"
    state = json.loads(path.read_text())
    assert state["characteristic"] == p and state["u_chart"] == chart
    assert tuple(state["permutation_order"]) == ORDER and state["start_depth"] == 6
    rows = {terse_cases(row): row for row in state["results"]}
    assert len(rows) == len(state["results"])
    visited: set[tuple[str, ...]] = set()
    counts: Counter[str] = Counter()
    candidates: list[tuple[str, ...]] = []

    def walk(depth: int, prefix: tuple[str, ...]) -> None:
        if depth >= 6:
            assert prefix in rows, f"missing prefix {prefix}"
            row = rows[prefix]
            verify_result(p, row, prefix)
            visited.add(prefix)
            counts[row["status"]] += 1
            if row["status"] == "UNIT":
                return
        if depth == len(ORDER):
            candidates.append(prefix)
            return
        index = ORDER[depth]
        for label in labels(p, index):
            walk(depth + 1, prefix + (f"{index}:{label}",))

    walk(0, ())
    assert visited == set(rows)
    assert not state["pending"] and state["pending_nodes"] == 0
    assert state["open_due_to_load"] == 0 and state.get("blocked_reason") is None
    assert state["closed_subtrees"] == counts["UNIT"]
    assert state["complete_nonunit_leaves"] == len(candidates) == 0
    assert state["candidate_leaves"] == [] and state["exhaustive"]
    return {
        "characteristic": p,
        "u_chart": chart,
        "state_sha256": digest(path),
        "tested_nodes": len(rows),
        "status_counts": dict(counts),
        "candidate_leaves": 0,
        "max_depth": max(map(len, rows), default=0),
        "max_seconds": max((row["seconds"] for row in rows.values()), default=0),
        "max_peak_rss_kib": max((row.get("peak_rss_kib") or 0 for row in rows.values()), default=0),
        "verified": True,
    }


def symmetry_orbits() -> list[list[int]]:
    generators = ((1, 0, 2, 3), (0, 1, 3, 2))
    unseen, orbits = set(range(6)), []
    while unseen:
        orbit = {min(unseen)}
        changed = True
        while changed:
            changed = False
            for chart in tuple(orbit):
                for permutation in generators:
                    pair = tuple(sorted(permutation[row] for row in CHARTS[chart]))
                    image = CHARTS.index(pair)
                    if image not in orbit:
                        orbit.add(image)
                        changed = True
        unseen -= orbit
        orbits.append(sorted(orbit))
    assert orbits == [[0], [1, 2, 3, 4], [5]]
    return orbits


def verify_control(p: int, chart: int) -> dict:
    path = HERE / f"controls_p{p}_uc{chart}.json"
    report = json.loads(path.read_text())
    cases, audit = control_classification(p)
    expected = [f"{index}:E_1" for index in (1, 2, 3, 6, 7, 8, 10, 11, 14, 15, 16, 17, 18, 19, 20, 21, 22)]
    assert report["characteristic"] == p and report["u_chart"] == chart
    assert report["matrix"] == A and report["U"] == U
    assert report["rank_U"] == report["rank_W"] == report["rank_A_minus_I"] == 2
    assert report["case_keys"] == cases == expected and report["classification"] == audit
    rows = CHARTS[chart]
    minor = (U[rows[0]][0] * U[rows[1]][1] - U[rows[0]][1] * U[rows[1]][0]) % p
    assert minor == report["u_chart_minor"] != 0
    verify_result(p, report["result"], tuple(cases))
    assert report["result"]["status"] == "NONUNIT" and report["passed"]
    return {"sha256": digest(path), "status": "NONUNIT", "case_keys": cases, "verified": True}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=HERE / "verification.json")
    parser.add_argument("--characteristic", "-p", type=int, choices=(11, 13), action="append")
    args = parser.parse_args()
    characteristics = args.characteristic or [11, 13]
    report = {
        "characteristics": characteristics,
        "symmetry_orbits": symmetry_orbits(),
        "representatives": list(REPRESENTATIVES),
        "primes": [],
    }
    for p in characteristics:
        prime = {"characteristic": p, "inventory": verify_inventory(p), "charts": []}
        for chart in REPRESENTATIVES:
            row = verify_tree(p, chart)
            row["control"] = verify_control(p, chart)
            prime["charts"].append(row)
        report["primes"].append(prime)
    report["verified"] = True
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()

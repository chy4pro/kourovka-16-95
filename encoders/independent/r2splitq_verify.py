#!/usr/bin/env python3
"""Independent replay verifier for K6-R2SPLIT-Q certificates."""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import re
from collections import Counter
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPRESENTATIVES = (0, 1, 5)
ORDER = (0, 1, 4, 5, 13, 20, 6, 15, 22, 2, 3, 7, 10, 11, 14, 18, 19, 8, 9, 12, 16, 17, 21)
PERMS = tuple(p for p in itertools.permutations(range(4)) if p != tuple(range(4)))
CHARTS = tuple(itertools.combinations(range(4), 2))


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def rank(matrix: list[list[int | Fraction]]) -> int:
    work = [[Fraction(value) for value in row] for row in matrix]
    rows, cols = len(work), len(work[0])
    pivot_row = 0
    for col in range(cols):
        pivot = next((row for row in range(pivot_row, rows) if work[row][col]), None)
        if pivot is None:
            continue
        work[pivot_row], work[pivot] = work[pivot], work[pivot_row]
        scale = work[pivot_row][col]
        work[pivot_row] = [value / scale for value in work[pivot_row]]
        for row in range(rows):
            if row != pivot_row and work[row][col]:
                factor = work[row][col]
                work[row] = [work[row][j] - factor * work[pivot_row][j] for j in range(cols)]
        pivot_row += 1
        if pivot_row == rows:
            break
    return pivot_row


def multiply(left: list[list[int]], right: list[list[int]]) -> list[list[int]]:
    return [[sum(left[i][k] * right[k][j] for k in range(4)) for j in range(4)] for i in range(4)]


def add(left: list[list[int]], right: list[list[int]], sign: int = 1) -> list[list[int]]:
    return [[left[i][j] + sign * right[i][j] for j in range(4)] for i in range(4)]


def power(matrix: list[list[int]], exponent: int) -> list[list[int]]:
    answer = [[int(i == j) for j in range(4)] for i in range(4)]
    for _ in range(exponent):
        answer = multiply(answer, matrix)
    return answer


def permutation_matrix(permutation: tuple[int, ...]) -> list[list[int]]:
    return [[int(permutation[j] == i) for j in range(4)] for i in range(4)]


def control_classification() -> tuple[list[str], list[dict]]:
    identity = [[int(i == j) for j in range(4)] for i in range(4)]
    a = [[0, 0, 0, 1], [0, 0, 1, 0], [0, 1, 0, 0], [1, 0, 0, 0]]
    cases, audit = [], []
    for index in ORDER[:9]:
        b = multiply(a, permutation_matrix(PERMS[index]))
        columns = [[entry for row in power(b, exponent) for entry in row] for exponent in range(4)]
        cyclic_rank = rank([[columns[col][row] for col in range(4)] for row in range(16)])
        rank_minus = rank(add(b, identity, -1))
        rank_plus = rank(add(b, identity, 1))
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
    seen, lengths = set(), []
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


def labels(index: int) -> tuple[str, ...]:
    ctype = cycle_type(PERMS[index])
    roots = ["E_1"]
    if any(length % 2 == 0 for length in ctype):
        roots.append("E_m1")
    if 3 in ctype:
        roots += ["E_omega", "E_omega2"]
    if 4 in ctype:
        roots += ["E_i", "E_mi"]
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


def verify_result(row: dict, prefix: tuple[str, ...]) -> None:
    assert terse_cases(row) == prefix
    assert row["characteristic"] == 0
    assert row["wrapper_returncode"] == 0 and row["child_returncode"] == 0
    assert not row["capped"]
    source, log, gb = Path(row["path"]), Path(row["log"]), Path(row["gb"])
    assert source.is_file() and log.is_file() and gb.is_file()
    source_text = source.read_text(errors="replace")
    source_lines = source_text.splitlines()
    assert len(source_lines) >= 3 and source_lines[1].strip() == "0"
    if any("E_omega" in case for case in prefix):
        assert "omega^2 + omega + 1" in source_text
    if any("E_i" in case or "E_mi" in case for case in prefix):
        assert "ii^2 + 1" in source_text
    log_text = log.read_text(errors="replace")
    assert "UNRESOLVED cap=" not in log_text and "EXIT code=0" in log_text
    if row["status"] == "UNIT":
        assert row["unit"] and basis_starts_unit(gb)
    elif row["status"] == "NONUNIT":
        assert not row["unit"] and not basis_starts_unit(gb)
    else:
        raise AssertionError(f"unexpected status {row['status']}")


def verify_tree(chart: int) -> dict:
    path = HERE / "certificates" / f"state_p0_uc{chart}.json"
    state = json.loads(path.read_text())
    assert state["characteristic"] == 0 and state["u_chart"] == chart
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
            verify_result(row, prefix)
            visited.add(prefix)
            counts[row["status"]] += 1
            if row["status"] == "UNIT":
                return
        if depth == len(ORDER):
            candidates.append(prefix)
            return
        index = ORDER[depth]
        for label in labels(index):
            walk(depth + 1, prefix + (f"{index}:{label}",))

    walk(0, ())
    assert visited == set(rows)
    assert not state["pending"] and state["pending_nodes"] == 0
    assert state["open_due_to_load"] == 0 and state.get("blocked_reason") is None
    assert state["closed_subtrees"] == counts["UNIT"]
    assert state["complete_nonunit_leaves"] == len(candidates) == 0
    assert state["candidate_leaves"] == [] and state["exhaustive"]
    return {
        "u_chart": chart,
        "state_sha256": digest(path),
        "tested_nodes": len(rows),
        "status_counts": dict(counts),
        "candidate_leaves": 0,
        "max_depth": max(map(len, rows), default=0),
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


def verify_control(chart: int) -> dict:
    report = json.loads((HERE / f"controls_p0_uc{chart}.json").read_text())
    cases, audit = control_classification()
    assert report["matrix"] == [[0, 0, 0, 1], [0, 0, 1, 0], [0, 1, 0, 0], [1, 0, 0, 0]]
    assert report["rank_A_minus_I"] == 2 and report["det_A"] == 1
    assert report["case_keys"] == cases and report["classification"] == audit
    assert cases == ["1:E_1", "20:E_1", "6:E_1", "15:E_1", "22:E_1"]
    u = report["U"]
    rows = CHARTS[chart]
    minor = u[rows[0]][0] * u[rows[1]][1] - u[rows[0]][1] * u[rows[1]][0]
    assert minor == report["u_chart_minor"] != 0
    result = report["result"]
    verify_result(result, tuple(cases))
    assert result["status"] == "NONUNIT" and report["passed"]
    return {"status": result["status"], "case_keys": cases, "verified": True}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=HERE / "verification.json")
    args = parser.parse_args()
    report = {
        "characteristic": 0,
        "symmetry_orbits": symmetry_orbits(),
        "representatives": list(REPRESENTATIVES),
        "charts": [],
    }
    for chart in REPRESENTATIVES:
        row = verify_tree(chart)
        row["control"] = verify_control(chart)
        report["charts"].append(row)
    report["verified"] = True
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()

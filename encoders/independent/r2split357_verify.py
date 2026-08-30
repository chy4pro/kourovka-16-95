#!/usr/bin/env python3
"""Independent structural verifier for the K6-R2SPLIT-357 certificates.

This verifier does not invoke msolve.  It replays the ternary branch tree from
the recorded cases, checks that every pruned node has an actual unit basis and
clean capped-wrapper log, validates the required controls, and checks the
three-orbit reduction of the six exact-rank-two U charts.
"""
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
PERMS = tuple(permutation for permutation in itertools.permutations(range(4))
              if permutation != tuple(range(4)))


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def basis_starts_unit(path: Path) -> bool:
    body = "".join(line for line in path.read_text(errors="replace").splitlines()
                   if not line.startswith("#"))
    return re.sub(r"\s+", "", body).startswith("[1]")


def terse_text(text: str) -> str:
    match = re.fullmatch(r"s(\d+)_[0-9]+:(E_[A-Za-z0-9]+|N)", text)
    if not match:
        raise AssertionError(f"unrecognised recorded case {text!r}")
    return f"{int(match.group(1))}:{match.group(2)}"


def terse_cases(row: dict) -> tuple[str, ...]:
    answer = []
    for text in row["cases"]:
        answer.append(terse_text(text))
    return tuple(answer)


def cycle_type(permutation: tuple[int, ...]) -> tuple[int, ...]:
    seen = set()
    lengths = []
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


def labels(characteristic: int, permutation: int) -> tuple[str, ...]:
    assert characteristic in (3, 5, 7) and 0 <= permutation < 23
    ctype = cycle_type(PERMS[permutation])
    roots = ["E_1"]
    if any(length % 2 == 0 for length in ctype):
        roots.append("E_m1")
    if 3 in ctype:
        roots += ["E_omega", "E_omega2"] if characteristic == 5 else (
            ["E_2", "E_4"] if characteristic == 7 else [])
    if 4 in ctype:
        roots += ["E_2", "E_m2"] if characteristic == 5 else ["E_i", "E_mi"]
    return tuple(roots + ["N"])


def verify_result(row: dict, prefix: tuple[str, ...]) -> None:
    assert terse_cases(row) == prefix
    assert row["wrapper_returncode"] == 0
    assert row["child_returncode"] == 0
    assert not row["capped"]
    log = Path(row["log"])
    gb = Path(row["gb"])
    assert log.is_file() and gb.is_file()
    log_text = log.read_text(errors="replace")
    assert "UNRESOLVED cap=" not in log_text
    assert "EXIT code=0" in log_text
    if row["status"] == "UNIT":
        assert row["unit"] and basis_starts_unit(gb)
    elif row["status"] == "NONUNIT":
        assert not row["unit"] and not basis_starts_unit(gb)
    else:
        raise AssertionError(f"unexpected result status {row['status']}")


def verify_tree(state_path: Path) -> dict:
    state = json.loads(state_path.read_text())
    p = state["characteristic"]
    assert tuple(state["permutation_order"]) == ORDER
    assert state["start_depth"] == 6
    rows = {terse_cases(row): row for row in state["results"]}
    assert len(rows) == len(state["results"]), "duplicate tested prefix"
    visited: set[tuple[str, ...]] = set()
    counts: Counter[str] = Counter()
    candidate_leaves: list[tuple[str, ...]] = []

    def walk(depth: int, prefix: tuple[str, ...]) -> None:
        if depth >= state["start_depth"]:
            assert prefix in rows, f"missing tested prefix at depth {depth}: {prefix}"
            row = rows[prefix]
            verify_result(row, prefix)
            visited.add(prefix)
            counts[row["status"]] += 1
            if row["status"] == "UNIT":
                return
        if depth == len(ORDER):
            candidate_leaves.append(prefix)
            return
        permutation = ORDER[depth]
        for label in labels(p, permutation):
            walk(depth + 1, prefix + (f"{permutation}:{label}",))

    walk(0, ())
    assert visited == set(rows), "record contains results outside replayed tree"
    assert not state["pending"] and state["pending_nodes"] == 0
    assert state["open_due_to_load"] == 0 and state.get("blocked_reason") is None
    assert state["closed_subtrees"] == counts["UNIT"]
    assert state["complete_nonunit_leaves"] == len(candidate_leaves)
    recorded_candidates = [tuple(terse_text(text) for text in leaf)
                           for leaf in state["candidate_leaves"]]
    assert sorted(recorded_candidates) == sorted(candidate_leaves)
    assert state["exhaustive"] == (not candidate_leaves)
    return {
        "characteristic": p,
        "u_chart": state["u_chart"],
        "state_sha256": digest(state_path),
        "tested_nodes": len(rows),
        "status_counts": dict(counts),
        "candidate_leaves": len(candidate_leaves),
        "max_depth": max(map(len, rows), default=0),
        "verified": True,
    }


def symmetry_orbits() -> list[list[int]]:
    charts = list(itertools.combinations(range(4), 2))
    generators = ((1, 0, 2, 3), (0, 1, 3, 2))
    unseen = set(range(6))
    orbits = []
    while unseen:
        orbit = {min(unseen)}
        changed = True
        while changed:
            changed = False
            for chart in tuple(orbit):
                for permutation in generators:
                    image_rows = tuple(sorted(permutation[row] for row in charts[chart]))
                    image = charts.index(image_rows)
                    if image not in orbit:
                        orbit.add(image)
                        changed = True
        unseen -= orbit
        orbits.append(sorted(orbit))
    assert orbits == [[0], [1, 2, 3, 4], [5]]
    return orbits


def verify_controls(characteristic: int, chart: int) -> list[dict]:
    path = HERE / f"controls_p{characteristic}_uc{chart}.json"
    rows = json.loads(path.read_text())
    assert [row["control"] for row in rows] == ["all_trans_E1", "matrix_pattern"]
    answer = []
    for row in rows:
        prefix = terse_cases(row)
        verify_result(row, prefix)
        if row["control"] == "matrix_pattern":
            assert row["status"] == "NONUNIT" and row["passed"]
        else:
            assert row["passed"]
        answer.append({"control": row["control"], "status": row["status"], "verified": True})
    return answer


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--characteristic", "-p", type=int, choices=(3, 5, 7), action="append")
    parser.add_argument("--output", type=Path, default=HERE / "verification.json")
    args = parser.parse_args()
    characteristics = args.characteristic or [3, 5, 7]
    report = {"symmetry_orbits": symmetry_orbits(), "representatives": list(REPRESENTATIVES), "charts": []}
    for p in characteristics:
        for chart in REPRESENTATIVES:
            row = verify_tree(HERE / "certificates" / f"state_p{p}_uc{chart}.json")
            row["controls"] = verify_controls(p, chart)
            report["charts"].append(row)
    report["verified"] = True
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Exact integer control for the characteristic-zero rank-two search."""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

import sympy as sp

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE))

from r2split_encoder import PERMS, parse_case, perm_matrix  # noqa: E402
from r2split_search import run_branch  # noqa: E402

FIRST_NINE = (0, 1, 4, 5, 13, 20, 6, 15, 22)
A = sp.Matrix([[0, 0, 0, 1], [0, 0, 1, 0], [0, 1, 0, 0], [1, 0, 0, 0]])
U0 = sp.Matrix([[-1, 0], [0, -1], [0, 1], [1, 0]])
W0 = sp.Matrix([[1, 0], [0, 1], [0, -1], [-1, 0]])
CHART_ROWS = ((0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3))


def classify() -> tuple[list[str], list[dict]]:
    identity = sp.eye(4)
    cases = []
    audit = []
    for index in FIRST_NINE:
        b = A * perm_matrix(PERMS[index])
        power_vectors = [sp.Matrix(b**power).reshape(16, 1) for power in range(4)]
        cyclic_rank = sp.Matrix.hstack(*power_vectors).rank()
        rank_minus = (b - identity).rank()
        rank_plus = (b + identity).rank()
        if cyclic_rank == 4:
            label = "CYCLIC"
        elif rank_minus <= 2:
            label = "E_1"
        elif rank_plus <= 2:
            label = "E_m1"
        else:
            label = "N"
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


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--u-chart", type=int, choices=range(6), required=True)
    parser.add_argument("--output-dir", type=Path, default=HERE / "certificates/controls")
    args = parser.parse_args()
    assert A.det() != 0 and (A - sp.eye(4)).rank() == 2
    assert A == sp.eye(4) + U0 * W0.T
    rows = CHART_ROWS[args.u_chart]
    minor = U0.extract(rows, (0, 1)).det()
    if minor == 0:
        raise RuntimeError(f"control point does not lie in U chart {args.u_chart}")
    case_keys, audit = classify()
    cases = [parse_case(0, key) for key in case_keys]
    result = run_branch(0, cases, args.output_dir, args.u_chart)
    passed = result["status"] == "NONUNIT" and not result["capped"]
    report = {
        "control": "integer_reversal_matrix",
        "matrix": [list(map(int, A.row(i))) for i in range(4)],
        "rank_A_minus_I": 2,
        "det_A": int(A.det()),
        "U": [list(map(int, U0.row(i))) for i in range(4)],
        "W": [list(map(int, W0.row(i))) for i in range(4)],
        "u_chart": args.u_chart,
        "u_chart_minor": int(minor),
        "classification": audit,
        "case_keys": case_keys,
        "result": result,
        "passed": passed,
    }
    path = HERE / f"controls_p0_uc{args.u_chart}.json"
    path.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({
        "control": report["control"],
        "u_chart": args.u_chart,
        "case_keys": case_keys,
        "status": result["status"],
        "passed": passed,
        "seconds": result["seconds"],
        "swap_used_mib_at_start": result["swap_used_mib_at_start"],
    }), flush=True)
    if not passed:
        raise SystemExit(1)


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Concrete exact-rank-two controls for K6-R2SPLIT-1723."""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
ENCODER = ROOT / "encoders/independent"
sys.path.insert(0, str(ENCODER))

from r2split_encoder import PERMS, parse_case  # noqa: E402
from r2split_search import run_branch  # noqa: E402

U = [[-1, 0], [0, -1], [0, 1], [1, 0]]
W = [[1, 0], [0, 1], [0, -1], [-1, 0]]
A = [[0, 0, 0, 1], [0, 0, 1, 0], [0, 1, 0, 0], [1, 0, 0, 0]]
CHARTS = ((0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3))


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
    answer = [[int(i == j) for j in range(4)] for i in range(4)]
    for _ in range(exponent):
        answer = multiply(answer, matrix, p)
    return answer


def permutation_matrix(permutation: tuple[int, ...]) -> list[list[int]]:
    return [[int(permutation[j] == i) for j in range(4)] for i in range(4)]


def classify(p: int) -> tuple[list[str], list[dict]]:
    identity = [[int(i == j) for j in range(4)] for i in range(4)]
    cases: list[str] = []
    audit: list[dict] = []
    for index, permutation in enumerate(PERMS):
        b = multiply(A, permutation_matrix(permutation), p)
        vectors = [[entry for row in matrix_power(b, exponent, p) for entry in row]
                   for exponent in range(4)]
        cyclic_rank = rank_mod([[vectors[column][row] for column in range(4)]
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


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--characteristic", "-p", type=int, choices=(17, 19, 23), required=True)
    parser.add_argument("--u-chart", type=int, choices=range(6), required=True)
    parser.add_argument("--output-dir", type=Path, default=HERE / "certificates/controls")
    args = parser.parse_args()
    p, chart = args.characteristic, args.u_chart
    rows = CHARTS[chart]
    minor = (U[rows[0]][0] * U[rows[1]][1] - U[rows[0]][1] * U[rows[1]][0]) % p
    if minor == 0:
        raise SystemExit(f"control matrix is outside U chart {chart}")
    cases, audit = classify(p)
    result = run_branch(p, [parse_case(p, text) for text in cases], args.output_dir, chart)
    report = {
        "characteristic": p,
        "u_chart": chart,
        "matrix": A,
        "U": U,
        "W": W,
        "rank_U": rank_mod(U, p),
        "rank_W": rank_mod(W, p),
        "rank_A_minus_I": rank_mod([[
            (A[i][j] - int(i == j)) % p for j in range(4)] for i in range(4)], p),
        "u_chart_minor": minor,
        "case_keys": cases,
        "classification": audit,
        "result": result,
        "passed": result["status"] == "NONUNIT" and not result["capped"],
    }
    output = HERE / f"controls_p{p}_uc{chart}.json"
    output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({
        "characteristic": p,
        "u_chart": chart,
        "cases": len(cases),
        "status": result["status"],
        "seconds": result["seconds"],
        "passed": report["passed"],
        "swap_used_mib_at_start": result["swap_used_mib_at_start"],
    }), flush=True)
    if not report["passed"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()

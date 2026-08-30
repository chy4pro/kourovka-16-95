#!/usr/bin/env python3
"""Three required NONUNIT controls for the J5 encoder."""
from __future__ import annotations

import itertools
import json
from pathlib import Path

import sympy as sp

from n5j_runner import HERE, run_ideal

P = 3
N = 4


def existing_clean_nonunit(tag: str) -> dict | None:
    path = HERE / "controls" / f"{tag}.json"
    if not path.exists():
        return None
    result = json.loads(path.read_text())
    return result if (result.get("status") == "NONUNIT" and
                      result.get("child_returncode") == 0 and
                      not result.get("capped")) else None


def existing_result(tag: str) -> dict | None:
    path = HERE / "controls" / f"{tag}.json"
    return json.loads(path.read_text()) if path.exists() else None


def matvec(matrix: list[list[int]], vector: list[int], p: int = P) -> list[int]:
    return [sum(matrix[i][j] * vector[j] for j in range(N)) % p for i in range(N)]


def det_mod(matrix: list[list[int]], p: int = P) -> int:
    work = [[entry % p for entry in row] for row in matrix]
    determinant = 1
    for column in range(N):
        pivot = next((row for row in range(column, N) if work[row][column]), None)
        if pivot is None:
            return 0
        if pivot != column:
            work[column], work[pivot] = work[pivot], work[column]
            determinant = -determinant
        value = work[column][column]
        determinant = determinant * value % p
        inverse = pow(value, -1, p)
        for row in range(column + 1, N):
            factor = work[row][column] * inverse % p
            for j in range(column, N):
                work[row][j] = (work[row][j] - factor * work[column][j]) % p
    return determinant % p


def determinant_value(x: tuple[int, ...], y: tuple[int, ...], pivot: int,
                      ordering: tuple[int, ...]) -> int:
    columns = [list(x)]
    for index in range(N):
        columns.append([(int(row == index) + y[index] * x[row]) % P for row in range(N)])
    matrix = [[columns[ordering[column]][row] for column in range(N)] for row in range(N)]
    vectors = [columns[pivot]]
    for _ in range(3):
        vectors.append(matvec(matrix, vectors[-1]))
    krylov = [[vectors[column][row] for column in range(N)] for row in range(N)]
    return det_mod(krylov)


def find_realised_pattern(rows: list[dict], variables: list[str]) -> dict:
    symbols = sp.symbols(" ".join(variables))
    nonzero_rows = [row for row in rows if not row["zero"]]
    parsed = [sp.Poly(sp.sympify(row["polynomial"]), *symbols, modulus=P)
              for row in nonzero_rows]
    best: tuple[int, tuple[int, ...], tuple[int, ...], list[int]] | None = None
    for x in itertools.product(range(P), repeat=N):
        if not any(x):
            continue
        for y in itertools.product(range(P), repeat=N):
            direct = [determinant_value(x, y, row["pivot"], tuple(row["ordering"]))
                      for row in rows]
            nonzero_count = sum(value != 0 for value in direct)
            if 0 < nonzero_count < len(nonzero_rows) and (best is None or nonzero_count > best[0]):
                best = (nonzero_count, x, y, direct)
    if best is None:
        raise AssertionError("failed to find a mixed realised pattern")
    nonzero_count, x, y, direct = best
    substitutions = dict(zip(symbols, x + y))
    polynomial_values = [int(poly.eval(substitutions)) % P for poly in parsed]
    direct_nonzero_values = [direct[index] for index, row in enumerate(rows) if not row["zero"]]
    assert polynomial_values == direct_nonzero_values
    u0 = next(value for value in range(P)
              if (1 + value + sum(x[i] * y[i] for i in range(N))) % P)
    u = (u0,) + x
    v = (1,) + y
    matrix = [[(int(i == j) + u[i] * v[j]) % P for j in range(5)] for i in range(5)]
    return {
        "selection": "maximum number of nonzero D_j_tau over normalized GF(3) points",
        "x": list(x), "y": list(y), "u": list(u), "v": list(v),
        "matrix": matrix,
        "det_A": (1 + sum(u[i] * v[i] for i in range(5))) % P,
        "direct_values": direct,
        "nonzero_determinants": nonzero_count,
        "vanishing_determinants": len(rows) - nonzero_count,
    }


def main() -> None:
    bundle = json.loads((HERE / "j5_polynomials.json").read_text())
    variables = bundle["variables"]
    rows = bundle["determinants"]
    pivot_polynomials = [row["polynomial"] for row in rows
                         if row["pivot"] == 0 and not row["zero"]]
    pivot_result = existing_clean_nonunit("pivot_j_eq_i") or run_ideal(
        "pivot_j_eq_i", P, variables, pivot_polynomials, HERE / "controls",
        {"control": "only determinants whose pivot column is x", "pivot": 0})

    realised = find_realised_pattern(rows, variables)
    vanishing_polynomials = [row["polynomial"] for row, value in
                             zip(rows, realised["direct_values"])
                             if not row["zero"] and value == 0]
    realised_result = existing_result("realised_pattern") or run_ideal(
        "realised_pattern", P, variables, vanishing_polynomials,
        HERE / "controls",
        {"control": "nonzero determinant polynomials vanishing at concrete rank-one A"})
    point = realised["x"] + realised["y"]
    witness_polynomials = vanishing_polynomials + [
        f"{variable} - {value}" for variable, value in zip(variables, point)
    ]
    witness_result = existing_clean_nonunit("realised_pattern_with_witness") or run_ideal(
        "realised_pattern_with_witness", P, variables, witness_polynomials,
        HERE / "controls",
        {"control": "vanishing determinant ideal plus its concrete point maximal ideal",
         "logic": "a nonunit containing ideal certifies the determinant subideal nonunit"})

    toy_result = existing_clean_nonunit("toy_xy_1_minus_tx") or run_ideal(
        "toy_xy_1_minus_tx", P, ["toy_x", "toy_y", "toy_t"],
        ["toy_x*toy_y", "1 - toy_t*toy_x"], HERE / "controls",
        {"control": "<xy,1-tx>"})

    report = {
        "characteristic": P,
        "pivot_control": {
            "all_24_rows": sum(row["pivot"] == 0 for row in rows),
            "nonzero_generators": len(pivot_polynomials),
            "result": pivot_result,
        },
        "realised_pattern_control": {
            **realised,
            "nonzero_vanishing_generators": len(vanishing_polynomials),
            "raw_result": realised_result,
            "witness_linear_generators": 8,
            "witness_result": witness_result,
            "certification_logic": (
                "the witness ideal contains the raw vanishing ideal; since the larger ideal "
                "is nonunit, the raw ideal is nonunit"
            ),
        },
        "toy_control": {"result": toy_result},
    }
    clean = lambda result: (result["status"] == "NONUNIT" and
                            result["child_returncode"] == 0 and not result["capped"])
    report["passed"] = (clean(pivot_result) and clean(witness_result) and clean(toy_result)
                        and realised["det_A"] != 0)
    (HERE / "controls.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({
        "pivot": pivot_result["status"],
        "realised_raw": realised_result["status"],
        "realised_witness": witness_result["status"],
        "toy": toy_result["status"],
        "realised_nonzero_determinants": realised["nonzero_determinants"],
        "passed": report["passed"],
    }))
    if not report["passed"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Independent construction of the 120 Krylov determinants defining J5."""
from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path

import sympy as sp

HERE = Path(__file__).resolve().parent
X = sp.symbols("x1:5")
Y = sp.symbols("y1:5")
VARIABLES = X + Y


def columns() -> tuple[sp.Matrix, ...]:
    x = sp.Matrix(X)
    out = [x]
    for index, y in enumerate(Y):
        basis = sp.zeros(4, 1)
        basis[index, 0] = 1
        out.append(basis + y * x)
    return tuple(out)


def build_rows() -> list[dict]:
    cols = columns()
    rows: list[dict] = []
    for pivot in range(5):
        others = tuple(index for index in range(5) if index != pivot)
        for ordering in itertools.permutations(others):
            matrix = sp.Matrix.hstack(*(cols[index] for index in ordering))
            vector = cols[pivot]
            krylov = [vector]
            for _ in range(3):
                krylov.append(matrix * krylov[-1])
            determinant = sp.Poly(
                sp.expand(sp.Matrix.hstack(*krylov).det()), *VARIABLES, domain=sp.ZZ
            )
            expression = determinant.as_expr()
            rows.append({
                "pivot": pivot,
                "ordering": list(ordering),
                "polynomial": str(expression),
                "zero": determinant.is_zero,
                "total_degree": 0 if determinant.is_zero else determinant.total_degree(),
                "terms": len(determinant.terms()),
            })
    assert len(rows) == 120
    return rows


def build_bundle() -> dict:
    rows = build_rows()
    nonzero = [row for row in rows if not row["zero"]]
    return {
        "definition": "D_j_tau = det[c_j,M*c_j,M^2*c_j,M^3*c_j]",
        "deleted_row_and_normalized_coordinate": 0,
        "variables": [str(variable) for variable in VARIABLES],
        "determinants": rows,
        "total_determinants": len(rows),
        "identically_zero": sum(row["zero"] for row in rows),
        "nonzero": len(nonzero),
        "max_total_degree": max(row["total_degree"] for row in nonzero),
        "distinct_nonzero_polynomials": len({row["polynomial"] for row in nonzero}),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=HERE / "j5_polynomials.json")
    args = parser.parse_args()
    bundle = build_bundle()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(bundle, indent=2) + "\n")
    print(json.dumps({key: bundle[key] for key in (
        "total_determinants", "identically_zero", "nonzero",
        "max_total_degree", "distinct_nonzero_polynomials")}, indent=2))


if __name__ == "__main__":
    main()

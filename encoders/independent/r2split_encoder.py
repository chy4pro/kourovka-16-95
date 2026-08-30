#!/usr/bin/env python3
"""Polynomial encoder for the K6-R2SPLIT rank-two case decomposition.

The permutation convention is P_sigma e_j = e_{sigma(j)}.  A case is either
E:<root>, where the bad eigenvalue is a specified root of the permutation
polynomial, or N, where the bad parameter is forced away from that polynomial.

For an E case we use all 3 by 3 minors of AP_sigma-tI.  This is the direct,
basis-free polynomial form of the bordered-rank condition in R2HAND/R2CHAR2.
For N we use the four numerators of the Woodbury equation and invert chi(t).
"""
from __future__ import annotations

import argparse
import itertools
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence

import sympy as sp

N = 4
IDENTITY = tuple(range(N))
PERMS = [s for s in itertools.permutations(range(N)) if s != IDENTITY]

U_NAMES = tuple(f"u{i}{j}" for i in range(1, 5) for j in range(1, 3))
W_NAMES = ("w31", "w32", "w41", "w42")
BASE_NAMES = U_NAMES + W_NAMES + ("za",)
BASE_SYMBOLS = sp.symbols(" ".join(BASE_NAMES))
SYMBOL = {str(x): x for x in BASE_SYMBOLS}
OMEGA = sp.Symbol("omega")
II = sp.Symbol("ii")


def cycle_type(sigma: Sequence[int]) -> tuple[int, ...]:
    seen = [False] * N
    lengths: list[int] = []
    for start in range(N):
        if not seen[start]:
            j, length = start, 0
            while not seen[j]:
                seen[j] = True
                j = sigma[j]
                length += 1
            lengths.append(length)
    return tuple(sorted(lengths, reverse=True))


def perm_matrix(sigma: Sequence[int]) -> sp.Matrix:
    return sp.Matrix(N, N, lambda i, j: int(sigma[j] == i))


def permutation_name(index: int) -> str:
    return "s%02d_%s" % (index, "".join(str(x + 1) for x in PERMS[index]))


def matrices() -> tuple[sp.Matrix, sp.Matrix]:
    us = BASE_SYMBOLS[:8]
    ws = BASE_SYMBOLS[8:12]
    u = sp.Matrix(4, 2, us)
    w = sp.Matrix([[1, 0], [0, 1], [ws[0], ws[1]], [ws[2], ws[3]]])
    return u, w


U, W = matrices()
ZA = BASE_SYMBOLS[-1]
ZU = sp.Symbol("zu")
BASE_DET = sp.expand((sp.eye(2) + W.T * U).det())
BASE_GENERATOR = sp.expand(BASE_DET * ZA - 1)
U_CHART_ROWS = list(itertools.combinations(range(4), 2))


def u_chart_generator(u_chart: int) -> sp.Expr:
    if not 0 <= u_chart < len(U_CHART_ROWS):
        raise ValueError("U chart must be between 0 and 5")
    rows = U_CHART_ROWS[u_chart]
    return sp.expand(U.extract(rows, (0, 1)).det() * ZU - 1)


@dataclass(frozen=True)
class Case:
    perm_index: int
    kind: str
    root_name: str | None = None

    @property
    def key(self) -> str:
        return f"{permutation_name(self.perm_index)}:{self.label}"

    @property
    def label(self) -> str:
        return "N" if self.kind == "N" else f"E_{self.root_name}"


def eigen_roots(characteristic: int, ctype: tuple[int, ...]) -> list[tuple[str, sp.Expr]]:
    """Distinct algebraic eigenvalues for one cycle type in the requested p."""
    if characteristic == 0:
        roots = [("1", sp.Integer(1))]
        if any(k % 2 == 0 for k in ctype):
            roots.append(("m1", sp.Integer(-1)))
        if 3 in ctype:
            roots += [("omega", OMEGA), ("omega2", OMEGA**2)]
        if 4 in ctype:
            roots += [("i", II), ("mi", -II)]
        return roots
    if characteristic == 2:
        roots = [("1", sp.Integer(1))]
        if 3 in ctype:
            roots += [("omega", OMEGA), ("omega2", OMEGA**2)]
        return roots
    if characteristic == 3:
        roots = [("1", sp.Integer(1))]
        if any(k % 2 == 0 for k in ctype):
            roots.append(("m1", sp.Integer(-1)))
        if 4 in ctype:
            roots += [("i", II), ("mi", -II)]
        return roots
    if characteristic == 5:
        roots = [("1", sp.Integer(1))]
        if any(k % 2 == 0 for k in ctype):
            roots.append(("m1", sp.Integer(-1)))
        if 3 in ctype:
            roots += [("omega", OMEGA), ("omega2", OMEGA**2)]
        if 4 in ctype:
            roots += [("2", sp.Integer(2)), ("m2", sp.Integer(-2))]
        return roots
    if characteristic == 7:
        roots = [("1", sp.Integer(1))]
        if any(k % 2 == 0 for k in ctype):
            roots.append(("m1", sp.Integer(-1)))
        if 3 in ctype:
            roots += [("2", sp.Integer(2)), ("4", sp.Integer(4))]
        if 4 in ctype:
            roots += [("i", II), ("mi", -II)]
        return roots
    if characteristic == 11:
        roots = [("1", sp.Integer(1))]
        if any(k % 2 == 0 for k in ctype):
            roots.append(("m1", sp.Integer(-1)))
        if 3 in ctype:
            roots += [("omega", OMEGA), ("omega2", OMEGA**2)]
        if 4 in ctype:
            roots += [("i", II), ("mi", -II)]
        return roots
    if characteristic == 13:
        roots = [("1", sp.Integer(1))]
        if any(k % 2 == 0 for k in ctype):
            roots.append(("m1", sp.Integer(-1)))
        if 3 in ctype:
            roots += [("3", sp.Integer(3)), ("9", sp.Integer(9))]
        if 4 in ctype:
            roots += [("5", sp.Integer(5)), ("8", sp.Integer(8))]
        return roots
    raise ValueError("supported characteristics are 0, 2, 3, 5, 7, 11, and 13")


def case_list(characteristic: int, perm_index: int) -> list[Case]:
    roots = eigen_roots(characteristic, cycle_type(PERMS[perm_index]))
    return [Case(perm_index, "E", name) for name, _ in roots] + [Case(perm_index, "N")]


def all_case_lists(characteristic: int) -> list[list[Case]]:
    return [case_list(characteristic, i) for i in range(len(PERMS))]


def root_expression(characteristic: int, case: Case) -> sp.Expr:
    assert case.kind == "E" and case.root_name is not None
    return dict(eigen_roots(characteristic, cycle_type(PERMS[case.perm_index])))[case.root_name]


def extension_relations(characteristic: int, cases: Iterable[Case]) -> list[sp.Expr]:
    names = {c.root_name for c in cases if c.kind == "E"}
    out: list[sp.Expr] = []
    if names & {"omega", "omega2"}:
        out.append(OMEGA**2 + OMEGA + 1)
    if names & {"i", "mi"}:
        out.append(II**2 + 1)
    return out


def e_generators(characteristic: int, case: Case) -> list[sp.Expr]:
    sigma = PERMS[case.perm_index]
    pmat = perm_matrix(sigma)
    wsigma = sp.Matrix([list(W.row(sigma[j])) for j in range(N)])
    mat = pmat + U * wsigma.T - root_expression(characteristic, case) * sp.eye(N)
    gens: list[sp.Expr] = []
    for rows in itertools.combinations(range(N), 3):
        for cols in itertools.combinations(range(N), 3):
            value = sp.expand(mat.extract(rows, cols).det())
            if value != 0 and value not in gens:
                gens.append(value)
    return gens


def n_symbols(case: Case) -> tuple[sp.Symbol, sp.Symbol]:
    return sp.Symbol(f"t{case.perm_index:02d}"), sp.Symbol(f"zn{case.perm_index:02d}")


def n_generators(case: Case) -> list[sp.Expr]:
    sigma = PERMS[case.perm_index]
    pmat = perm_matrix(sigma)
    wsigma = sp.Matrix([list(W.row(sigma[j])) for j in range(N)])
    t, zn = n_symbols(case)
    base = pmat - t * sp.eye(N)
    chi = sp.expand(base.det())
    numerator = chi * sp.eye(2) + wsigma.T * base.adjugate() * U
    return [sp.expand(numerator[i, j]) for i in range(2) for j in range(2)] + [sp.expand(chi * zn - 1)]


def case_generators(characteristic: int, case: Case) -> list[sp.Expr]:
    return n_generators(case) if case.kind == "N" else e_generators(characteristic, case)


def variables_for(cases: Sequence[Case], u_chart: int | None = None) -> list[sp.Symbol]:
    variables = list(BASE_SYMBOLS)
    if u_chart is not None:
        variables.append(ZU)
    roots = {c.root_name for c in cases if c.kind == "E"}
    if roots & {"omega", "omega2"}:
        variables.append(OMEGA)
    if roots & {"i", "mi"}:
        variables.append(II)
    for case in cases:
        if case.kind == "N":
            variables.extend(n_symbols(case))
    return variables


def reduce_mod(expr: sp.Expr, variables: Sequence[sp.Symbol], characteristic: int) -> sp.Expr:
    poly = sp.Poly(sp.expand(expr), *variables)
    terms = {mon: int(coef) % characteristic for mon, coef in poly.terms() if int(coef) % characteristic}
    return sp.Poly.from_dict(terms, variables).as_expr() if terms else sp.Integer(0)


def ideal(characteristic: int, cases: Sequence[Case], u_chart: int | None = None) -> tuple[list[sp.Symbol], list[sp.Expr]]:
    variables = variables_for(cases, u_chart)
    raw = [BASE_GENERATOR] + extension_relations(characteristic, cases)
    if u_chart is not None:
        raw.append(u_chart_generator(u_chart))
    for case in cases:
        raw.extend(case_generators(characteristic, case))
    generators: list[sp.Expr] = []
    for generator in raw:
        value = sp.expand(generator) if characteristic == 0 else reduce_mod(generator, variables, characteristic)
        if value != 0 and value not in generators:
            generators.append(value)
    return variables, generators


def write_msolve(path: Path, characteristic: int, cases: Sequence[Case], u_chart: int | None = None) -> dict:
    variables, generators = ideal(characteristic, cases, u_chart)
    path.parent.mkdir(parents=True, exist_ok=True)
    body = ",\n".join(str(g).replace("**", "^") for g in generators)
    path.write_text(",".join(map(str, variables)) + f"\n{characteristic}\n" + body + "\n")
    return {
        "path": str(path),
        "characteristic": characteristic,
        "variables": len(variables),
        "generators": len(generators),
        "u_chart": u_chart,
        "u_chart_rows": None if u_chart is None else [r + 1 for r in U_CHART_ROWS[u_chart]],
        "cases": [c.key for c in cases],
    }


def parse_case(characteristic: int, text: str) -> Case:
    left, label = text.split(":", 1)
    if left.startswith("s"):
        index = int(left[1:3])
    else:
        index = int(left)
    choices = {case.label: case for case in case_list(characteristic, index)}
    if label not in choices:
        raise ValueError(f"unknown case {text}; choices are {sorted(choices)}")
    return choices[label]


def inventory(characteristic: int) -> dict:
    rows = []
    for index, cases in enumerate(all_case_lists(characteristic)):
        rows.append({
            "index": index,
            "name": permutation_name(index),
            "one_line": [x + 1 for x in PERMS[index]],
            "cycle_type": list(cycle_type(PERMS[index])),
            "cases": [case.label for case in cases],
        })
    return {"characteristic": characteristic, "permutations": rows}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--characteristic", "-p", type=int, required=True, choices=(0, 2, 3, 5, 7, 11, 13))
    parser.add_argument("--inventory", action="store_true")
    parser.add_argument("--case", action="append", default=[], help="INDEX:LABEL, e.g. 0:E_1 or 3:N")
    parser.add_argument("--u-chart", type=int, choices=range(6), help="saturate by this U 2x2 row minor")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.inventory:
        print(json.dumps(inventory(args.characteristic), indent=2))
        return
    cases = [parse_case(args.characteristic, value) for value in args.case]
    if not args.output:
        parser.error("--output is required unless --inventory is used")
    print(json.dumps(write_msolve(args.output, args.characteristic, cases, args.u_chart), indent=2))


if __name__ == "__main__":
    main()

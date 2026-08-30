#!/usr/bin/env python3
"""Independent exact encoder for the K6-N4x rank-one audit."""
from itertools import permutations
from pathlib import Path
import random
import sympy as sp

ROOT = Path(__file__).resolve().parent
IDEALS = ROOT / "ideals"
IDEALS.mkdir(parents=True, exist_ok=True)
DOMAINS = (0, 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47)

a, b, c, y1, y2, y3, r = sp.symbols("a b c y1 y2 y3 r")
NATURAL = (a, b, c, y1, y2, y3)
ORDER = (y3, y2, y1, c, b, a, r)
NATURAL_ORDER = (a, b, c, y1, y2, y3, r)


def determinant_family(wrong=False):
    x = sp.Matrix([a, b, c])
    columns = [x, sp.eye(3)[:, 0] + y1*x, sp.eye(3)[:, 1] + y2*x]
    columns.append(sp.eye(3)[:, 2] if wrong else sp.eye(3)[:, 2] + y3*x)
    indexed = []
    for j in range(4):
        for tau in permutations(k for k in range(4) if k != j):
            vector = columns[j]
            matrix = sp.Matrix.hstack(*(columns[k] for k in tau))
            value = sp.expand(sp.Matrix.hstack(vector, matrix*vector, matrix*matrix*vector).det())
            indexed.append((j, tau, value))
    assert len(indexed) == 24
    return indexed


def output_expr(expr):
    return str(sp.expand(expr)).replace("**", "^")


def write_msolve(name, generators, characteristic, variables=ORDER):
    if characteristic:
        generators = [sp.Poly(g, *variables, modulus=characteristic).as_expr() for g in generators]
    generators = [sp.expand(g) for g in generators if g != 0]
    path = IDEALS / f"{name}_p{characteristic}.ms"
    with path.open("w") as fp:
        fp.write(",".join(map(str, variables)) + "\n")
        fp.write(str(characteristic) + "\n")
        fp.write(",\n".join(output_expr(g) for g in generators) + "\n")
    return path


def main():
    exact = determinant_family(False)
    wrong = determinant_family(True)
    S = a+b+c
    Q = a*a+b*b+c*c-a*b-a*c-b*c
    j0 = [g for j, tau, g in exact if j == 0]
    assert sum(g == 0 for g in j0) == 4
    assert sorted([sp.cancel(g/(S*Q)) for g in j0 if g != 0], key=str) == [-1, 1]
    nonzero = [g for _, _, g in exact if g != 0]
    wrong_nonzero = [g for _, _, g in wrong if g != 0]

    manifest = ROOT / "determinants.txt"
    with manifest.open("w") as fp:
        for label, family in (("RIGHT", exact), ("WRONG", wrong)):
            for j, tau, g in family:
                degree = -1 if g == 0 else sp.Poly(g, *NATURAL).total_degree()
                fp.write(f"{label} j={j} tau={''.join(map(str,tau))} degree={degree} polynomial={output_expr(g)}\n")
        fp.write(f"RIGHT_COUNT indexed=24 nonzero={len(nonzero)} zero={24-len(nonzero)}\n")
        fp.write(f"WRONG_COUNT indexed=24 nonzero={len(wrong_nonzero)} zero={24-len(wrong_nonzero)}\n")
        fp.write("J0_CHECK four_zero=PASS two_nonzero=+-(a+b+c)*(a^2+b^2+c^2-ab-ac-bc)=PASS\n")

    charts = {"a": [1-r*a], "b": [a, 1-r*b], "c": [a, b, 1-r*c]}
    for chart, chart_gens in charts.items():
        for p in DOMAINS:
            write_msolve(f"full_{chart}", nonzero + chart_gens, p)
        for p in (0, 2):
            write_msolve(f"alt_full_{chart}", nonzero + chart_gens, p, NATURAL_ORDER)

    # Control (i): x=0 remains allowed.  Generate it over Q and GF(7).
    for p in (0, 7):
        write_msolve("control_nochart", nonzero, p)

    # Control (ii): find a point with a != 0 at which a proper, nonempty
    # subset vanishes, then include the a-chart equation.  The listed point
    # with r=a^-1 is an exact witness that this ideal is nonunit over GF(7).
    rng = random.Random(41695)
    while True:
        point = [rng.randrange(7) for _ in NATURAL]
        if point[0] == 0:
            continue
        subs = dict(zip(NATURAL, point))
        vanished = [g for g in nonzero if int(g.subs(subs)) % 7 == 0]
        if len(vanished) == 1:
            break
    rinv = pow(point[0], -1, 7)
    write_msolve("control_subset", vanished + [1-r*a], 7)
    (ROOT / "control_subset_point.txt").write_text(
        f"GF(7) point a,b,c,y1,y2,y3,r={point+[rinv]}\n"
        f"vanishing_nonzero_determinants={len(vanished)} of {len(nonzero)}\n"
        "All retained determinant generators and 1-r*a evaluate to zero.\n")

    # Control (iii): wrong fourth column, on every x-chart, over Q and GF(2).
    for chart, chart_gens in charts.items():
        for p in (0, 2):
            write_msolve(f"wrong_{chart}", wrong_nonzero + chart_gens, p)

    print(f"ENCODER right_nonzero={len(nonzero)} right_zero={24-len(nonzero)} "
          f"wrong_nonzero={len(wrong_nonzero)} wrong_zero={24-len(wrong_nonzero)}")
    print(f"SUBSET_CONTROL point={point+[rinv]} vanished={len(vanished)}/{len(nonzero)}")
    print("ENCODER_COMPLETE PASS")


if __name__ == "__main__":
    main()

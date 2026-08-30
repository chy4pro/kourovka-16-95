#!/usr/bin/env python3
"""Exact SymPy checker for the algebraic identities used in K6-R1ALLN.

This is not a search heuristic: every assertion is a polynomial identity over Z.
"""
from __future__ import annotations

import sympy as sp


def krylov_det(M: sp.Matrix, b: sp.Matrix) -> sp.Expr:
    m = M.rows
    cols = []
    v = b
    for _ in range(m):
        cols.append(v)
        v = M * v
    return sp.expand(sp.Matrix.hstack(*cols).det())


def check_path(m: int) -> None:
    t = sp.symbols("t")
    xs = sp.symbols(f"x0:{m}")
    ys = sp.symbols(f"y0:{m}")
    x = sp.Matrix(xs)

    # N e_s=e_{s+1}, N e_{m-1}=0; z=(y1,...,y_{m-1},1).
    N = sp.zeros(m)
    for s in range(m - 1):
        N[s + 1, s] = 1
    z = sp.Matrix(list(ys[1:]) + [1])
    M = N + x * z.T
    b = sp.eye(m)[:, 0] + ys[0] * x

    chi = sp.expand((t * sp.eye(m) - M).det())
    G = sp.expand(1 + sum(ys[s] * t ** (m - s) for s in range(m)))
    X = sp.expand(sum(xs[r] * t**r for r in range(m)))
    Q = sp.expand(
        1
        + sum(
            ys[s] * xs[r] * t ** (r - s)
            for s in range(m)
            for r in range(s, m)
        )
    )
    assert sp.expand(chi + G * X - t**m * Q) == 0

    h = sp.expand((z.T * (t * sp.eye(m) - M).adjugate() * b)[0])
    assert sp.expand(h + ys[0] * chi - G) == 0

    # In this path basis the observability determinant is a unit (sign),
    # and with these conventions the signs cancel: D=Res_t(chi,G).
    D = krylov_det(M, b)
    R = sp.resultant(chi, G, t)
    assert sp.expand(D - R) == 0
    print(f"PASS path identities/resultant m={m}")


def check_path_plus_fixed(ell: int) -> None:
    t = sp.symbols("t")
    xp = sp.symbols(f"xp0:{ell}")
    yp = sp.symbols(f"yp0:{ell}")
    xf, yf = sp.symbols("xf yf")

    Np = sp.zeros(ell)
    for s in range(ell - 1):
        Np[s + 1, s] = 1
    zp = sp.Matrix(list(yp[1:]) + [1])
    Mp = Np + sp.Matrix(xp) * zp.T
    chip = sp.expand((t * sp.eye(ell) - Mp).det())
    Gp = sp.expand(1 + sum(yp[s] * t ** (ell - s) for s in range(ell)))

    N = sp.diag(Np, sp.Matrix([[1]]))
    x = sp.Matrix(list(xp) + [xf])
    z = sp.Matrix(list(zp) + [yf])
    M = N + x * z.T
    b = sp.eye(ell + 1)[:, 0] + yp[0] * x
    Phi = sp.expand((t * sp.eye(ell + 1) - M).det())
    assert sp.expand(Phi - ((t - 1) * chip - xf * yf * t**ell)) == 0

    h = sp.expand((z.T * (t * sp.eye(ell + 1) - M).adjugate() * b)[0])
    assert sp.expand(h + yp[0] * Phi - (t - 1) * Gp) == 0
    print(f"PASS path+fixed identities ell={ell}")


def check_m2_closed_forms() -> None:
    a, b, p, q = sp.symbols("a b p q")
    x = sp.Matrix([a, b])
    c0 = x
    c1 = sp.Matrix([1, 0]) + p * x
    c2 = sp.Matrix([0, 1]) + q * x
    U, V, W = 1 + a * p, 1 + b * q, 1 + a * p + b * q

    P1 = krylov_det(sp.Matrix.hstack(c2, c0), c1)
    F1 = krylov_det(sp.Matrix.hstack(c0, c2), c1)
    P2 = krylov_det(sp.Matrix.hstack(c0, c1), c2)
    F2 = krylov_det(sp.Matrix.hstack(c1, c0), c2)

    assert sp.expand(P1 - (U * W + b**2 * p)) == 0
    assert sp.expand(F1 - b * (U + p * W)) == 0
    assert sp.expand(P2 + (V * W + a**2 * q)) == 0
    assert sp.expand(F2 + a * (V + q * W)) == 0
    print("PASS m=2 four closed forms")


def check_constant_x(m: int) -> None:
    t, c = sp.symbols("t c")
    ys = sp.symbols(f"y0:{m}")
    S = sum(ys)
    G = sp.expand(1 + sum(ys[s] * t ** (m - s) for s in range(m)))
    Q = sp.expand(
        1
        + c
        * sum(
            ys[s] * t ** (r - s)
            for s in range(m)
            for r in range(s, m)
        )
    )
    lam = 1 + c * (1 + S)
    assert sp.expand((t - 1) * Q - (c * G + t - lam)) == 0
    print(f"PASS constant-x telescoping identity m={m}")


def main() -> None:
    for m in (1, 2, 3):
        check_path(m)
    for ell in (1, 2, 3):
        check_path_plus_fixed(ell)
    check_m2_closed_forms()
    for m in range(1, 7):
        check_constant_x(m)
    print("ALL SYMBOLIC CHECKS PASSED")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""ROUND 6-AV (registry R6.123): independent verification of the load-bearing K6-R1ALLN identities
at dimensions beyond the accompanying symbolic checker (its m <= 3 resultant,
m <= 6 constant-x):
  (3.1)  chi_v(t) + g_v(t) X_v(t) = t^m q_v(t)                        [Hamilton path, random samples, m = 4..7]
  (3.2)  D_v != 0  <=>  gcd(chi_v, g_v) = 1                            [random samples over GF(p)]
  (3.3)  D_v = 0   <=>  g_v, q_v share a root in the closure          [via gcd(g_v, q_v) over GF(p), deg check]
  (4.1)  Phi(t) = (t-1) chi_v(t) - x_f y_f t^ell                       [path + fixed point, m = 5, 6]
  (4.2)  bad  <=>  exists alpha: g_v(alpha) = 0 and (alpha-1)q_v(alpha) = x_f y_f   [random samples]
  (8.1)  (t-1) q_v(t) = c g_v(t) + t - lambda   for constant x = c     [m = 7, 8, random y]
Conventions exactly as the harvest: path coordinates v = (v_0..v_{m-1}), N e_r = e_{r+1} (r < m-1), N e_{m-1} = 0,
M = N + x z^T with z = (y_1,...,y_{m-1}, 1)^T, b = e_0 + y_0 x  (indices AFTER renaming so that x_r = x_{v_r});
g_v(t) = 1 + sum_s y_s t^{m-s}, X_v(t) = sum_r x_r t^r, q_v(t) = 1 + sum_{0<=s<=r<m} y_s x_r t^{r-s};
D_v = det[b, Mb, ..., M^{m-1}b].  Fixed point (4.x): one extra index f with M e_f = e_f + x_f * z-part? NO —
the fixed-point config: the full matrix on indices {path(ell)} u {f}: column f is c_f placed at position f
(fixed point), i.e. M = N' + x z'^T where N' has the path shift plus e_f at position f, z' has y-entries on the
path slots and y_f at f... Here we take the harvest's (4.1) as the claim to TEST: build the explicit
(ell+1)-dim matrix with a length-ell path and one fixed point and compare char poly with (t-1)chi_v - x_f y_f t^ell.
All checks over GF(p) for p in {101, 2}, many random samples; exact sympy over QQ for (3.1)/(8.1) at one random
integer point per m.  PASS/FAIL per item."""
import random, sys
sys.stdout.reconfigure(line_buffering=True)
import sympy as sp

random.seed(20260830)
t = sp.symbols('t')

def path_config(m, xs, ys):
    # matrix M (m x m) over the ring of xs entries: N shift + x z^T ; b
    N = sp.zeros(m, m)
    for r in range(m - 1): N[r + 1, r] = 1
    x = sp.Matrix(xs); z = sp.Matrix(ys[1:] + [1])
    M = N + x * z.T
    b = sp.Matrix([1 if i == 0 else 0 for i in range(m)]) + ys[0] * x
    return M, b, x

def polys(m, xs, ys):
    g = 1 + sum(ys[s] * t**(m - s) for s in range(m))
    X = sum(xs[r] * t**r for r in range(m))
    q = 1 + sum(ys[s] * xs[r] * t**(r - s) for s in range(m) for r in range(s, m))
    return sp.expand(g), sp.expand(X), sp.expand(q)

def krylov_det(M, b, m):
    K = sp.Matrix.hstack(*[(M**k) * b for k in range(m)])
    return K.det()

def check31_81(m, p=None):
    xs = [random.randint(0, 96) for _ in range(m)]; ys = [random.randint(0, 96) for _ in range(m)]
    M, b, x = path_config(m, xs, ys)
    g, X, q = polys(m, xs, ys)
    chi = sp.expand((t * sp.eye(m) - M).det())
    lhs = sp.expand(chi + g * X - t**m * q)
    ok31 = lhs == 0
    # (8.1) with constant x
    c = random.randint(1, 50); xs2 = [c] * m
    g2, _, q2 = polys(m, xs2, ys)
    S = sum(ys); lam = 1 + c * (1 + S)
    ok81 = sp.expand((t - 1) * q2 - (c * g2 + t - lam)) == 0
    return ok31, ok81

def check32_33(m, p, trials):
    ok = True
    for _ in range(trials):
        xs = [random.randrange(p) for _ in range(m)]; ys = [random.randrange(p) for _ in range(m)]
        M, b, x = path_config(m, xs, ys)
        g, X, q = polys(m, xs, ys)
        chi = sp.expand((t * sp.eye(m) - M).det())
        D = krylov_det(M, b, m) % p
        gp = sp.Poly(g, t, modulus=p); chip = sp.Poly(chi, t, modulus=p); qp = sp.Poly(q, t, modulus=p)
        gcd_cg = sp.gcd(chip, gp)
        pred32 = (gcd_cg.degree() == 0)
        if (D != 0) != pred32: ok = False; print("  (3.2) FAIL m=%d p=%d xs=%s ys=%s D=%s gcd=%s" % (m, p, xs, ys, D, gcd_cg)); break
        gcd_gq = sp.gcd(gp, qp)
        pred33_bad = (gcd_gq.degree() > 0)   # over GF(p) a common factor means a common root in the closure
        if (D == 0) != pred33_bad:
            # gcd over GF(p) with no root in GF(p) still means common root in closure — (3.3) compares closure roots; degree>0 suffices
            ok = False; print("  (3.3) FAIL m=%d p=%d xs=%s ys=%s D=%s gcd_gq=%s" % (m, p, xs, ys, D, gcd_gq)); break
    return ok

def fixed_point_config(ell, xs, ys, xf, yf):
    # indices 0..ell-1 = path (renamed), index ell = fixed point f
    m = ell + 1
    N = sp.zeros(m, m)
    for r in range(ell - 1): N[r + 1, r] = 1
    N[ell, ell] = 1                       # fixed point column: e_f at position f
    x = sp.Matrix(xs + [xf]); z = sp.Matrix(ys[1:] + [1] + [yf])
    # careful: z entries: path columns 0..ell-1 use y_1..y_{ell-1} then weight 1 on the LAST path column (position ell-1);
    # the fixed-point column (position ell) carries y_f.
    M = N + x * z.T
    b = sp.Matrix([1 if i == 0 else 0 for i in range(m)]) + ys[0] * x
    return M, b

def check41_42(ell, p, trials):
    ok41 = True; ok42 = True
    for _ in range(trials):
        xs = [random.randrange(p) for _ in range(ell)]; ys = [random.randrange(p) for _ in range(ell)]
        xf = random.randrange(1, p); yf = random.randrange(1, p)
        M, b = fixed_point_config(ell, xs, ys, xf, yf)
        m = ell + 1
        g, X, q = polys(ell, xs, ys)
        chi_path = sp.expand((t * sp.eye(ell) - path_config(ell, xs, ys)[0]).det())
        Phi = sp.expand((t * sp.eye(m) - M).det())
        if sp.Poly(sp.expand(Phi - ((t - 1) * chi_path - xf * yf * t**ell)), t, modulus=p).is_zero is False:
            ok41 = False; print("  (4.1) FAIL ell=%d p=%d xs=%s ys=%s xf=%d yf=%d" % (ell, p, xs, ys, xf, yf)); break
        D = krylov_det(M, b, m) % p
        gp = sp.Poly(g, t, modulus=p); qp = sp.Poly(q, t, modulus=p)
        h = sp.Poly(sp.expand((t - 1) * q - xf * yf), t, modulus=p)
        bad_pred = sp.gcd(gp, h).degree() > 0
        if (D == 0) != bad_pred:
            ok42 = False; print("  (4.2) FAIL ell=%d p=%d xs=%s ys=%s xf=%d yf=%d D=%s" % (ell, p, xs, ys, xf, yf, D)); break
    return ok41, ok42

print("== (3.1) and (8.1), exact over ZZ ==")
for m in (4, 5, 6, 7, 8):
    a, b8 = check31_81(m)
    print("m=%d: (3.1) %s   (8.1) %s" % (m, "PASS" if a else "FAIL", "PASS" if b8 else "FAIL"))
print("== (3.2)/(3.3) over GF(101) and GF(2) ==")
for m in (4, 5, 6):
    for p in (101, 2):
        r = check32_33(m, p, 60)
        print("m=%d p=%d: (3.2)+(3.3) %s" % (m, p, "PASS" if r else "FAIL"))
print("== (4.1)/(4.2) over GF(101) and GF(2), path length ell ==")
for ell in (4, 5):
    for p in (101, 2):
        a, b4 = check41_42(ell, p, 40)
        print("ell=%d p=%d: (4.1) %s   (4.2) %s" % (ell, p, "PASS" if a else "FAIL", "PASS" if b4 else "FAIL"))
print("done")

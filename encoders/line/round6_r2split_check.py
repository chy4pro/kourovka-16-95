#!/usr/bin/env python3
"""ROUND 6-AF: independent re-check of the K6-R2SPLIT characteristic-2 theorem (registry R6.93), own encoder.
Claim: over every field of characteristic 2, for every A = I + U W^T with rank(U W^T) = 2, at least one of
the seven permutations {six transpositions, (12)(34)} makes A P_sigma cyclic.
Normalisation: W = [[1,0],[0,1],[w31,w32],[w41,w42]] (rank W = 2, conjugation + GL_2 gauge); rank U = 2 is
covered by the six U-charts "det U[{i,j},:] != 0".  For each of the 7 permutations sigma, in
characteristic 2 the only eigenvalue of P_sigma is 1, so
   sigma bad  <=>  (E1) all 3x3 minors of (P_sigma + U W_sigma^T + I) vanish    [rank(AP_sigma - I) <= 2]
              or   (N)  exists t with chi(t) != 0 and chi(t) I_2 + W_sigma^T adj(P_sigma - tI) U = 0
                        [Woodbury: rank(P_sigma - tI + U W_sigma^T) <= 2 iff I_2 + W_sigma^T (P_sigma-tI)^{-1} U = 0].
For every U-chart and every one of the 2^7 case assignments we build the ideal (plus c*za - 1 and
det(U[rows]) zu - 1) over GF(2) and ask msolve for a Groebner basis: ALL must be the unit ideal.
Controls: (i) a realised partial pattern (the bad cases of a concrete GF(2) rank-two matrix restricted
to the seven permutations) must be NON-unit; (ii) the all-E1 conjunction of the six transpositions
must be unit (K6-R2SPLIT's core).  Usage: round6_r2split_check.py [--controls-only] [--charts 0,1,...]"""
import sys, os, itertools, time, subprocess, json
from pathlib import Path
sys.stdout.reconfigure(line_buffering=True)
import sympy as sp
T0 = time.time()
controls_only = "--controls-only" in sys.argv
charts_arg = None
if "--charts" in sys.argv: charts_arg = [int(x) for x in sys.argv[sys.argv.index("--charts") + 1].split(",")]
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
out_arg = sys.argv[sys.argv.index("--out") + 1] if "--out" in sys.argv else None
OUT = Path(out_arg) if out_arg else REPO / "certificates/generated/line/rank2/p2"
OUT.mkdir(parents=True, exist_ok=True)
MS = os.environ.get("MSOLVE", "msolve"); ENV = dict(os.environ)
p = 2; n = 4
U = sp.Matrix(n, 2, sp.symbols("u11 u12 u21 u22 u31 u32 u41 u42"))
w31, w32, w41, w42 = sp.symbols("w31 w32 w41 w42")
W = sp.Matrix([[1, 0], [0, 1], [w31, w32], [w41, w42]])
za, zu = sp.symbols("za zu")
A = sp.eye(n) + U * W.T
c = sp.expand((sp.eye(2) + W.T * U).det())
def perm_matrix(s): return sp.Matrix(n, n, lambda i, j: 1 if s[j] == i else 0)
def wsig(s): return sp.Matrix([[W[s[j], 0], W[s[j], 1]] for j in range(n)])
SEVEN = [(1, 0, 2, 3), (2, 1, 0, 3), (3, 1, 2, 0), (0, 2, 1, 3), (0, 3, 2, 1), (0, 1, 3, 2), (1, 0, 3, 2)]  # six transpositions + (12)(34)
NAMES = ["(12)", "(13)", "(14)", "(23)", "(24)", "(34)", "(12)(34)"]
tt = {s: sp.Symbol("t%d" % k) for k, s in enumerate(SEVEN)}
zn = {s: sp.Symbol("zn%d" % k) for k, s in enumerate(SEVEN)}
def gens_E1(s):
    M = perm_matrix(s) + U * wsig(s).T + sp.eye(n)   # char 2: -I = +I
    out = []
    for rows in itertools.combinations(range(n), 3):
        for cols in itertools.combinations(range(n), 3):
            m = sp.expand(M.extract(list(rows), list(cols)).det())
            if m != 0: out.append(m)
    return out
def gens_N(s):
    t = tt[s]; P = perm_matrix(s); M = P - t * sp.eye(n)
    chi = sp.expand(M.det()); adj = M.adjugate()
    E = chi * sp.eye(2) + wsig(s).T * adj * U
    out = [sp.expand(E[i, j]) for i in range(2) for j in range(2)]
    out.append(sp.expand(chi * zn[s] - 1))
    return [g for g in out if g != 0]
GE1 = {s: gens_E1(s) for s in SEVEN}; GN = {s: gens_N(s) for s in SEVEN}
print("generators ready: E1 sizes %s, N sizes %s  [%.0fs]" % ([len(GE1[s]) for s in SEVEN], [len(GN[s]) for s in SEVEN], time.time()-T0))
UCHARTS = list(itertools.combinations(range(n), 2))
def reduce_mod(expr, VARS):
    P = sp.Poly(expr, *VARS)
    terms = {m: (int(cf) % p) for m, cf in P.terms() if int(cf) % p}
    return sp.Poly(terms, *VARS).as_expr() if terms else sp.Integer(0)
def run_ideal(tag, chart, assignment):
    """assignment: dict sigma -> 'E1' | 'N' (subset of SEVEN allowed)."""
    VARS = [v for v in U] + [w31, w32, w41, w42, za, zu]
    body = [sp.expand(c * za - 1), sp.expand(U.extract(list(chart), [0, 1]).det() * zu - 1)]
    for s, case in assignment.items():
        if case == "E1": body += GE1[s]
        else:
            body += GN[s]; VARS += [tt[s], zn[s]]
    lines = []
    for g in body:
        r = reduce_mod(g, VARS)
        if r != 0: lines.append(str(r).replace("**", "^"))
    path = OUT / (tag + ".ms")
    path.write_text(",".join(str(v) for v in VARS) + "\n" + str(p) + "\n" + ",\n".join(lines) + "\n")
    out = Path(str(path) + ".gb")
    try:
        subprocess.run([MS, "-g", "2", "-t", "1", "-f", str(path), "-o", str(out)], env=ENV, capture_output=True, text=True, timeout=600)
    except subprocess.TimeoutExpired:
        return None
    basis = "".join(l for l in out.read_text().splitlines() if not l.startswith("#")).replace(" ", "")
    return basis.startswith("[1]")
# ---- controls ----
# (ii) all-E1 conjunction of the six transpositions, chart {0,1}: expected UNIT (their core)
r = run_ideal("ctrl_allE1_chart01", (0, 1), {s: "E1" for s in SEVEN[:6]})
print("control all-transpositions-E1 on chart {1,2}: unit=%s (expected True)" % r)
# (i) realised pattern: take the GF(2) matrix A0 = I + U0 W0^T with U0 rows (1,1),(0,1),(1,1),(0,1), W0 = chart with w rows (1,0),(0,1)
U0 = sp.Matrix([[1, 1], [0, 1], [1, 1], [0, 1]]); W0 = sp.Matrix([[1, 0], [0, 1], [1, 0], [0, 1]])
A0 = (sp.eye(n) + U0 * W0.T).applyfunc(lambda x: x % 2)
src = (HERE / "round6_controllable.py").read_text()
G = {}
exec(compile(src[:src.index('print("ROUND 6-B')], "r6b", "exec"), G)
GF, rank_rows, cyclic = G['GF'], G['rank_rows'], G['cyclic']
F2 = GF(2)
A0l = [[int(A0[i, j]) for j in range(n)] for i in range(n)]
print("control matrix A0 =", A0l, "rank", rank_rows([r[:] for r in A0l], n, F2), "rank(U0)=", U0.rank())
pattern = {}
for s in SEVEN:
    B = [[A0l[i][s[j]] for j in range(n)] for i in range(n)]
    bad = not cyclic(tuple(B[i][j] for i in range(n) for j in range(n)), n, F2)
    if bad:
        BI = [[(B[i][j] + (1 if i == j else 0)) % 2 for j in range(n)] for i in range(n)]
        pattern[s] = "E1" if rank_rows([r[:] for r in BI], n, F2) <= 2 else "N"
print("A0 bad among the seven:", {NAMES[SEVEN.index(s)]: v for s, v in pattern.items()})
chart0 = next(ch for ch in UCHARTS if U0.extract(list(ch), [0, 1]).det() % 2 != 0)
r = run_ideal("ctrl_realised_A0", chart0, pattern)
print("control realised pattern of A0 on chart %s: unit=%s (expected False)  [%.0fs]" % (chart0, r, time.time()-T0))
if controls_only: sys.exit(0)
# ---- full enumeration ----
charts = UCHARTS if charts_arg is None else [UCHARTS[k] for k in charts_arg]
results = {}
nonunit = []
for ci, ch in enumerate(charts):
    cnt = 0
    for bits in itertools.product(("E1", "N"), repeat=7):
        assignment = dict(zip(SEVEN, bits))
        tag = "chart%d%d_%s" % (ch[0], ch[1], "".join("E" if b == "E1" else "N" for b in bits))
        r = run_ideal(tag, ch, assignment)
        results[tag] = r; cnt += 1
        if r is not True: nonunit.append((tag, r)); print("  NOT-UNIT/capped:", tag, r)
    print("chart %s: %d assignments done, non-unit/capped so far %d  [%.0fs]" % (ch, cnt, len(nonunit), time.time()-T0))
(OUT / "summary.json").write_text(json.dumps({"results": results, "nonunit": nonunit}, indent=1) + "\n")
print("RESULT char 2: charts %d x 128 assignments = %d ideals; NOT unit or capped: %d" % (len(charts), len(results), len(nonunit)))
print("done %.0fs" % (time.time()-T0))

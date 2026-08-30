#!/usr/bin/env python3
"""ROUND 6-AG: independent DPLL re-check of the rank-two case decomposition in ODD characteristic p
(registry R6.96), own encoder.  Theorem target: over every field of characteristic p, every
A = I + U W^T with rank(U W^T) = 2 has a cyclic A P_sigma.
Normalisation as in round6_r2split_check.py: W = [[1,0],[0,1],[w31,w32],[w41,w42]], U-chart (i,j) with
det U[{i,j},:] != 0 (variable zu), det(I2 + W^T U) != 0 (variable za).
Cases for sigma: E_r for each eigenvalue r of P_sigma over the algebraic closure (2-cycles and double
transpositions: r in {1,-1}; 3-cycles: {1, w, w^2} with w^2+w+1=0 (w = 1 if p = 3; w in GF(p) if p = 1 mod 3,
else adjoined as a variable 'om' with om^2+om+1 = 0); 4-cycles: {1,-1, i,-i} with i^2 = -1 (i in GF(p) if
p = 1 mod 4, else adjoined as 'ii' with ii^2+1 = 0)): all 3x3 minors of P_sigma + U W_sigma^T - r I;
and N: chi_sigma(t) I2 + W_sigma^T adj(P_sigma - tI) U = 0 with chi_sigma(t) zn - 1 = 0 (t a free variable).
"sigma bad" <=> OR of its cases (exhaustive: t is an eigenvalue or not).
DPLL: branch over permutations in the given order; at each node the ideal of the chosen cases (+ za, zu,
adjoined relations) is sent to msolve; unit => branch closed; else branch on the next permutation's
cases; a node with ALL permutations of the order assigned and still non-unit is reported as OPEN (a
candidate all-bad configuration among that permutation set).
Usage: round6_r2split_odd.py <p> <chart_index 0..5> [--order transp,double,three,four] [--max-runs N] [--controls-only]"""
import sys, os, itertools, time, subprocess, json
from pathlib import Path
sys.stdout.reconfigure(line_buffering=True)
import sympy as sp
T0 = time.time()
p = int(sys.argv[1]); chart_idx = int(sys.argv[2]) if len(sys.argv) > 2 and sys.argv[2].isdigit() else 0
controls_only = "--controls-only" in sys.argv
max_runs = int(sys.argv[sys.argv.index("--max-runs") + 1]) if "--max-runs" in sys.argv else 4000
order_arg = sys.argv[sys.argv.index("--order") + 1] if "--order" in sys.argv else "transp,double,three,four"
# --start-depth D: assign the first D permutations of the order completely (all case combinations) before the
# first msolve call, so that no shallow positive-dimensional ideal is ever sent to the solver (§R6.95 lesson).
start_depth = int(sys.argv[sys.argv.index("--start-depth") + 1]) if "--start-depth" in sys.argv else 0
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
out_arg = sys.argv[sys.argv.index("--out") + 1] if "--out" in sys.argv else None
OUT = Path(out_arg) if out_arg else REPO / f"certificates/generated/line/rank2/p{p}_chart{chart_idx}"
OUT.mkdir(parents=True, exist_ok=True)
MS = os.environ.get("MSOLVE", "msolve"); ENV = dict(os.environ)
n = 4
U = sp.Matrix(n, 2, sp.symbols("u11 u12 u21 u22 u31 u32 u41 u42"))
w31, w32, w41, w42 = sp.symbols("w31 w32 w41 w42")
W = sp.Matrix([[1, 0], [0, 1], [w31, w32], [w41, w42]])
za, zu, om, ii = sp.symbols("za zu om ii")
c = sp.expand((sp.eye(2) + W.T * U).det())
def perm_matrix(s): return sp.Matrix(n, n, lambda i, j: 1 if s[j] == i else 0)
def wsig(s): return sp.Matrix([[W[s[j], 0], W[s[j], 1]] for j in range(n)])
def ctype(s):
    seen = [False]*n; t = []
    for i in range(n):
        if not seen[i]:
            j = i; L = 0
            while not seen[j]: seen[j] = True; j = s[j]; L += 1
            t.append(L)
    return tuple(sorted(t, reverse=True))
perms = [s for s in itertools.permutations(range(n)) if s != tuple(range(n))]
by_type = {"transp": [s for s in perms if ctype(s) == (2, 1, 1)], "double": [s for s in perms if ctype(s) == (2, 2)],
           "three": [s for s in perms if ctype(s) == (3, 1)], "four": [s for s in perms if ctype(s) == (4,)]}
ORDER = [s for key in order_arg.split(",") for s in by_type[key]]
# field constants
minus1 = (p - 1) if p else -1
have_omega = (p % 3 == 1); have_i = (p % 4 == 1)
omega_vals = [1] if p == 3 else ([x for x in range(p) if (x*x + x + 1) % p == 0] if have_omega else None)
i_vals = [x for x in range(p) if (x*x + 1) % p == 0] if have_i else None
def eig_cases(s):
    t = ctype(s)
    if t in ((2, 1, 1), (2, 2)): return [("E1", 1), ("Em1", minus1)]
    if t == (3, 1):
        if p == 3: return [("E1", 1)]
        if have_omega: return [("E1", 1), ("Ew", omega_vals[0]), ("Ew2", omega_vals[1])]
        return [("E1", 1), ("Ew", om), ("Ew2", sp.expand(om * om))]
    if t == (4,):
        base = [("E1", 1), ("Em1", minus1)]
        if have_i: return base + [("Ei", i_vals[0]), ("Emi", i_vals[1])]
        return base + [("Ei", ii), ("Emi", -ii)]
tt = {s: sp.Symbol("t%d" % k) for k, s in enumerate(perms)}
zn = {s: sp.Symbol("zn%d" % k) for k, s in enumerate(perms)}
CACHE = {}
def gens_E(s, r):
    key = (s, str(r))
    if key in CACHE: return CACHE[key]
    M = perm_matrix(s) + U * wsig(s).T - r * sp.eye(n)
    out = []
    for rows in itertools.combinations(range(n), 3):
        for cols in itertools.combinations(range(n), 3):
            m = sp.expand(M.extract(list(rows), list(cols)).det())
            if m != 0: out.append(m)
    CACHE[key] = out; return out
def gens_N(s):
    key = (s, "N")
    if key in CACHE: return CACHE[key]
    t = tt[s]; M = perm_matrix(s) - t * sp.eye(n)
    chi = sp.expand(M.det()); adj = M.adjugate()
    E = chi * sp.eye(2) + wsig(s).T * adj * U
    out = [sp.expand(E[i, j]) for i in range(2) for j in range(2)] + [sp.expand(chi * zn[s] - 1)]
    CACHE[key] = [g for g in out if g != 0]; return CACHE[key]
UCHARTS = list(itertools.combinations(range(n), 2)); chart = UCHARTS[chart_idx]
def reduce_mod(expr, VARS):
    if p == 0: return sp.expand(expr)
    P = sp.Poly(expr, *VARS)
    terms = {m: (int(cf) % p) for m, cf in P.terms() if int(cf) % p}
    return sp.Poly(terms, *VARS).as_expr() if terms else sp.Integer(0)
RUNS = 0
def run_ideal(tag, assignment):
    """assignment: list of (sigma, case_name, r_or_None)."""
    global RUNS
    VARS = [v for v in U] + [w31, w32, w41, w42, za, zu]
    body = [sp.expand(c * za - 1), sp.expand(U.extract(list(chart), [0, 1]).det() * zu - 1)]
    need_om = need_i = False
    for s, name, r in assignment:
        if name == "N":
            body += gens_N(s); VARS += [tt[s], zn[s]]
        else:
            g = gens_E(s, r); body += g
            if any(e.has(om) for e in g): need_om = True
            if any(e.has(ii) for e in g): need_i = True
    if need_om: body.append(sp.expand(om*om + om + 1)); VARS.append(om)
    if need_i: body.append(sp.expand(ii*ii + 1)); VARS.append(ii)
    lines = []
    for g in body:
        rr = reduce_mod(g, VARS)
        if rr != 0: lines.append(str(rr).replace("**", "^"))
    path = OUT / (tag + ".ms")
    path.write_text(",".join(str(v) for v in VARS) + "\n" + str(p) + "\n" + ",\n".join(lines) + "\n")
    out = Path(str(path) + ".gb"); RUNS += 1
    try:
        subprocess.run([MS, "-g", "2", "-t", "1", "-f", str(path), "-o", str(out)], env=ENV, capture_output=True, text=True, timeout=600)
    except subprocess.TimeoutExpired:
        return None
    basis = "".join(l for l in out.read_text().splitlines() if not l.startswith("#")).replace(" ", "")
    return basis.startswith("[1]")
# ---- controls over GF(p): realised pattern of a concrete exact-rank-two matrix, restricted to 2-cycles/double transpositions/3-cycles ----
src = (HERE / "round6_controllable.py").read_text()
G = {}
exec(compile(src[:src.index('print("ROUND 6-B')], "r6b", "exec"), G)
GF, rank_rows, cyclic = G['GF'], G['rank_rows'], G['cyclic']
Fp = GF(p) if p else None
def is_cyclic_Q(B):
    # over Q: cyclic <=> I, B, B^2, B^3 linearly independent
    cols = [sp.eye(n).reshape(16, 1), B.reshape(16, 1), (B*B).reshape(16, 1), (B*B*B).reshape(16, 1)]
    return sp.Matrix.hstack(*cols).rank() == 4
def realised_pattern_Q(U0, W0):
    A0 = sp.eye(n) + U0 * W0.T
    A0l = [[int(A0[i, j]) for j in range(n)] for i in range(n)]
    pat = []
    for s in ORDER:
        if ctype(s) not in ((2, 1, 1), (2, 2)): continue
        B = sp.Matrix(n, n, lambda i, j: A0[i, s[j]])
        if is_cyclic_Q(B): continue
        found = None
        for name, r in eig_cases(s):
            if (B - r * sp.eye(n)).rank() <= 2: found = (s, name, r); break
        pat.append(found if found else (s, "N", None))
    return A0l, pat
def realised_pattern(U0, W0):
    A0 = (sp.eye(n) + U0 * W0.T).applyfunc(lambda x: x % p)
    A0l = [[int(A0[i, j]) for j in range(n)] for i in range(n)]
    pat = []
    for s in ORDER:
        if ctype(s) == (4,): continue
        B = [[A0l[i][s[j]] for j in range(n)] for i in range(n)]
        if cyclic(tuple(B[i][j] for i in range(n) for j in range(n)), n, Fp): continue
        found = None
        for name, r in eig_cases(s):
            if isinstance(r, sp.Basic): continue
            Br = [[(B[i][j] - (int(r) if i == j else 0)) % p for j in range(n)] for i in range(n)]
            if rank_rows([row[:] for row in Br], n, Fp) <= 2: found = (s, name, r); break
        pat.append(found if found else (s, "N", None))
    return A0l, pat
rng_seed = 1695 + p
import random
rng = random.Random(rng_seed)
found_ctrl = None
for _ in range(20000):
    rv = (lambda: rng.randrange(-2, 3)) if p == 0 else (lambda: rng.randrange(p))
    U0 = sp.Matrix(n, 2, [rv() for _ in range(8)]); W0 = sp.Matrix([[1, 0], [0, 1], [rv(), rv()], [rv(), rv()]])
    dU = U0.extract(list(chart), [0, 1]).det(); dA = sp.expand((sp.eye(2) + W0.T * U0).det())
    if (dU == 0 if p == 0 else dU % p == 0): continue
    if (dA == 0 if p == 0 else dA % p == 0): continue
    A0l, pat = realised_pattern_Q(U0, W0) if p == 0 else realised_pattern(U0, W0)
    if len(pat) >= (2 if p == 0 else 6): found_ctrl = (U0, W0, A0l, pat); break
if found_ctrl:
    U0, W0, A0l, pat = found_ctrl
    print("control: A0 =", A0l, "bad (non-4-cycle) cases:", [(ctype(s), name) for s, name, r in pat])
    r = run_ideal("ctrl_realised", pat)
    print("control realised pattern (%d cases) unit=%s (expected False)  [%.0fs]" % (len(pat), r, time.time()-T0))
else:
    print("control: no matrix with >= 6 bad non-4-cycles found in 20000 samples on chart", chart)
r = run_ideal("ctrl_alltransp_E1", [(s, "E1", 1) for s in by_type["transp"]])
print("all-transposition E1 conjunction: unit=%s (odd characteristic: expected False per N4n)  [%.0fs]" % (r, time.time()-T0))
if controls_only: sys.exit(0)
# ---- DPLL ----
closed = 0; open_nodes = []; capped = 0
def dpll(depth, assignment, tag):
    global closed, capped
    if RUNS >= max_runs: open_nodes.append(("MAXRUNS", tag)); return
    if depth == len(ORDER):
        open_nodes.append(("OPEN", tag, [(ctype(s), nm) for s, nm, _ in assignment])); print("  OPEN leaf:", tag); return
    s = ORDER[depth]
    for name, rr in eig_cases(s) + [("N", None)]:
        node = assignment + [(s, name, rr)]; t2 = tag + "_" + name
        res = run_ideal(t2, node)
        if res is True: closed += 1
        elif res is None: capped += 1; open_nodes.append(("CAPPED", t2)); print("  capped:", t2)
        else: dpll(depth + 1, node, t2)
    if depth <= 1: print("  depth %d done: runs %d closed %d open %d capped %d  [%.0fs]" % (depth, RUNS, closed, len(open_nodes), capped, time.time()-T0))
if start_depth > 0:
    roots = list(itertools.product(*[eig_cases(s) + [("N", None)] for s in ORDER[:start_depth]]))
    print("start-depth %d: %d root assignments" % (start_depth, len(roots)))
    for k, combo in enumerate(roots):
        node = [(s, name, rr) for s, (name, rr) in zip(ORDER[:start_depth], combo)]
        tag = "r%04d" % k
        res = run_ideal(tag, node)
        if res is True: closed += 1
        elif res is None: capped += 1; open_nodes.append(("CAPPED", tag)); print("  capped:", tag)
        else: dpll(start_depth, node, tag)
        if k % 100 == 99: print("  roots %d/%d: runs %d closed %d open %d capped %d  [%.0fs]" % (k+1, len(roots), RUNS, closed, len(open_nodes), capped, time.time()-T0))
else:
    dpll(0, [], "d")
(OUT / "summary.json").write_text(json.dumps({"p": p, "chart": chart, "order": [ctype(s) for s in ORDER], "runs": RUNS, "closed": closed, "open": open_nodes, "capped": capped}, indent=1) + "\n")
print("RESULT p=%d chart %s: msolve runs %d, closed branches %d, OPEN leaves %d, capped %d  [%.0fs]" % (p, chart, RUNS, closed, len([o for o in open_nodes if o[0] == "OPEN"]), capped, time.time()-T0))
print("done")

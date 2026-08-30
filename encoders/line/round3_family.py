#!/usr/bin/env python3
"""ROUND 3-B (line k1695, 2026-08-24): the RANK-ONE-OVER-MONOMIAL family.

WHY THIS FAMILY.  For n = 3, EVERY counterexample to Kourovka 16.95 must lie in it:
if A in GL(3,F) is not cyclic then P=I already fails, so A is derogatory, so some
eigenvalue has geometric multiplicity >= 2, so rank(A - lambda I) <= 1; and lambda must
lie in F (a lambda outside F would carry >= 2 conjugates of algebraic multiplicity >= 2,
i.e. degree >= 4 > 3).  So A = lambda I + u v^T.  More generally this is the
"maximally derogatory" stratum -- the natural place for a counterexample to hide, and
the natural generalisation of round 2's aI+bJ theorem (u = b*1, v = 1).

FAMILY.   A = N + u v^T with N = D P_tau monomial (D invertible diagonal), u,v in F^n.
          A P_sigma = D P_pi + u w^T   with pi = tau*sigma  and  w_i = vt_{pi(i)},
          vt_j := v_{tau^{-1}(j)}.  As sigma runs over S_n so does pi, so the whole
          question is: is there a permutation pi with D P_pi + u w^T cyclic?
          Conjugating by P_rho permutes the TRIPLES (d_j, u_j, vt_j) simultaneously and
          conjugates pi, so the answer depends only on the MULTISET of triples.  That is
          the reduction that lets this scan reach n = 12 where the GL(n,q) scan dies at 4.

CRITERION C1 (derived this round, for pi an n-cycle; validated below against brute force).
  Order the tokens cyclically as (d_i,u_i,vt_i), i=0..n-1; Dp_j = d_0...d_j; delta = Dp_{n-1};
  w_i = vt_{i+1 mod n}.  M = D P_c + u w^T has ker(M - lambda) of dim >= 2 for some lambda
  iff chi(x)=x^n-delta, Pu, Pw and Palpha-delta have a common root, where
      Pu(x)     = sum_j (u_j/Dp_j) x^{j+1}                       [left eigenvector vs u]
      Pw(x)     = sum_j w_j Dp_j x^{n-1-j}                       [right eigenvector vs w]
      Palpha(x) = sum_{t<=j} w_j u_t (Dp_j/Dp_t) x^{n-1+t-j}     [the third clause]
  so  M is CYCLIC  <=>  gcd(chi, Pu, Pw, Palpha - delta) = 1  in F[x].
  Hand-checked before coding on two independent prior results (R8 of k1695_state.md):
  n=6,char 2,A=J-I gives gcd = x+1 (NOT cyclic, correct) and n=4 gives 1 (cyclic, correct).

DISCIPLINE.  Every "this permutation works" the criterion reports is re-verified by an
independent brute-force minimal-polynomial computation before it is counted; any
disagreement aborts the run.  A "no permutation works" is only reported after an
EXHAUSTIVE search over all n! permutations (small n) or is labelled CAPPED (large n) --
never silently.
"""
import sys, time, itertools
sys.stdout.reconfigure(line_buffering=True)
T0 = time.time()
HARD_LIMIT = 2400.0

def check_time(tag=""):
    if time.time() - T0 > HARD_LIMIT:
        print("HARD TIMEOUT at %.1fs (%s) -- everything printed above stands as stated" % (time.time()-T0, tag))
        sys.exit(2)

IRRED = {(2,2):[1,1,1], (2,3):[1,1,0,1], (3,2):[1,0,1], (5,2):[2,0,1]}

def prime_power(q):
    p = 2
    while p*p <= q and q % p:
        p += 1
    if q % p:
        p = q
    k, t = 0, q
    while t % p == 0:
        t //= p; k += 1
    assert t == 1
    return p, k

class GF(object):
    def __init__(self, q):
        p, k = prime_power(q)
        self.q, self.p, self.k = q, p, k
        if k == 1:
            self.ADD = [[(a+b) % p for b in range(q)] for a in range(q)]
            self.MUL = [[(a*b) % p for b in range(q)] for a in range(q)]
        else:
            f = IRRED[(p,k)]
            def dg(a):
                d = []
                for _ in range(k):
                    d.append(a % p); a //= p
                return d
            def ud(d):
                v = 0
                for i in reversed(range(k)):
                    v = v*p + d[i]
                return v
            def pm(a, b):
                da, db = dg(a), dg(b); c = [0]*(2*k-1)
                for i in range(k):
                    if da[i]:
                        for j in range(k):
                            c[i+j] = (c[i+j] + da[i]*db[j]) % p
                for i in reversed(range(k, 2*k-1)):
                    if c[i]:
                        co = c[i]; c[i] = 0
                        for j in range(k):
                            c[i-k+j] = (c[i-k+j] - co*f[j]) % p
                return ud(c[:k])
            self.ADD = [[ud([(x+y) % p for x, y in zip(dg(a), dg(b))]) for b in range(q)] for a in range(q)]
            self.MUL = [[pm(a, b) for b in range(q)] for a in range(q)]
        self.NEG = [next(b for b in range(q) if self.ADD[a][b] == 0) for a in range(q)]
        self.INV = [0]*q
        for a in range(1, q):
            self.INV[a] = next(b for b in range(1, q) if self.MUL[a][b] == 1)
        assert all(self.MUL[a][self.INV[a]] == 1 for a in range(1, q))

# ------------------------------------------------------------------ polynomials
def ptrim(a):
    while a and a[-1] == 0:
        a.pop()
    return a

def pmod(a, b, F):
    """a mod b, both low->high coefficient lists, b nonzero."""
    a = list(a); b = list(b)
    ADD, MUL, NEG, INV = F.ADD, F.MUL, F.NEG, F.INV
    ib = INV[b[-1]]
    while len(a) >= len(b) and a:
        if a[-1] == 0:
            a.pop(); continue
        f = MUL[a[-1]][ib]; nf = NEG[f]; sh = len(a) - len(b)
        Mnf = MUL[nf]
        for i in range(len(b)):
            a[sh+i] = ADD[a[sh+i]][Mnf[b[i]]]
        ptrim(a)
    return a

def pgcd(a, b, F):
    a = ptrim(list(a)); b = ptrim(list(b))
    while b:
        a, b = b, pmod(a, b, F)
    if a:
        iv = F.INV[a[-1]]
        a = [F.MUL[c][iv] for c in a]
    return a

# --------------------------------------------------------------- brute oracles
def cyclic(M, n, F):
    """O1: minpoly degree == n (I,M,...,M^{n-1} linearly independent). M flat tuple."""
    MUL, ADD, NEG, INV = F.MUL, F.ADD, F.NEG, F.INV
    rows = []
    cur = tuple(1 if i == j else 0 for i in range(n) for j in range(n))
    for _ in range(n):
        v = list(cur)
        for (piv, rw) in rows:
            f = v[piv]
            if f:
                Mnf = MUL[NEG[f]]
                for t in range(piv, n*n):
                    if rw[t]:
                        v[t] = ADD[v[t]][Mnf[rw[t]]]
        piv = next((i for i, x in enumerate(v) if x), None)
        if piv is None:
            return False
        Miv = MUL[INV[v[piv]]]
        rows.append((piv, [Miv[x] for x in v]))
        C = [0]*(n*n)
        for i in range(n):
            ri = i*n
            for k2 in range(n):
                a = cur[ri+k2]
                if a:
                    rk = k2*n; Ma = MUL[a]
                    for j in range(n):
                        b = M[rk+j]
                        if b:
                            C[ri+j] = ADD[C[ri+j]][Ma[b]]
        cur = tuple(C)
    return True

def build_M(order, tokens, pi, n, F):
    """M = D P_pi + u w^T, w_i = vt_{pi(i)}; token j sits at position order[j]... here
    `order` IS the position->token map: pos i holds tokens[order[i]]."""
    MUL, ADD = F.MUL, F.ADD
    d = [tokens[order[i]][0] for i in range(n)]
    u = [tokens[order[i]][1] for i in range(n)]
    vt = [tokens[order[i]][2] for i in range(n)]
    w = [vt[pi[i]] for i in range(n)]
    M = [0]*(n*n)
    for i in range(n):
        M[pi[i]*n + i] = d[pi[i]]          # (D P_pi)[pi(i)][i] = d_{pi(i)}
    for j in range(n):
        for i in range(n):
            if u[j] and w[i]:
                M[j*n+i] = ADD[M[j*n+i]][MUL[u[j]][w[i]]]
    return tuple(M)

# ------------------------------------------------------------------ criterion
def criterion_ncycle(seq, n, F):
    """seq = list of tokens (d,u,vt) in cyclic order.  Returns (is_cyclic, gcd_poly)."""
    MUL, ADD, NEG, INV = F.MUL, F.ADD, F.NEG, F.INV
    d = [t[0] for t in seq]; u = [t[1] for t in seq]; vt = [t[2] for t in seq]
    w = [vt[(i+1) % n] for i in range(n)]
    Dp = [0]*n
    acc = 1
    for j in range(n):
        acc = MUL[acc][d[j]]; Dp[j] = acc
    delta = Dp[n-1]
    chi = [0]*(n+1); chi[n] = 1; chi[0] = NEG[delta]
    Pu = [0]*(n+1)
    for j in range(n):
        Pu[j+1] = MUL[u[j]][INV[Dp[j]]]
    Pw = [0]*n
    for j in range(n):
        Pw[n-1-j] = MUL[w[j]][Dp[j]]
    Pa = [0]*n
    for j in range(n):
        if w[j] == 0:
            continue
        for t in range(j+1):
            if u[t] == 0:
                continue
            c = MUL[MUL[w[j]][u[t]]][MUL[Dp[j]][INV[Dp[t]]]]
            e = n-1+t-j
            Pa[e] = ADD[Pa[e]][c]
    Pa[0] = ADD[Pa[0]][NEG[delta]]
    g = pgcd(chi, Pu, F)
    if len(g) > 1:
        g = pgcd(g, Pw, F)
    if len(g) > 1:
        g = pgcd(g, Pa, F)
    return (len(g) <= 1), g

# ---------------------------------------------------------- permutation helpers
def cycle_type(s):
    n = len(s); seen = [False]*n; t = []
    for i in range(n):
        if not seen[i]:
            L = 0; j = i
            while not seen[j]:
                seen[j] = True; j = s[j]; L += 1
            t.append(L)
    return tuple(sorted(t, reverse=True))

def perms_by_tier(n):
    out = [[], [], [], []]
    for s in itertools.permutations(range(n)):
        ct = cycle_type(s)
        if len(ct) == 1:
            out[0].append((ct, s))
        elif ct == (n-1, 1):
            out[1].append((ct, s))
        elif len(ct) == 2:
            out[2].append((ct, s))
        else:
            out[3].append((ct, s))
    return out

def multiset_perms(seq):
    """Each DISTINCT permutation of the multiset exactly once (next-permutation order)."""
    a = sorted(seq)
    while True:
        yield tuple(a)
        i = len(a) - 2
        while i >= 0 and a[i] >= a[i+1]:
            i -= 1
        if i < 0:
            return
        j = len(a) - 1
        while a[j] <= a[i]:
            j -= 1
        a[i], a[j] = a[j], a[i]
        a[i+1:] = list(reversed(a[i+1:]))

def distinct_cyclic_orders(tokens, n, cap):
    """Distinct cyclic arrangements: pin slot 0 to an occurrence of the smallest token
    (every cyclic class has such a rotation), permute the rest without repetition."""
    toks = sorted(tokens)
    first, rest = toks[0], toks[1:]
    out = []
    for perm in multiset_perms(rest):
        out.append((first,) + perm)
        if len(out) >= cap:
            return out, True
    return out, False

def fallback_perms(n):
    """Permutations with >= 2 cycles, type (n-1,1) FIRST (that is round 2's proved
    fallback), then -- only when they can be enumerated -- every remaining type."""
    for f in range(n):
        rest = [i for i in range(n) if i != f]
        head, tail = rest[0], rest[1:]
        for pr in itertools.permutations(tail):
            cyc = (head,) + pr
            s = [0]*n
            s[f] = f
            L = len(cyc)
            for t in range(L):
                s[cyc[t]] = cyc[(t+1) % L]
            yield ((n-1, 1), tuple(s))
    if n <= 8:
        for s in itertools.permutations(range(n)):
            ct = cycle_type(s)
            if len(ct) >= 2 and ct != (n-1, 1):
                yield (ct, s)

# ---------------------------------------------------------------- validation
def validate(F, n, rows, tag):
    """Cross-validate criterion C1 against brute force O1 on explicit (token-order) rows."""
    bad = 0; ncyc = 0
    ident = tuple(range(n))
    pi_c = tuple((i+1) % n for i in range(n))
    for seq in rows:
        pred, g = criterion_ncycle(list(seq), n, F)
        M = build_M(ident, list(seq), pi_c, n, F)
        truth = cyclic(M, n, F)
        if pred != truth:
            bad += 1
            if bad <= 3:
                print("   DISAGREEMENT q=%d n=%d seq=%s pred=%s truth=%s gcd=%s" % (F.q, n, seq, pred, truth, g))
        if truth:
            ncyc += 1
    print("  validate %s q=%d n=%d rows=%d disagreements=%d (criterion said cyclic on %d, i.e. not a constant answer)"
          % (tag, F.q, n, len(rows), bad, ncyc))
    assert bad == 0, "CRITERION C1 DISAGREES WITH BRUTE FORCE -- everything downstream is void"
    assert 0 < ncyc < len(rows), "VACUITY: criterion returned a constant answer on this grid"
    return bad

# --------------------------------------------------------------- family census
def family_scan(F, n, with_D, cap_orders, label):
    """All multisets of tokens; for each, find a permutation pi making D P_pi + u w^T
    cyclic.  n-cycles go through criterion C1 (every success re-verified by brute force);
    then >=2 cycles by brute force, type (n-1,1) first.  Exhaustive over all types for
    n <= 8; for n >= 9 the residual types are not enumerated and any case reaching that
    point is reported as UNRESOLVED, never as a success."""
    check_time(label)
    q = F.q
    dvals = list(range(1, q)) if with_D else [1]
    symbols = [(d, a, b) for d in dvals for a in range(q) for b in range(q)]
    tot = 0; need_fb = 0; capped = 0; cex = []; unresolved = []
    hard = []
    ident = tuple(range(n))
    pi_c = tuple((i+1) % n for i in range(n))
    t0 = time.time()
    for tokens in itertools.combinations_with_replacement(symbols, n):
        tot += 1
        check_time("%s at %d" % (label, tot))   # EVERY item: a coarse check lets one slow
        # cell (n=12) run past the cap unnoticed -- that happened on 2026-08-24 and is why
        # this is per-item now, not per-2000.
        orders, was_capped = distinct_cyclic_orders(list(tokens), n, cap_orders)
        hit = None; lastg = None
        for seq in orders:
            ok, g = criterion_ncycle(list(seq), n, F)
            lastg = g
            if ok:
                M = build_M(ident, list(seq), pi_c, n, F)
                assert cyclic(M, n, F), "WITNESS REJECTED BY BRUTE FORCE: %s" % (seq,)
                hit = (n,)
                break
        if hit is not None:
            continue
        need_fb += 1
        if was_capped:
            capped += 1
        found = None
        for (ct, s) in fallback_perms(n):
            M = build_M(ident, list(tokens), s, n, F)
            if cyclic(M, n, F):
                found = ct; break
        if found is None:
            if n <= 8 and not was_capped:
                cex.append(tokens)
                print("  *** FAMILY COUNTEREXAMPLE q=%d n=%d tokens=%s (ALL %d! permutations fail) ***"
                      % (q, n, tokens, n))
            else:
                unresolved.append(tokens)
                print("  ??? UNRESOLVED q=%d n=%d tokens=%s (search was capped -- NOT a counterexample claim)"
                      % (q, n, tokens))
        else:
            hard.append((tokens, found, lastg))
    types = sorted(set(h[1] for h in hard), key=str)
    print("%s q=%d n=%d D=%s multisets=%d | no-n-cycle=%d (capped %d) | fallback: %s | CEX=%d | UNRESOLVED=%d | %.1fs"
          % (label, q, n, "var" if with_D else "I", tot, need_fb, capped,
             ";".join("%s:%d" % (t, sum(1 for h in hard if h[1] == t)) for t in types) or "none",
             len(cex), len(unresolved), time.time()-t0))
    for h in hard[:5]:
        print("     hard multiset (d,u,vt)=%s -> no n-cycle (last obstruction gcd %s), first working type %s"
              % (h[0], h[2], h[1]))
    return cex, hard

print("ROUND 3-B family attack start; hard limit %ds" % HARD_LIMIT)
print("--- STEP 1: criterion C1 vs brute force O1 (must agree everywhere) ---")
# controls first: the two hand-computed known answers from R8
F2 = GF(2)
seq6 = [(1,1,1)]*6
pred6, g6 = criterion_ncycle(seq6, 6, F2)
print("  KAT q=2 n=6 A=J-I (u=v=1): criterion says cyclic=%s gcd=%s  [R8: n-cycle FAILS -> expect False]" % (pred6, g6))
assert pred6 is False
seq4 = [(1,1,1)]*4
pred4, g4 = criterion_ncycle(seq4, 4, F2)
print("  KAT q=2 n=4 A=J-I (u=v=1): criterion says cyclic=%s gcd=%s  [R8 control: n-cycle WORKS -> expect True]" % (pred4, g4))
assert pred4 is True
for q in [2, 3, 4, 5]:
    F = GF(q)
    for n in [2, 3, 4, 5]:
        if q**(3*n) > 4*10**6 or (q >= 4 and n >= 5):
            # exhaustive over tokens too big: use a deterministic spread instead
            rows = []
            syms = [(d, a, b) for d in range(1, q) for a in range(q) for b in range(q)]
            for k in range(3000):
                rows.append(tuple(syms[(k*7 + 3*i*i + i) % len(syms)] for i in range(n)))
            validate(F, n, rows, "spread")
        else:
            syms = [(d, a, b) for d in range(1, q) for a in range(q) for b in range(q)]
            rows = list(itertools.product(syms, repeat=n))
            if len(rows) > 60000:
                rows = rows[::max(1, len(rows)//60000)]
            validate(F, n, rows, "exhaustive-tokens")
print("--- STEP 1 PASS: criterion C1 == brute force on every row tested ---")

print("--- STEP 2: family census (does SOME permutation always work?) ---")
CEXS = []
JOBS = [(2, 3, True), (2, 4, True), (2, 5, True), (2, 6, True), (2, 7, True), (2, 8, True),
        (3, 3, True), (3, 4, True), (3, 5, True), (3, 6, False), (3, 7, False), (3, 8, False),
        (4, 3, True), (4, 4, True), (4, 5, False), (5, 3, True), (5, 4, False), (7, 3, False),
        (8, 3, False), (9, 3, False), (5, 5, False),
        (2, 9, False), (2, 10, False), (2, 11, False), (2, 12, False)]
for (q, n, wD) in JOBS:
    F = GF(q)
    cap = 5000 if n <= 8 else 2000
    cex, hard = family_scan(F, n, wD, cap, "family")
    CEXS.extend(cex)
print("VERDICT: %s | elapsed %.1fs" % ("FAMILY COUNTEREXAMPLE FOUND" if CEXS else "no family counterexample anywhere", time.time()-T0))

#!/usr/bin/env python3
"""ROUND 6-B (line k1695): does the CONTROLLABLE-ROW-BLOCK certificate always exist?

Facts. rank(A P_sigma - mu I) >= n-1 for all mu  <==  some (n-1)-row submatrix of
(A P_sigma - mu I) has full row rank n-1 for all mu.  Deleting row i, that submatrix is
   [ C P_tau - mu I_{n-1} | b ]   (after reordering columns),
with C = A[!=i, !=j], b = A[!=i, j], j = sigma(i), tau = sigma restricted -- i.e. the pair
(C P_tau, b) is CONTROLLABLE (PBH), i.e. b is a cyclic vector of C P_tau.
So define
  (S)   for A in GL(n,F): exist i, j, tau in S_{n-1} with A[!=i,j] a cyclic vector of A[!=i,!=j] P_tau
  (T_m) for EVERY m x (m+1) matrix R of rank m: exist column j and tau in S_m with
        R[:,j] a cyclic vector of R[:,!=j] P_tau.
(T_{n-1}) ==> (S) ==> 16.95(n).  Neither is implied by 16.95.  This script measures them.
Exact table arithmetic (GF tables from round3_family.py); no floating point.  Light compute only.
"""
import sys, time, itertools
sys.stdout.reconfigure(line_buffering=True)
T0 = time.time()
HARD_LIMIT = 1200.0
src = open("problems/k1695/round3_family.py").read()
G = {}
exec(compile(src[:src.index('print("ROUND 3-B family attack start')], "rf", "exec"), G)
GF, cyclic = G['GF'], G['cyclic']

def check_time(tag=""):
    if time.time() - T0 > HARD_LIMIT:
        print("HARD TIMEOUT at %.1fs (%s) -- everything printed above stands as stated" % (time.time()-T0, tag))
        sys.exit(2)

def rank_rows(rows, ncols, F):
    ADD, MUL, NEG, INV = F.ADD, F.MUL, F.NEG, F.INV
    R = [list(r) for r in rows]; r = 0
    for c in range(ncols):
        p = next((i for i in range(r, len(R)) if R[i][c]), None)
        if p is None: continue
        R[r], R[p] = R[p], R[r]
        iv = INV[R[r][c]]; R[r] = [MUL[x][iv] for x in R[r]]
        for i in range(len(R)):
            if i != r and R[i][c]:
                Mnf = MUL[NEG[R[i][c]]]
                R[i] = [ADD[R[i][t]][Mnf[R[r][t]]] for t in range(ncols)]
        r += 1
        if r == len(R): break
    return r

def matvec_cols(cols, m, v, F):
    """M = [cols] (each col a length-m list); returns M v"""
    ADD, MUL = F.ADD, F.MUL
    out = [0]*m
    for j, c in enumerate(cols):
        vj = v[j]
        if vj:
            Mv = MUL[vj]
            for i in range(m):
                if c[i]: out[i] = ADD[out[i]][Mv[c[i]]]
    return out

def controllable(cols, m, b, F):
    """is b a cyclic vector of the matrix with the given columns?  (Krylov rank == m)"""
    kry = [list(b)]; v = list(b)
    for _ in range(m-1):
        v = matvec_cols(cols, m, v, F); kry.append(v)
    return rank_rows(kry, m, F) == m

def T_test(colvecs, m, F):
    """(T_m) on the m x (m+1) matrix whose columns are colvecs: returns a witness (j, tau) or None"""
    idx = list(range(m+1))
    for j in idx:
        b = colvecs[j]
        others = [colvecs[t] for t in idx if t != j]
        for tau in itertools.permutations(range(m)):
            # C P_tau has column l = others[tau[l]]
            if controllable([others[tau[l]] for l in range(m)], m, b, F):
                return (j, tau)
    return None

print("ROUND 6-B: controllable-row-block certificate -- (T_m) and (S)")
# controls
F2 = GF(2)
assert controllable([[0,1],[1,0]], 2, [1,0], F2)          # swap, b=e1: e1, e2 -> cyclic vector
assert not controllable([[1,0],[0,1]], 2, [1,0], F2)      # identity: never
assert T_test([[1,0],[0,1],[1,1]], 2, F2) is not None      # [I | 1] at m=2
print("controls ok")

# ---- (T_m): all m x (m+1) matrices of rank m, up to column order (columns as sorted multisets)
def vec_of_int(x, m, q):
    v = []
    for _ in range(m):
        v.append(x % q); x //= q
    return v

for (m, q) in [(2, 2), (2, 3), (3, 2), (3, 3), (4, 2), (2, 4), (2, 5), (3, 4)]:
    check_time("T cell %d %d" % (m, q))
    F = GF(q)
    vecs = [vec_of_int(x, m, q) for x in range(q**m)]
    tot = 0; fail = 0; examples = []
    for comb in itertools.combinations_with_replacement(range(q**m), m+1):
        cols = [vecs[x] for x in comb]
        if rank_rows([[cols[j][i] for j in range(m+1)] for i in range(m)], m+1, F) < m:
            continue
        tot += 1
        if T_test(cols, m, F) is None:
            fail += 1
            if len(examples) < 5: examples.append(comb)
    print("(T_%d) over GF(%d): rank-%d column-multisets=%d  FAILURES=%d  examples(as column ints)=%s  [%.1fs]"
          % (m, q, m, tot, fail, examples, time.time()-T0))

# ---- (S) on all of GL(4,2) and GL(3,q), compared with 16.95 (which holds there)
def perm_matrix_cols(s, n):
    return [[1 if s[j] == i else 0 for i in range(n)] for j in range(n)]

for (n, q) in [(3, 2), (3, 3), (4, 2), (3, 4), (3, 5)]:
    check_time("S cell %d %d" % (n, q))
    F = GF(q)
    m = n-1
    tot = 0; S_fail = 0; both_fail = 0; ex = []
    for entries in itertools.product(range(q), repeat=n*n):
        rows = [list(entries[i*n:(i+1)*n]) for i in range(n)]
        if rank_rows(rows, n, F) < n: continue
        tot += 1
        okS = False
        for i in range(n):
            R = [rows[r] for r in range(n) if r != i]           # m x n
            cols = [[R[r][c] for r in range(m)] for c in range(n)]
            if T_test(cols, m, F) is not None:
                okS = True; break
        if not okS:
            S_fail += 1
            if len(ex) < 6: ex.append(entries)
            # 16.95 check for this A (must hold in these cells)
            A = tuple(entries)
            good = False
            for s in itertools.permutations(range(n)):
                P = tuple(1 if s[j] == i else 0 for i in range(n) for j in range(n))
                M = [0]*(n*n)
                for i2 in range(n):
                    for j2 in range(n):
                        acc = 0
                        for k in range(n):
                            if A[i2*n+k] and P[k*n+j2]:
                                acc = F.ADD[acc][F.MUL[A[i2*n+k]][P[k*n+j2]]]
                        M[i2*n+j2] = acc
                if cyclic(tuple(M), n, F):
                    good = True; break
            if not good: both_fail += 1
    print("(S) over GL(%d,%d): |GL|=%d  (S)-FAILURES=%d  of which also 16.95-failures=%d  examples=%s  [%.1fs]"
          % (n, q, tot, S_fail, both_fail, ex, time.time()-T0))
print("done %.1fs" % (time.time()-T0))

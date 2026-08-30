#!/usr/bin/env python3
"""Independent exhaustive GF(2)/GF(3) audit of the rank-one stratum."""
from __future__ import annotations
import itertools, json, time
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
N = 5
PERMS = tuple(itertools.permutations(range(N)))

def mul(a, b, p):
    return [[sum(a[i][k]*b[k][j] for k in range(N)) % p for j in range(N)] for i in range(N)]

def rank(matrix, p):
    a = [[x % p for x in row] for row in matrix]; r = 0
    for c in range(len(a[0])):
        pivot = next((i for i in range(r, len(a)) if a[i][c]), None)
        if pivot is None: continue
        a[r], a[pivot] = a[pivot], a[r]
        inv = pow(a[r][c], -1, p); a[r] = [x*inv % p for x in a[r]]
        for i in range(len(a)):
            if i != r and a[i][c]:
                q=a[i][c]; a[i]=[(a[i][j]-q*a[r][j])%p for j in range(len(a[0]))]
        r += 1
        if r == len(a[0]): break
    return r

def cyclic(a, permutation, p):
    b = [[a[i][permutation[j]] for j in range(N)] for i in range(N)]
    powers = [[[int(i==j) for j in range(N)] for i in range(N)]]
    for _ in range(4): powers.append(mul(powers[-1], b, p))
    columns = [[powers[k][i][j] for k in range(N)] for i in range(N) for j in range(N)]
    return rank(columns, p) == N

def projective_vectors(p):
    for first in range(N):
        for tail in itertools.product(range(p), repeat=N-first-1):
            yield (0,)*first + (1,) + tail

def audit(p):
    started=time.time(); tested=0; witnesses=Counter(); failures=[]
    identity=[[int(i==j) for j in range(N)] for i in range(N)]
    for v in projective_vectors(p):
        for u in itertools.product(range(p), repeat=N):
            if not any(u) or (1+sum(u[i]*v[i] for i in range(N))) % p == 0: continue
            tested += 1
            a=[[(identity[i][j]+u[i]*v[j])%p for j in range(N)] for i in range(N)]
            witness=next((index for index,perm in enumerate(PERMS) if cyclic(a,perm,p)),None)
            if witness is None: failures.append({"u":u,"v":v})
            else: witnesses[witness]+=1
    # Exclude the p^4 vectors on v.u=-1, then exclude u=0 for exact rank one.
    expected=((p**N-1)//(p-1))*(p**N-p**(N-1)-1)
    assert tested == expected and not failures
    return {"characteristic":p,"projective_v":(p**N-1)//(p-1),
            "rank_one_invertible_matrices":tested,"failed":0,
            "witness_permutation_counts":dict(sorted(witnesses.items())),
            "seconds":round(time.time()-started,3),"verified":True}

def main():
    report={"audits":[audit(2),audit(3)],"verified":True}
    (HERE/"finite_audit.json").write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(report,indent=2))

if __name__ == "__main__": main()

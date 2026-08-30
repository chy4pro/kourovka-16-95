#!/usr/bin/env python3
"""Self-contained checks for the four explicit C7 refutations."""
import itertools
import json
from pathlib import Path

DATA = json.loads((Path(__file__).with_name("REFUTATIONS.json")).read_text())

def add(a, b, q):
    return (a + b) % q if q != 4 else a ^ b

def mul(a, b, q):
    if q != 4:
        return a * b % q
    out = 0
    x, y = a, b
    while y:
        if y & 1: out ^= x
        y >>= 1; x <<= 1
        if x & 4: x ^= 7
    return out

def inv(a, q):
    for b in range(1, q):
        if mul(a, b, q) == 1: return b
    raise ZeroDivisionError

def rank(rows, q):
    a = [row[:] for row in rows]; r = 0
    for c in range(len(a[0])):
        pivot = next((i for i in range(r, len(a)) if a[i][c]), None)
        if pivot is None: continue
        a[r], a[pivot] = a[pivot], a[r]
        z = inv(a[r][c], q); a[r] = [mul(z, v, q) for v in a[r]]
        for i in range(len(a)):
            if i != r and a[i][c]:
                z = a[i][c]
                a[i] = [add(a[i][j], mul(z, a[r][j], q), q) if q == 4 else (a[i][j] - mul(z, a[r][j], q)) % q for j in range(len(a[0]))]
        r += 1
    return r

def mm(a, b, q):
    return [[sum((mul(a[i][k], b[k][j], q) for k in range(len(b))), 0) % q if q != 4 else _xor([mul(a[i][k], b[k][j], q) for k in range(len(b))]) for j in range(len(b[0]))] for i in range(len(a))]

def _xor(xs):
    out = 0
    for x in xs: out ^= x
    return out

def permute_columns(a, p):
    return [[row[p[j]] for j in range(len(p))] for row in a]

def cyclic(a, q):
    n = len(a); power = [[int(i == j) for j in range(n)] for i in range(n)]; cols = []
    for _ in range(n):
        cols.append([power[i][j] for i in range(n) for j in range(n)])
        power = mm(power, a, q)
    return rank([list(x) for x in zip(*cols)], q) == n

def kd(a, q):
    n = len(a); v = [1] + [0] * (n - 1); cols = []
    for _ in range(n):
        cols.append(v); v = [(_xor([mul(a[i][j], v[j], q) for j in range(n)]) if q == 4 else sum(mul(a[i][j], v[j], q) for j in range(n)) % q) for i in range(n)]
    return rank([list(x) for x in zip(*cols)], q)

def transpositions(n):
    for i in range(n):
        for j in range(i + 1, n):
            p = list(range(n)); p[i], p[j] = p[j], p[i]; yield (i, j), tuple(p)

def cycle_type(p):
    seen = set(); out = []
    for i in range(len(p)):
        if i not in seen:
            j = i; n = 0
            while j not in seen: seen.add(j); n += 1; j = p[j]
            out.append(n)
    return tuple(sorted(out, reverse=True))

a7 = DATA["transposition_only_gf7"]
assert all(not cyclic(permute_columns(a7, p), 7) for _, p in transpositions(4))
double_good = sum(cyclic(permute_columns(a7, p), 7) for p in itertools.permutations(range(4)) if cycle_type(p) == (2, 2))
assert double_good == 2

m = DATA["phi_prime_gf2"]; base = kd(m, 2); assert base == 5
profile = [(pair, kd(permute_columns(m, p), 2)) for pair, p in transpositions(6)]
neutral = [pair for pair, value in profile if value == base]
assert neutral == [(0, 4), (1, 4), (2, 4)]

c = DATA["neutral_then_ascent_gf4"]; base = kd(c, 4); assert base == 4
neighbors = [(pair, p, kd(permute_columns(c, p), 4)) for pair, p in transpositions(5)]
assert [v for _, _, v in neighbors] == [3, 3, 4, 4, 3, 3, 3, 2, 2, 2]
for _, first, value in neighbors:
    if value == base:
        b = permute_columns(c, first)
        assert max(kd(permute_columns(b, second), 4) for _, second in transpositions(5)) <= base

face = DATA["face_matching_transposition"]
four_bad = [p for p in itertools.permutations(range(4)) if cycle_type(p) == (4,) and not cyclic(permute_columns(face, p), 5)]
three_good = [p for p in itertools.permutations(range(4)) if cycle_type(p) == (3, 1) and cyclic(permute_columns(face, p), 5)]
assert len(four_bad) == 6 and len(three_good) == 4
print("PASS C7 transposition-only GF(7): six bad, two double transpositions good")
print("PASS C7 potential: kd=5 and neutral swaps (15),(25),(35)")
print("PASS C7 neutral-then-ascent: complete GF(4) profile and no such path")
print("PASS C7 face matching: six bad 4-cycles but only four good 3-cycles")

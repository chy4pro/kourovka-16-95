#!/usr/bin/env python3
"""ROUND 6-V: independent verification of a Singular lift(I, ideal(1)) cofactor certificate.
Reads the generators g_1..g_m from a Singular script (the lines between 'ideal I =' and ';') and the
cofactors h_1..h_m from the file written by write(":w ...", T) (comma-separated polynomials over Q),
checks sum h_i g_i == 1 exactly with sympy, and reports the common denominator D of all cofactor
coefficients with its prime factorisation: the certificate proves the unit ideal in every
characteristic p not dividing D (reduce mod p); the primes p | D must be checked separately.
Usage: round6_verify_cofactors.py <script.sing> <cofactors.txt>   -> prints VERIFIED / FAILED, D, primes"""
import sys, re
import sympy as sp
from sympy import Rational

sing, cof = sys.argv[1], sys.argv[2]
src = open(sing).read()
ring = re.search(r"ring\s+\w+\s*=\s*\S+\s*,\s*\(([^)]*)\)", src).group(1)
names = [v.strip() for v in ring.split(",")]
syms = sp.symbols(names)
loc = dict(zip(names, syms))
body = src[src.index("ideal I =") + len("ideal I ="):]
body = body[:body.index(";")]
gens = [sp.sympify(t.strip().replace("^", "**"), locals=loc) for t in body.split(",") if t.strip()]
# cofactor file: one entry per line and/or comma-separated (Singular write of string(T[i,1]) + ",")
cofs = [sp.sympify(t.strip().replace("^", "**"), locals=loc) for t in re.split(r"[,\n]", open(cof).read()) if t.strip()]
print("generators %d, cofactors %d, variables %s" % (len(gens), len(cofs), names))
if len(gens) != len(cofs):
    print("FAILED: length mismatch"); sys.exit(1)
total = sp.expand(sum(h * g for h, g in zip(cofs, gens)))
ok = (total == 1)
D = sp.Integer(1)
maxdeg = 0
for h in cofs:
    P = sp.Poly(h, *syms)
    maxdeg = max(maxdeg, P.total_degree() if not P.is_zero else 0)
    for c in P.coeffs():
        D = sp.ilcm(D, Rational(c).q)
print("sum h_i g_i == 1: %s   (max cofactor degree %d)" % (ok, maxdeg))
print("common denominator D = %s = %s" % (D, sp.factorint(D)))
print("VERIFIED: unit ideal in every characteristic p not dividing D; primes to check separately: %s"
      % sorted(sp.factorint(D).keys()) if ok else "FAILED: certificate does not sum to 1")
sys.exit(0 if ok else 1)

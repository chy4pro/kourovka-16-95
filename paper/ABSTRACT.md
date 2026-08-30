# Companion manuscript

## Abstract

For a field $K$ and $A\in\mathrm{GL}_n(K)$, Thompson asked whether some column permutation $AP_\sigma$ is cyclic. We prove the assertion for $n\leq3$ over every field. The case $n=3$ is kernel-checked in Lean, while the cases $n\leq2$ are elementary. For $n=4$ we prove it over every field of characteristic zero, in characteristics $2,3,5,7,11,13,17,19,23$, and in all but finitely many characteristics. The $n=4$ proof normalizes a hypothetical counterexample to $I+R$ with $\operatorname{rank} R\leq2$. The rank-one and rank-two strata are then closed by explicit unit-ideal certificates checked with msolve; independent encoder families are available in the characteristics recorded in the manuscript. A separate Lean proof shows that when the minimal polynomial of $A$ is an irreducible quadratic, every transposition works. For $n=5$, we prove the rank-one stratum $A=\lambda(I+uv^T)$ over characteristic zero and every prime characteristic below $2000$. This appears to be the first $n=5$ case of any kind. For every dimension, we further prove the rank-one cases in which $u$ or $w$ has support at most three, or is constant on the support of the other vector.

To the best of our knowledge, this is the first proof of Thompson's conjecture for $n=3$ over arbitrary fields and the first formal verification of a nontrivial case of Problem 16.95; the $4\times4$ results (the irreducible-quadratic stratum over every field, and every field of characteristic $0$ or $p\in\{2,3,5,7,11,13,17,19,23\}$) appear to be the first results of this scope.

The finite exceptional set in the rank-two argument is contained in the prime divisors of an explicit, but not yet computed, product $N$ of contraction generators. Thus we do *not* claim the result for every field in dimension four.

This repository is the verification/falsification supplement; the exact status ledger is `../CLAIMS.md`.

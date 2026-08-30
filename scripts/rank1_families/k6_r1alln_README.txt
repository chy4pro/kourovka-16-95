K6-R1ALLN exact verification bundle
==================================

Files
-----
k6_r1alln_verify.cpp
  Exhaustive verifier over a prime field F_p for the deflation system
    c_0=x, c_k=e_k+y_k x  (1 <= k <= m).
  For every (x,y), it searches for an omitted column b=c_j and an ordering
  tau of the other m columns such that
    det[b, M b, ..., M^(m-1)b] != 0,
  where M=[c_tau(1) ... c_tau(m)].

k6_r1alln_identity_check.py
  Exact SymPy checker over Z for the path/resultant identity, the
  path-plus-fixed-point identity, the four m=2 closed forms, and the
  constant-x telescoping identity.

k6_r1alln_runs.txt
  Transcript of completed exhaustive prime-field runs.

k6_r1alln_identity_runs.txt
  Transcript of completed symbolic identity checks.

Build and use
-------------
g++ -O3 -std=c++17 -Wall -Wextra -pedantic \
  k6_r1alln_verify.cpp -o k6_r1alln_verify

./k6_r1alln_verify PRIME_P M all
./k6_r1alln_verify PRIME_P M restricted

python k6_r1alln_identity_check.py

PRIME_P must be prime.  The finite verifier makes no claim about extension
fields.  Here m=n-1.

Candidate modes
---------------
all:
  All (m+1)! choices (omitted column, ordering of the remaining columns).

restricted:
  A witness-only subset:
    * omit c_0 and use an m-cycle: (m-1)! candidates;
    * an ordinary Hamilton path ending in c_0: m! candidates;
    * such a path plus one fixed ordinary vertex: m! candidates.
  Thus a successful restricted run is stronger than needed: every tested
  point already has a witness in this subset.  It does not assert that the
  omitted longer-cycle candidates are redundant in general.

Sound cache
-----------
For c_0=x, M=P+x q^T.  State feedback along the input x preserves the
Krylov determinant, so D_{0,tau}=det[x,Px,...,P^(m-1)x] is independent of y.
The verifier therefore tests c_0 candidates once per x at y=0 and skips all
values of y when one succeeds.

Completed runs in k6_r1alln_runs.txt
------------------------------------
  F_2: m=1,...,8  (n=2,...,9), restricted, all x,y.
  F_3: m=1,...,6  (n=2,...,7), restricted, all x,y.
  F_5: m=5        (n=6),       restricted, all x,y.
  F_7: m=4        (n=5),       restricted, all x,y.
  F_2: m=5        (n=6),       all (all 720 arrangements), all x,y.

No counterexample was found in any completed run.

SHA-256 (recorded 2026-08-30)
-----------------------------
af2f705a709c40f5e729e95735b4ab5bd9fa152793239063dbe2dc780bb45781  k6_r1alln_verify.cpp
28243e9d1f0e7f36fe4db8d3232b35d7cf57ba1ccc28f8d4a92d5fc1ea34d169  k6_r1alln_verify
75f210180e812df0772dae65544401803b2fa63e8579849757f63b8d3963b604  k6_r1alln_runs.txt
7c3db54f8f105a9dbe39e3f926d278ecc4ec6194f02255dd432b80222562adf9  k6_r1alln_identity_check.py
89fd5d8b8e578948190be05a7c533dd277ccaf37eac13375e967393486a13718  k6_r1alln_identity_runs.txt

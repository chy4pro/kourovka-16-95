# Claims (Kourovka Notebook problem 16.95, J. G. Thompson): for every field F and A ∈ GL(n,F) there is a permutation matrix P with AP cyclic (minimal polynomial = characteristic polynomial).

## C1

C1 [Lean, kernel-checked] n = 3, every field: K1695.kourovka_16_95_n3. Strengthening (GC3): at least two column permutations make e1 a cyclic vector (K1695.goodCount3). The cases n ≤ 2 are elementary and are not claimed as Lean declarations. verify.sh: lean.

Evidence: `lean/K1695/CyclicToMinpoly.lean`, `lean/K1695/CyclicVectorThree.lean`, `lean/K1695/GoodCount3.lean`, and `lean/recorded_checks/round6_gc3lean_check.log`.

## C2

C2 [Lean, kernel-checked] n = 4, every field, stratum "minimal polynomial an irreducible quadratic": EVERY transposition works (K1695.stratumB_minpoly); the rank-to-minimal-polynomial bridge for every n (K1695.minpoly_eq_charpoly_of_rank_ge). verify.sh: lean.

Evidence: `lean/K1695/StratumBMinpoly.lean`, `lean/K1695/RankToMinpoly.lean`, and the recorded axiom audits under `lean/recorded_checks/`.

## C3

C3 [hand + Lean-checked Lemma T] Normalisation: if all 24 AP_σ are non-cyclic then, after scaling by an eigenvalue of geometric multiplicity ≥ 2, A = I + R with rank R ≤ 2. (Proof in the paper.)

Evidence: `lean/K1695/TranspositionLemma.lean`, `lean/K1695/TranspositionLemmaFull.lean`, and `paper/ABSTRACT.md` (the complete hand proof is in the companion manuscript).

## C4

C4 [Gröbner certificates, two independent encoders] n = 4, rank R ≤ 1: some AP_σ is cyclic over every field of characteristic 0 and of every prime characteristic p < 10^4 (msolve unit ideals). verify.sh: rank1.

Evidence: bases under `certificates/rank1/`, source under `encoders/`, raw inputs indexed by `BUNDLE_INDEX.sha256`, and release-asset digest in `release/SHA256SUMS`.

## C5

C5 [Gröbner certificates, two independent encoders, two independent searches] n = 4, rank R = 2: some AP_σ is cyclic over every field of characteristic 0, 2, 3, 5, 7, 11, 13, 17, 19, 23 (case decomposition over the W-chart and six U-charts; every terminal ideal is the unit ideal). Every listed characteristic has two complete families. For 17, 19, and 23 the K6-R2SPLIT-1723 family has representative-chart trees of 826/806/797 runs with 795/781/775 unit terminals; the same replay verifies completion of the second p = 13 family. verify.sh: rank2-<p>.

Evidence: every recorded basis under `certificates/`, the DPLL states and node metadata under `certificates/trees/`, `data/SUMMARY.json`, and the indexed raw-input bundle.

## C6

C6 [theorem, from C3–C5 + transfer] n = 4: Kourovka 16.95 holds over every field of characteristic 0, over every field of characteristic p for p ∈ {2,3,5,7,11,13,17,19,23}, and over all but finitely many characteristics (ACF_0 → ACF_p transfer for the universal sentence; the exceptional set is contained in the primes dividing an explicit integer N = product of the contraction generators d_S of the terminal ideals, whose computation is in progress). NOT claimed: "every field" (until N is known and its primes are run).

Evidence: C3–C5 above and `REPRODUCE.md`; no stronger status is asserted here.

## C7

C7 [refutations, explicit matrices with verifiers] the transposition-only rule (odd characteristic families), the potential Φ' = (kd, −ν) (n = 6 over F2), the neutral-then-ascent rule (n = 5 over F4), the face-matching lemma (transposition matrices). verify.sh: data.

Evidence: `data/refutations/REFUTATIONS.json` and `data/refutations/verify_refutations.py`.

## C7'

C7' [exact integer content, computed] As of 2026-08-30 12:0x CDT, for 2,394 of the 4,694 characteristic-zero rank-two terminals the contraction generator d_S = generator of I_S ∩ Z has been computed exactly by a strong Gröbner basis over Z (Singular 4.3.2): d_S = 1 for 1,383 terminals, d_S = 2 for 1,006 terminals, and d_S = 3 for 5 terminals. Every prime dividing a computed d_S lies in {2,3}. Hence on those resolved terminals the certificate is valid in every characteristic; the explicit exceptional set restricted to them is contained in {2,3}, both closed directly.

Evidence: `scripts/round6_zstd_one.py`, `scripts/zlift_one_v2.py`, `scripts/zlift_one_v3.py`, `data/zstd/results.tsv`, and `data/zstd/run8_results.tsv`.

OPEN: n ≥ 5 in every characteristic; n = 4 for the finitely many unknown exceptional primes.

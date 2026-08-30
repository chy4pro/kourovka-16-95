# Rank-one families and finite-field checks

This directory accompanies claims C9 and C10. The paper contains the proofs for the sparse and constant rank-one families in every dimension. The Python programs check the identities used in those proofs. The two compiled programs independently exhaust the finite prime-field ranges stated in C10; they make no claim about extension fields or algebraic closures.

The full-witness C99 verifier is compiled and run as follows:

```sh
cc -O2 round6_r1alln_exhaust.c -o round6_r1alln_exhaust
./round6_r1alln_exhaust 2 4
```

Its archived multi-parameter output is `round6_r1alln_exhaust.log`. The repository's quick check repeats only the displayed $p=2$, $m=4$ command and requires `points=256 all_witnessed=1 bad=0`.

The independent C++17 verifier is compiled and run as follows:

```sh
g++ -O3 -std=c++17 -Wall -Wextra -pedantic k6_r1alln_verify.cpp -o k6_r1alln_verify
./k6_r1alln_verify PRIME_P M restricted
./k6_r1alln_verify PRIME_P M all
```

The completed upstream run table is preserved byte-for-byte as `k6_r1alln_runs.txt` and as the convenient alias `runs.txt`; `round6_r1alln_theirs.log` records the independent rerun. `k6_r1alln_SHA256SUMS.txt` authenticates the original five-file verifier bundle, while `SHA256SUMS` authenticates the complete release-facing set in this directory.

The identity checkers are run as follows:

```sh
python3 round6_r1alln_check.py
python3 k6_r1alln_identity_check.py
```

Their recorded outputs are `round6_r1alln_check.log` and `k6_r1alln_identity_runs.txt`.

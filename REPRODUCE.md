# Reproduction guide

## Environment

Use the pinned versions in `VERSIONS.md`. Set `MSOLVE` when the executable is not on `PATH`.

## Quick and Lean checks

`./verify.sh quick` is designed for a laptop and runs no Gröbner solver. It validates the manifest, recorded Lean audits, certificate inventories, finite audits, and refutation data; it also compiles the C99 rank-one verifier with `cc -O2` and exhausts the 256 points for $p=2$, $m=4$. The recorded Lean files took 5–12 seconds each after Mathlib was built; the largest recorded axiom check took 127.5 seconds. A fresh Mathlib build can use several GiB, so it is intentionally opt-in:

```sh
./verify.sh lean-build
```

This runs `lake build`, then checks the named files with `lake env lean`. The recorded `#print axioms` outputs contain only `propext`, `Classical.choice`, and `Quot.sound`.

## Certificate replay

Extract the release asset over the repository so its `certificates/` tree is visible, then run:

```sh
./verify.sh full /path/to/extracted/asset
```

The compact public asset contains all non-regenerable `.gb` outputs and DPLL JSON. It omits routine regenerable `.ms` bodies and per-node logs, retaining no more than 50 input self-tests; the nine realised control inputs and their logs remain as evidence rather than self-test samples. Other logs are retained only for capped/hard terminals and failure rows. A terminal unit certificate has body `[1]`; non-unit prefixes and realised controls remain part of the exhaustive evidence.

The original searches used one solver child at a time, a 600-second per-node wall cap, and a 2,500,000 KiB process-tree memory cap. Typical completed nodes took seconds; end-to-end chart runs took minutes to hours depending on characteristic and cache state. Counts are in `data/SUMMARY.json`.

## Regenerate recorded inputs byte-for-byte

For any recorded independent-family state, regenerate every node with:

```sh
python3 scripts/regenerate_from_state.py \
  certificates/k1695_r6_r2split1723/certificates/state_p17_uc0.json \
  generated/p17-chart0
shasum -a 256 generated/p17-chart0/*.ms
```

Compare the emitted hashes with `BUNDLE_INDEX.sha256`. Use `--sample-count 20` for a deterministic evenly spaced audit. The publication revision checked 20 nodes in each of characteristics 0, 2, 3, 5, 7, 11, 13, 17, 19, and 23, for 200 byte-identical regenerations.

## Generate a new search

```sh
python3 scripts/regenerate_ms.py --family line --p 37 --chart 0 --start-depth 6 --out generated/p37-chart0
python3 scripts/regenerate_ms.py --family independent --p 13 --chart 5 --start-depth 6 --max-runs 1 --out generated/p13-chart5
```

The first command is the public falsification hook. It enumerates algebraic badness cases for a new characteristic; a complete non-unit leaf must be resolved and tested with the exact cyclic oracle before it is interpreted.

## Independent falsification

```sh
python3 falsify/find_counterexample.py --p 37 --trials 10000
```

This searches random invertible matrices over a prime field and prints a full witness only if all 24 products are non-cyclic. Absence of a witness is not a proof.

# Reproduction guide

## Environment

Use the pinned versions in `VERSIONS.md`. Set `MSOLVE` when the executable is not on `PATH`.

## Quick and Lean checks

`./verify.sh quick` is designed for a laptop and uses at most one msolve process. The recorded Lean files took 5–12 seconds each after Mathlib was built; the largest recorded axiom check took 127.5 seconds. A fresh Mathlib build can use several GiB, so it is intentionally opt-in:

```sh
./verify.sh lean-build
```

This runs `lake build`, then checks the named files with `lake env lean`. The recorded `#print axioms` outputs contain only `propext`, `Classical.choice`, and `Quot.sound`.

## Certificate replay

Extract the release asset so its `certificates/` tree is visible, then run:

```sh
./verify.sh full /path/to/extracted/asset
```

Each raw input is replayed as `msolve -g 2 -t 1 -f X.ms -o X.gb`; a terminal unit certificate has body `[1]`. Non-unit prefixes and realised controls are retained because they are part of the exhaustive DPLL evidence, and their expected status is recorded in the adjacent JSON.

The original searches used one solver child at a time, a 600-second per-node wall cap, and a 2,500,000 KiB process-tree memory cap. Typical completed nodes took seconds; end-to-end chart runs took minutes to hours depending on characteristic and cache state. Counts are in `data/SUMMARY.json`.

## Regenerate inputs

```sh
python3 scripts/regenerate_ms.py --family line --p 37 --chart 0 --start-depth 6 --out generated/p37-chart0
python3 scripts/regenerate_ms.py --family independent --p 13 --chart 5 --start-depth 6 --max-runs 1 --out generated/p13-chart5
```

The first command is the public falsification hook. It enumerates algebraic badness cases for a new characteristic; a complete non-unit leaf must be solved and tested with the exact cyclic oracle before it is interpreted.

## Independent falsification

```sh
python3 falsify/find_counterexample.py --p 37 --trials 10000
```

This searches random invertible matrices over a prime field and prints a full witness only if all 24 products are non-cyclic. Absence of a witness is not a proof.

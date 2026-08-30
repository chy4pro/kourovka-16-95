# Kourovka 16.95 verification and falsification package

This local prepublication package accompanies work on J. G. Thompson's Kourovka Notebook problem 16.95. It contains the exact, deliberately limited claims in `CLAIMS.md`, recorded Gröbner bases, complete tree/control metadata, independent encoder implementations, Lean sources and recorded kernel axiom audits, and explicit refutations of four tempting intermediate rules.

It does **not** claim the problem over every field or in dimensions at least five. Nothing here has been pushed or published.

## Five-minute check

Install msolve 0.10.1 and Python 3 with SymPy, then run:

```sh
./verify.sh quick
```

The quick target validates repository integrity, checks the exact claims text and recorded Lean audits, checks representative recorded bases, regenerates one K6-R2SPLIT-1723 sample byte-for-byte for each of p = 17, 19, 23, reruns each sample sequentially through the recorded 600-second/2,500,000-KiB wrapper, and independently verifies all four explicit refutations. The ticket intentionally prohibited a Lean build during assembly; `./verify.sh lean-build` is the opt-in kernel rebuild.

## Longer checks

```sh
./verify.sh lean
./verify.sh rank1
./verify.sh rank2-0
./verify.sh rank2-2
./verify.sh rank2-3
./verify.sh data
./verify.sh full /path/to/extracted/release-asset
```

See `REPRODUCE.md` for expected output, runtime tiers, release-asset extraction, and trying a new prime.

## Repository/release split

The Git tree contains the compact proof metadata, controls, source, Lean files, and the established basis families. The 25,795,157-byte `kourovka-16-95-certificates-v2.tar.zst` release asset supplies the large completed p = 13, 17, 19, 23 independent-family basis/JSON branch sets. Regenerable `.ms` bodies are replaced by `REGENERABLE_MS.sha256` and 50 total self-test samples (47 in the asset and three in Git); nine additional control inputs are retained because the controls themselves are evidence. Routine per-node logs are omitted, while capped/hard-terminal, failure, and control logs are retained. `scripts/regenerate_from_state.py` recreates recorded inputs byte-for-byte from the DPLL state, and `BUNDLE_INDEX.sha256` authenticates the public asset members.

Code is MIT licensed (`LICENSE`); text and data are CC BY 4.0 (`LICENSE-CC-BY-4.0`).

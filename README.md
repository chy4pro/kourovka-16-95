# Kourovka 16.95 verification and falsification package

This local prepublication package accompanies work on R. C. Thompson's Kourovka Notebook problem 16.95. It contains the exact, deliberately limited claims in `CLAIMS.md`, 54,727 recorded Gröbner bases, complete tree/control metadata, two encoder implementations, Lean sources and recorded kernel axiom audits, and explicit refutations of four tempting intermediate rules.

It does **not** claim the problem over every field or in dimensions at least five. Nothing here has been pushed or published.

## Five-minute check

Install msolve 0.10.1 and Python 3 with SymPy, then run:

```sh
./verify.sh quick
```

The quick target validates repository integrity, checks the exact claims text and recorded Lean audits, checks representative recorded bases, runs a tiny unit-ideal job with one msolve process, and independently verifies all four explicit refutations. The ticket intentionally prohibited a Lean build during assembly; `./verify.sh lean-build` is the opt-in kernel rebuild.

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

All `.gb` outputs, DPLL trees and JSON, controls, source, Lean, and documentation are versioned here. Raw `.ms` inputs and per-node logs live in `kourovka-16-95-certificates-v1.tar.zst`; `BUNDLE_INDEX.sha256` authenticates each member and `release/SHA256SUMS` authenticates the asset. `scripts/regenerate_ms.py` and `encoders/line/run_decomposition.py` provide regeneration entry points.

Code is MIT licensed (`LICENSE`); text and data are CC BY 4.0 (`LICENSE-CC-BY-4.0`).

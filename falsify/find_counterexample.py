#!/usr/bin/env python3
"""Random prime-field search for an invertible all-24-bad 4 by 4 matrix."""
import argparse, itertools, random
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "data/refutations"))
from verify_refutations import cyclic, permute_columns, rank

ap = argparse.ArgumentParser()
ap.add_argument("--p", type=int, required=True)
ap.add_argument("--trials", type=int, default=10000)
ap.add_argument("--seed", type=int, default=1695)
args = ap.parse_args(); rng = random.Random(args.seed)
perms = list(itertools.permutations(range(4)))
for trial in range(1, args.trials + 1):
    a = [[rng.randrange(args.p) for _ in range(4)] for _ in range(4)]
    if rank(a, args.p) < 4: continue
    good = [p for p in perms if cyclic(permute_columns(a, p), args.p)]
    if not good:
        print(f"CANDIDATE p={args.p} trial={trial} matrix={a}")
        raise SystemExit(1)
print(f"NO-CANDIDATE p={args.p} trials={args.trials}; this is not a proof")

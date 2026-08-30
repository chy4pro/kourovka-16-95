#!/usr/bin/env python3
"""DPLL driver for K6-R2SPLIT in characteristics 17, 19, and 23."""
from __future__ import annotations

import argparse
import contextlib
import json
import os
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
LINEAGE = ROOT / "encoders/independent"
sys.path.insert(0, str(LINEAGE))

from r2split357_search import dpll, summary  # noqa: E402
from r2split_encoder import inventory  # noqa: E402


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--characteristic", "-p", type=int, choices=(17, 19, 23), required=True)
    parser.add_argument("--u-chart", type=int, choices=range(6), required=True)
    parser.add_argument("--start-depth", type=int, default=6)
    parser.add_argument("--max-runs", type=int, default=1)
    parser.add_argument("--quiet", action="store_true", help="suppress per-node Python output")
    parser.add_argument("--output-dir", type=Path, default=HERE / "certificates")
    args = parser.parse_args()
    inventory_path = HERE / f"inventory_p{args.characteristic}.json"
    inventory_path.write_text(json.dumps(inventory(args.characteristic), indent=2) + "\n")
    if args.quiet:
        with open(os.devnull, "w") as sink, contextlib.redirect_stdout(sink):
            state = dpll(args.characteristic, args.u_chart, args.output_dir, args.start_depth, args.max_runs)
    else:
        state = dpll(args.characteristic, args.u_chart, args.output_dir, args.start_depth, args.max_runs)
    print("SUMMARY " + json.dumps(summary(state)), flush=True)


if __name__ == "__main__":
    try:
        main()
    except RuntimeError as error:
        print(f"ERROR: {error}", file=sys.stderr)
        raise SystemExit(2)

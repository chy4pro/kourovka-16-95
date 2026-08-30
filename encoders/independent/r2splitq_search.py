#!/usr/bin/env python3
"""Characteristic-zero driver for the in-house K6 rank-two DPLL search."""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE))

from r2split357_search import ORDER, dpll, summary  # noqa: E402


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--u-chart", type=int, choices=range(6), required=True)
    parser.add_argument("--start-depth", type=int, default=6)
    parser.add_argument("--max-runs", type=int, default=1)
    parser.add_argument("--output-dir", type=Path, default=HERE / "certificates")
    args = parser.parse_args()
    assert len(ORDER) == 23
    state = dpll(0, args.u_chart, args.output_dir, args.start_depth, args.max_runs)
    print("SUMMARY " + json.dumps(summary(state)), flush=True)


if __name__ == "__main__":
    try:
        main()
    except RuntimeError as error:
        print(f"ERROR: {error}", file=sys.stderr)
        raise SystemExit(2)

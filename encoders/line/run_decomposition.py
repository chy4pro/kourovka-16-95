#!/usr/bin/env python3
"""Public wrapper for the primary rank-two decomposition."""
import argparse
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent

parser = argparse.ArgumentParser()
parser.add_argument("--p", type=int, required=True)
parser.add_argument("--chart", type=int, choices=range(6), required=True)
parser.add_argument("--start-depth", type=int, default=6)
parser.add_argument("--max-runs", type=int, default=4000)
parser.add_argument("--out", type=Path, required=True)
args = parser.parse_args()

if args.p == 2:
    command = [sys.executable, str(HERE / "round6_r2split_check.py"), "--charts", str(args.chart), "--out", str(args.out)]
else:
    command = [sys.executable, str(HERE / "round6_r2split_odd.py"), str(args.p), str(args.chart), "--start-depth", str(args.start_depth), "--max-runs", str(args.max_runs), "--out", str(args.out)]
raise SystemExit(subprocess.call(command))

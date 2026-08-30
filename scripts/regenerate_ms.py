#!/usr/bin/env python3
"""Dispatch the public encoders to regenerate raw msolve inputs."""
import argparse
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser()
parser.add_argument("--family", choices=("line", "independent"), required=True)
parser.add_argument("--p", type=int, required=True)
parser.add_argument("--chart", type=int, choices=range(6), required=True)
parser.add_argument("--start-depth", type=int, default=6)
parser.add_argument("--max-runs", type=int, default=1)
parser.add_argument("--out", type=Path, required=True)
args = parser.parse_args()

if args.family == "line":
    script = ROOT / "encoders/line/run_decomposition.py"
    command = [sys.executable, str(script), "--p", str(args.p), "--chart", str(args.chart), "--start-depth", str(args.start_depth), "--max-runs", str(args.max_runs), "--out", str(args.out)]
else:
    if args.p in (3, 5, 7):
        script = ROOT / "encoders/independent/r2split357_search.py"
    elif args.p in (11, 13):
        script = ROOT / "encoders/independent/r2split1113_search.py"
    elif args.p == 0:
        script = ROOT / "encoders/independent/r2splitq_search.py"
    else:
        script = ROOT / "encoders/independent/r2split_search.py"
    command = [sys.executable, str(script), "--characteristic", str(args.p), "--u-chart", str(args.chart), "--start-depth", str(args.start_depth), "--max-runs", str(args.max_runs), "--output-dir", str(args.out)]
raise SystemExit(subprocess.call(command))

#!/usr/bin/env python3
"""Regenerate recorded rank-two msolve inputs from one DPLL state file."""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "encoders/independent"))

from r2split_encoder import parse_case, write_msolve  # noqa: E402


def sample_indices(size: int, count: int) -> list[int]:
    """Return deterministic, evenly spaced indices including both ends."""
    if count <= 0 or count >= size:
        return list(range(size))
    if count == 1:
        return [0]
    return sorted({round(i * (size - 1) / (count - 1)) for i in range(count)})


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("state", type=Path, help="recorded state_*.json")
    parser.add_argument("output", type=Path, help="directory for regenerated .ms files")
    parser.add_argument("--sample-count", type=int, default=0,
                        help="evenly spaced sample size; 0 regenerates every node")
    args = parser.parse_args()

    state = json.loads(args.state.read_text())
    characteristic = int(state["characteristic"])
    chart = int(state["u_chart"])
    results = state["results"]
    args.output.mkdir(parents=True, exist_ok=True)

    for index in sample_indices(len(results), args.sample_count):
        row = results[index]
        cases = [parse_case(characteristic, text) for text in row["cases"]]
        destination = args.output / Path(row["path"]).name
        write_msolve(destination, characteristic, cases, chart)
        digest = hashlib.sha256(destination.read_bytes()).hexdigest()
        print(f"{digest}  {destination.name}")


if __name__ == "__main__":
    main()

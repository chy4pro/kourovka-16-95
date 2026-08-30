#!/usr/bin/env python3
"""Independent replay for K6-R2SPLIT-1723 plus the p=13 chart-5 audit."""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
REPLAY_DIR = ROOT / "encoders/independent"
LEGACY = ROOT / "certificates/trees/k1695_r6_r2split1113"
sys.path.insert(0, str(REPLAY_DIR))

import r2split1113_verify as replay  # noqa: E402


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=HERE / "verification.json")
    args = parser.parse_args()
    report = {
        "characteristics": [17, 19, 23],
        "symmetry_orbits": replay.symmetry_orbits(),
        "representatives": list(replay.REPRESENTATIVES),
        "legacy_p13_chart5": None,
        "primes": [],
    }
    replay.HERE = LEGACY
    legacy = replay.verify_tree(13, 5)
    legacy["control"] = replay.verify_control(13, 5)
    report["legacy_p13_chart5"] = legacy
    replay.HERE = HERE
    for p in (17, 19, 23):
        prime = {"characteristic": p, "inventory": replay.verify_inventory(p), "charts": []}
        for chart in replay.REPRESENTATIVES:
            row = replay.verify_tree(p, chart)
            row["control"] = replay.verify_control(p, chart)
            prime["charts"].append(row)
        report["primes"].append(prime)
    report["verified"] = True
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()

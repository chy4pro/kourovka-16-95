#!/usr/bin/env python3
"""Odd-characteristic DPLL driver for K6-R2SPLIT-357.

The first nine permutations are all six transpositions followed by all three
double transpositions, as required by the ticket.  Three-cycles and then
four-cycles are added only to surviving branches.  State is written after
every msolve result, so a swap-gate stop or an interrupted invocation loses at
most the currently running capped child (whose own log remains on disk).
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE))

from r2split_encoder import Case, PERMS, case_list, cycle_type, parse_case  # noqa: E402
from r2split_search import run_branch  # noqa: E402


def odd_order() -> list[int]:
    by_type = {
        ctype: [i for i, sigma in enumerate(PERMS) if cycle_type(sigma) == ctype]
        for ctype in ((2, 1, 1), (2, 2), (3, 1), (4,))
    }
    return by_type[(2, 1, 1)] + by_type[(2, 2)] + by_type[(3, 1)] + by_type[(4,)]


ORDER = odd_order()
assert len(ORDER) == 23
assert all(cycle_type(PERMS[i]) in ((2, 1, 1), (2, 2)) for i in ORDER[:9])


def peak_rss_kib(result: dict) -> int | None:
    text = Path(result["log"]).read_text(errors="replace")
    match = re.search(r"peak_rss_kib=(\d+)", text)
    return int(match.group(1)) if match else None


def compact_result(result: dict) -> dict:
    return {
        "depth": len(result["cases"]),
        "status": result["status"],
        "seconds": result["seconds"],
        "peak_rss_kib": result.get("peak_rss_kib"),
        "swap_used_mib_at_start": result["swap_used_mib_at_start"],
        "tag": result["tag"],
    }


def encode_node(node: tuple[int, list[Case], bool]) -> dict:
    return {"depth": node[0], "cases": [case.key for case in node[1]], "needs_test": node[2]}


def decode_node(characteristic: int, node: dict) -> tuple[int, list[Case], bool]:
    return node["depth"], [parse_case(characteristic, key) for key in node["cases"]], node["needs_test"]


def save_state(path: Path, state: dict, stack: list[tuple[int, list[Case], bool]]) -> None:
    state["pending"] = [encode_node(node) for node in stack]
    state["pending_nodes"] = len(stack)
    state["status_counts"] = dict(Counter(row["status"] for row in state["results"]))
    state["exhaustive"] = (
        not stack
        and state["complete_nonunit_leaves"] == 0
        and state["open_due_to_load"] == 0
        and state.get("blocked_reason") is None
    )
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(state, indent=2) + "\n")


def dpll(characteristic: int, u_chart: int, output_dir: Path, start_depth: int, max_runs: int) -> dict:
    state_path = output_dir / f"state_p{characteristic}_uc{u_chart}.json"
    if state_path.exists():
        state = json.loads(state_path.read_text())
        if state["permutation_order"] != ORDER or state["start_depth"] != start_depth:
            raise RuntimeError(f"state parameters disagree: {state_path}")
        stack = [decode_node(characteristic, node) for node in state["pending"]]
    else:
        state = {
            "characteristic": characteristic,
            "u_chart": u_chart,
            "start_depth": start_depth,
            "permutation_order": ORDER,
            "results": [],
            "closed_subtrees": 0,
            "complete_nonunit_leaves": 0,
            "open_due_to_load": 0,
            "blocked_reason": None,
            "candidate_leaves": [],
        }
        stack: list[tuple[int, list[Case], bool]] = [(0, [], False)]
    state["blocked_reason"] = None
    invocation_runs = 0
    while stack:
        depth, prefix, needs_test = stack.pop()
        if needs_test:
            if invocation_runs >= max_runs:
                stack.append((depth, prefix, needs_test))
                break
            try:
                result = run_branch(characteristic, prefix, output_dir / "branches", u_chart)
            except RuntimeError as error:
                stack.append((depth, prefix, needs_test))
                state["blocked_reason"] = str(error)
                break
            result["peak_rss_kib"] = peak_rss_kib(result)
            state["results"].append(result)
            invocation_runs += 1
            print(json.dumps(compact_result(result)), flush=True)
            if result["unit"]:
                state["closed_subtrees"] += 1
                save_state(state_path, state, stack)
                continue
            if result["capped"]:
                state["open_due_to_load"] += 1
                save_state(state_path, state, stack)
                continue
        if depth == len(ORDER):
            state["complete_nonunit_leaves"] += 1
            state["candidate_leaves"].append([case.key for case in prefix])
            save_state(state_path, state, stack)
            continue
        index = ORDER[depth]
        for case in reversed(case_list(characteristic, index)):
            child = prefix + [case]
            stack.append((depth + 1, child, depth + 1 >= start_depth))
        save_state(state_path, state, stack)
    state["invocation_runs"] = invocation_runs
    save_state(state_path, state, stack)
    return state


def summary(state: dict) -> dict:
    results = state["results"]
    return {
        "characteristic": state["characteristic"],
        "u_chart": state["u_chart"],
        "total_runs": len(results),
        "invocation_runs": state.get("invocation_runs", 0),
        "closed_subtrees": state["closed_subtrees"],
        "status_counts": state.get("status_counts", {}),
        "pending_nodes": state.get("pending_nodes", 0),
        "open_due_to_load": state["open_due_to_load"],
        "candidate_leaves": len(state["candidate_leaves"]),
        "blocked_reason": state.get("blocked_reason"),
        "exhaustive": state.get("exhaustive", False),
        "max_seconds": max((row["seconds"] for row in results), default=0),
        "max_peak_rss_kib": max((row.get("peak_rss_kib") or 0 for row in results), default=0),
        "max_depth_tested": max((len(row["cases"]) for row in results), default=0),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--characteristic", "-p", type=int, choices=(3, 5, 7), required=True)
    parser.add_argument("--u-chart", type=int, choices=range(6), required=True)
    parser.add_argument("--start-depth", type=int, default=6)
    parser.add_argument("--max-runs", type=int, default=1)
    parser.add_argument("--output-dir", type=Path, default=HERE / "certificates")
    args = parser.parse_args()
    state = dpll(args.characteristic, args.u_chart, args.output_dir, args.start_depth, args.max_runs)
    print("SUMMARY " + json.dumps(summary(state)), flush=True)


if __name__ == "__main__":
    try:
        main()
    except RuntimeError as error:
        print(f"ERROR: {error}", file=sys.stderr)
        raise SystemExit(2)

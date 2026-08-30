#!/usr/bin/env python3
"""Independent structural verifier for the characteristic-two certificates."""
from __future__ import annotations

import itertools
import json
import re
from collections import Counter
from pathlib import Path

from r2split_encoder import BASE_SYMBOLS, ZU, parse_case, ideal

HERE = Path(__file__).resolve().parent
CERT = HERE / "certificates"
TRANS = (0, 1, 4, 5, 13, 20)
DOUBLE = 6


def unit_basis(path: Path) -> bool:
    body = "".join(line for line in path.read_text().splitlines() if not line.startswith("#"))
    return re.sub(r"\s+", "", body).startswith("[1]")


def verify_chart(chart: int) -> dict:
    state = json.loads((CERT / f"search_p2_uc{chart}.json").read_text())
    assert state["exhaustive"] and not state["pending"]
    assert state["open_due_to_load"] == 0 and state["complete_nonunit_leaves"] == 0
    result_by_cases = {tuple(row["cases"]): row for row in state["results"]}
    core_path = CERT / "probes" / (
        f"p2_uc{chart}__s00_E_1__s01_E_1__s04_E_1__s05_E_1__s13_E_1__s20_E_1.gb"
    )
    assert unit_basis(core_path)
    checked_unit_files = 0
    for row in state["results"]:
        log = Path(row["log"]).read_text()
        assert "UNRESOLVED cap=" not in log and "EXIT code=0" in log
        if row["unit"]:
            assert unit_basis(Path(row["gb"]))
            checked_unit_files += 1
    leaves = 0
    core_prunes = 0
    for labels in itertools.product(("E_1", "N"), repeat=6):
        prefix = tuple(parse_case(2, f"{i}:{label}").key for i, label in zip(TRANS, labels))
        if labels == ("E_1",) * 6:
            core_prunes += 1
            continue
        row = result_by_cases[prefix]
        if row["unit"]:
            leaves += 1
            continue
        assert row["status"] == "NONUNIT"
        for label in ("E_1", "N"):
            child = prefix + (parse_case(2, f"{DOUBLE}:{label}").key,)
            assert result_by_cases[child]["unit"]
            leaves += 1
    return {
        "u_chart": chart,
        "runs": len(state["results"]),
        "statuses": dict(Counter(row["status"] for row in state["results"])),
        "unit_bases_checked": checked_unit_files,
        "known_core_basis_checked": str(core_path),
        "terminal_unit_leaves": leaves,
        "known_core_prunes": core_prunes,
        "max_seconds": max(row["seconds"] for row in state["results"]),
        "max_swap_used_mib_at_start": max(row["swap_used_mib_at_start"] for row in state["results"]),
    }


def verify_negative_control() -> dict:
    indices = (2, 3, 4, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21)
    cases = [parse_case(2, f"{i}:E_1") for i in indices]
    variables, generators = ideal(2, cases, 0)
    values = (1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 0, 1, 1)
    substitution = dict(zip(BASE_SYMBOLS, values)) | {ZU: 1}
    residues = [int(generator.subs(substitution)) % 2 for generator in generators]
    assert not any(residues)
    matches = list((CERT / "probes").glob("p2_uc0__s02_E_1__*s21_E_1.gb"))
    assert len(matches) == 1 and not unit_basis(matches[0])
    return {
        "cases": len(cases),
        "generators_evaluated": len(generators),
        "all_zero_at_explicit_gf2_point": True,
        "msolve_basis_is_nonunit": True,
    }


def main() -> None:
    report = {
        "characteristic": 2,
        "charts": [verify_chart(chart) for chart in (0, 1, 5)],
        "negative_control": verify_negative_control(),
        "symmetry_orbits_of_u_charts": {"same": [0], "one_common_row": [1, 2, 3, 4], "disjoint": [5]},
        "verified": True,
    }
    (HERE / "verification.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()

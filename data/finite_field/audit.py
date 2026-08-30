#!/usr/bin/env python3
"""Independent consistency audit and explicit-table exporter for K6-GC4EQ."""
from __future__ import annotations

import importlib.util
import json
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
CLASSIFIER = HERE / "classify.py"
PRIOR = HERE.parent / "k1695_r6_gc4r2"
spec = importlib.util.spec_from_file_location("gc4eq_classify", CLASSIFIER)
assert spec is not None and spec.loader is not None
c = importlib.util.module_from_spec(spec)
spec.loader.exec_module(c)


def field_order(label: str) -> int:
    return int(label[3:-1])


def flatten(matrix):
    return tuple(int(x) for row in matrix for x in row)


def field_integer(field, n: int) -> int:
    out = 0
    for _ in range(n):
        out = field.scalar.ADD[out][1]
    return out


def family_keys(q: int):
    field = c.scan.BatchField(q)
    scalar = c.canonical_full(c.IDENT, field)
    z = [0, 0, 1, field.scalar.NEG[1]]
    anti = (3, 2, 1, 0)
    two_support = tuple(
        field.scalar.ADD[int(i == anti[j])][field.scalar.MUL[z[i]][z[j]]]
        for i in range(4) for j in range(4)
    )
    keys = {
        scalar: "scalar-permutation",
        c.canonical_full(two_support, field): "two-support",
    }
    four = field_integer(field, 4)
    for gamma in range(q):
        omega = field.scalar.ADD[1][field.scalar.MUL[four][gamma]]
        omega3 = field.scalar.MUL[field.scalar.MUL[omega][omega]][omega]
        if omega != 1 and omega3 == 1:
            dense = tuple(field.scalar.ADD[int(i == j)][gamma] for i in range(4) for j in range(4))
            keys[c.canonical_full(dense, field)] = "dense-I+gamma-J"
    return keys


def good_text(good):
    pieces = []
    for item in good:
        perm = "".join(str(x + 1) for x in item["permutation"])
        ctype = "-".join(str(x) for x in item["cycle_type"])
        pieces.append(f"{perm}:{ctype}")
    return ";".join(pieces)


def matrix_text(matrix):
    return "/".join("".join(str(x) for x in row) for row in matrix)


def audit_result(name: str):
    path = HERE / f"result_{name}.json"
    data = json.loads(path.read_text())
    q = field_order(data["field"])
    field = c.scan.BatchField(q)
    allowed = family_keys(q)
    seen = set()
    class_counts = Counter()
    rank_counts = Counter()
    lines = ["id\tmatrix_rows\trank_A_minus_I\tfull_symmetry_family\tgood_permutations_and_cycle_types"]
    for index, record in enumerate(data["minimizers"], 1):
        matrix = flatten(record["matrix"])
        assert matrix not in seen
        seen.add(matrix)
        good = c.good_record(matrix, field)
        assert good == record["good"] and len(good) == 6
        rank = c.scan.matrix_rank_minus_identity(matrix, field)
        assert rank == record["rank_A_minus_I"]
        key = c.canonical_full(matrix, field)
        assert key in allowed, (name, record["matrix"], c.rows(key))
        family = allowed[key]
        class_counts[family] += 1
        rank_counts[rank] += 1
        lines.append(f"{index}\t{matrix_text(record['matrix'])}\t{rank}\t{family}\t{good_text(good)}")
    assert len(seen) == data["minimizer_count"]
    class_keys = {flatten(row["canonical_matrix"]) for row in data["full_symmetry_classes"]}
    assert class_keys == {c.canonical_full(m, field) for m in seen}
    table = HERE / f"{name.upper()}_MINIMIZERS.tsv"
    table.write_text("\n".join(lines) + "\n")
    return {
        "field": data["field"],
        "minimizers": len(seen),
        "rank_A_minus_I": dict(sorted(rank_counts.items())),
        "families": dict(sorted(class_counts.items())),
        "table": table.name,
    }


def main():
    expected = {
        "f2": (168, 2), "f3": (237, 2), "f4": (4, 2), "f5": (3, 1),
        "f7rank1": (45, 4), "f7rank2": (0, 0), "f9rank1": (17, 2),
    }
    rows = {}
    for name, (count, classes) in expected.items():
        data = json.loads((HERE / f"result_{name}.json").read_text())
        assert data["minimizer_count"] == count
        assert data["full_symmetry_class_count"] == classes
        rows[name] = audit_result(name)

    assert rows["f2"]["rank_A_minus_I"] == {0: 1, 1: 24, 2: 101, 3: 42}
    assert rows["f3"]["rank_A_minus_I"] == {0: 1, 1: 42, 2: 194}

    controls = json.loads((HERE / "result_controls.json").read_text())
    for key in ("aI", "I+2J", "I+J", "I+uuT"):
        assert controls[key]["g_primary"] == controls[key]["expected"]
        assert controls[key]["g_helper"] == controls[key]["expected"]
    for q in (2, 3, 4, 5, 7, 9):
        assert controls[f"two_support_GF{q}"]["g"] == 6

    f7r1 = json.loads((HERE / "result_f7rank1.json").read_text())
    f7r2 = json.loads((HERE / "result_f7rank2.json").read_text())
    assert f7r1["metadata"]["invertible_rank1_scanned"] + 1 + f7r2["metadata"]["invertible_matrices_scanned"] == 3_000_000
    assert f7r2["metadata"]["minimum_g"] == 10

    prior9 = json.loads((PRIOR / "result_f9.json").read_text())["result"]
    assert prior9["invertible_matrices_scanned"] == 1_000_000
    assert prior9["minimum_g"] == 12

    summary = {
        "status": "PASS",
        "all_recorded_equality_cases_in_conjectured_families": True,
        "controls": "PASS",
        "gf7_distinct_rank_le_2_tested": 3_000_000,
        "gf7_rank2_minimum_g": 10,
        "gf9_rank1_distinct_tested": 1_000_000,
        "gf9_prior_rank2_distinct_tested": 1_000_000,
        "gf9_prior_rank2_minimum_g": 12,
        "results": rows,
    }
    (HERE / "result_audit.json").write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print(json.dumps(summary, indent=2, sort_keys=True))
    print("DONE audit=PASS")


if __name__ == "__main__":
    main()

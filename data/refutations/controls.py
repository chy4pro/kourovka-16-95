#!/usr/bin/env python3
"""Mandatory primary controls for K6-U2CENSUS."""

from __future__ import annotations

from itertools import combinations
from pathlib import Path

from u2_core import classify, field_tables, named_matrix, swap_columns


TRANS6 = tuple(combinations(range(6), 2))
TRANS5 = tuple(combinations(range(5), 2))


def profile(space, matrix):
    pairs = TRANS6 if space.n == 6 else TRANS5
    return [space.kd(swap_columns(matrix, pair)) for pair in pairs]


def helper_field_crosscheck() -> None:
    source = Path("problems/k1695/round6_controllable.py").read_text(encoding="utf-8")
    namespace = {}
    stop = source.index(chr(112) + 'rint("ROUND 6-B')
    exec(compile(source[:stop], "round6_controllable_prefix", "exec"), namespace)
    helper_gf = namespace["GF"]
    for q in (2, 3, 4):
        add, mul, _, _ = field_tables(q)
        helper = helper_gf(q)
        assert add == helper.ADD
        assert mul == helper.MUL
        print(f"FIELD_CONTROL GF({q}) tables match round6_controllable helper")


def main() -> int:
    helper_field_crosscheck()

    space, matrix = named_matrix("M")
    expected_m = [3, 4, 4, 5, 4, 4, 4, 5, 4, 2, 5, 4, 3, 4, 3]
    assert space.rank(matrix) == 6
    assert space.kd(matrix) == 5
    assert profile(space, matrix) == expected_m
    neutral = [pair for pair, value in zip(TRANS6, expected_m) if value == 5]
    assert neutral == [(0, 4), (1, 4), (2, 4)]
    neighbour_nu = []
    for pair in neutral:
        neighbour = swap_columns(matrix, pair)
        neighbour_nu.append(sum(value == 5 for value in profile(space, neighbour)))
    assert neighbour_nu == [8, 4, 4]
    result = classify(space, matrix)
    assert result.local_maximum and not result.twostep_failure and not result.u2_failure
    print("M_CONTROL rank=6 kd=5 neutral=[(1,5),(2,5),(3,5)] neighbour_nu=[8,4,4]")
    print("M_PROFILE " + ",".join(map(str, expected_m)))

    space, matrix = named_matrix("C")
    expected_c = [3, 3, 4, 4, 3, 3, 3, 2, 2, 2]
    assert space.rank(matrix) == 5
    assert space.kd(matrix) == 4
    assert profile(space, matrix) == expected_c
    result = classify(space, matrix)
    assert result.local_maximum and result.twostep_failure
    assert not result.strict_local_maximum and not result.u2_failure
    escaped = swap_columns(swap_columns(matrix, (1, 2)), (1, 3))
    assert space.kd(escaped) == 5
    print("C_CONTROL rank=5 kd=4 2Step_failure=true U2_failure=false escape=(2,3),(2,4)")
    print("C_PROFILE " + ",".join(map(str, expected_c)))

    space, matrix = named_matrix("T")
    expected_t = [3, 3, 2, 3, 3, 2, 2, 3, 3, 2]
    assert space.rank(matrix) == 5
    assert space.kd(matrix) == 4
    assert profile(space, matrix) == expected_t
    result = classify(space, matrix)
    assert result.local_maximum and result.twostep_failure and result.strict_local_maximum
    assert not result.u2_failure
    escaped = swap_columns(swap_columns(matrix, (0, 1)), (0, 2))
    assert space.kd(escaped) == 5
    print("T_CONTROL rank=5 kd=4 strict=true 2Step_failure=true U2_failure=false escape=(1,2),(1,3)")
    print("T_PROFILE " + ",".join(map(str, expected_t)))
    print("CONTROLS_OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

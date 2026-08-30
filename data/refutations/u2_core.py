#!/usr/bin/env python3
"""Exact finite-field and radius-two routines for K6-U2CENSUS.

Vectors are base-q packed integers.  For GF(2) and GF(4), vector addition is
integer XOR; GF(3) uses a compact precomputed table.  No floating point is used.
"""

from __future__ import annotations

from array import array
from dataclasses import dataclass
from itertools import combinations


def field_tables(q: int):
    if q == 2:
        add = [[a ^ b for b in range(q)] for a in range(q)]
        mul = [[a & b for b in range(q)] for a in range(q)]
    elif q == 3:
        add = [[(a + b) % 3 for b in range(q)] for a in range(q)]
        mul = [[(a * b) % 3 for b in range(q)] for a in range(q)]
    elif q == 4:
        # 0,1,alpha,alpha+1 with alpha^2=alpha+1.
        add = [[a ^ b for b in range(q)] for a in range(q)]

        def mul4(a: int, b: int) -> int:
            raw = 0
            for i in range(2):
                if (a >> i) & 1:
                    raw ^= b << i
            if raw & 4:  # x^2 = x+1 modulo x^2+x+1
                raw ^= 0b111
            return raw

        mul = [[mul4(a, b) for b in range(q)] for a in range(q)]
    else:
        raise ValueError("supported fields are GF(2), GF(3), and GF(4)")
    neg = [next(b for b in range(q) if add[a][b] == 0) for a in range(q)]
    inv = [0] + [next(b for b in range(1, q) if mul[a][b] == 1) for a in range(1, q)]
    return add, mul, neg, inv


class PackedSpace:
    def __init__(self, q: int, n: int):
        self.q = q
        self.n = n
        self.size = q ** n
        self.add_scalar, self.mul_scalar, self.neg, self.inv = field_tables(q)
        self.powers = tuple(q ** i for i in range(n))
        self.digits = tuple(self.decode_raw(code) for code in range(self.size))
        self.pivot = tuple(
            max((i for i, value in enumerate(ds) if value), default=-1)
            for ds in self.digits
        )
        self.scale = tuple(
            tuple(self.encode(self.mul_scalar[a][x] for x in ds) for ds in self.digits)
            for a in range(q)
        )
        self._add3 = None
        if q == 3:
            table = array("H", [0]) * (self.size * self.size)
            for a, da in enumerate(self.digits):
                offset = a * self.size
                for b, db in enumerate(self.digits):
                    table[offset + b] = self.encode((da[i] + db[i]) % 3 for i in range(n))
            self._add3 = table

    def decode_raw(self, code: int) -> tuple[int, ...]:
        digits = []
        for _ in range(self.n):
            digits.append(code % self.q)
            code //= self.q
        return tuple(digits)

    def encode(self, digits) -> int:
        return sum(value * self.powers[i] for i, value in enumerate(digits))

    def add(self, a: int, b: int) -> int:
        if self.q in (2, 4):
            return a ^ b
        return self._add3[a * self.size + b]

    def insert(self, basis: list[int], vector: int) -> bool:
        while vector:
            pivot = self.pivot[vector]
            coefficient = self.digits[vector][pivot]
            if basis[pivot]:
                multiple = self.scale[self.neg[coefficient]][basis[pivot]]
                vector = self.add(vector, multiple)
            else:
                basis[pivot] = self.scale[self.inv[coefficient]][vector]
                return True
        return False

    def rank(self, vectors) -> int:
        basis = [0] * self.n
        return sum(self.insert(basis, vector) for vector in vectors)

    def matvec(self, columns: tuple[int, ...], vector: int) -> int:
        if self.q == 2:
            result = 0
            while vector:
                bit = vector & -vector
                result ^= columns[bit.bit_length() - 1]
                vector ^= bit
            return result
        result = 0
        for j, coefficient in enumerate(self.digits[vector]):
            if coefficient:
                result = self.add(result, self.scale[coefficient][columns[j]])
        return result

    def kd(self, columns: tuple[int, ...], point: int = 0) -> int:
        basis = [0] * self.n
        vector = self.powers[point]
        for dimension in range(self.n):
            if not self.insert(basis, vector):
                return dimension
            vector = self.matvec(columns, vector)
        return self.n

    def identity_columns(self) -> tuple[int, ...]:
        return self.powers

    def matrix_from_rows(self, rows) -> tuple[int, ...]:
        if len(rows) != self.n or any(len(row) != self.n for row in rows):
            raise ValueError("matrix shape does not match packed space")
        return tuple(self.encode(rows[i][j] for i in range(self.n)) for j in range(self.n))

    def rows_from_matrix(self, columns: tuple[int, ...]) -> list[list[int]]:
        return [[self.digits[columns[j]][i] for j in range(self.n)] for i in range(self.n)]


def swap_columns(columns: tuple[int, ...], transposition: tuple[int, int]) -> tuple[int, ...]:
    left, right = transposition
    result = list(columns)
    result[left], result[right] = result[right], result[left]
    return tuple(result)


def permute_columns(columns: tuple[int, ...], permutation: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(columns[permutation[j]] for j in range(len(columns)))


def compose_permutations(left: tuple[int, ...], right: tuple[int, ...]) -> tuple[int, ...]:
    """Column convention: applying left and then right gives left[right[j]]."""
    return tuple(left[right[j]] for j in range(len(left)))


def transposition_permutation(n: int, pair: tuple[int, int]) -> tuple[int, ...]:
    result = list(range(n))
    result[pair[0]], result[pair[1]] = result[pair[1]], result[pair[0]]
    return tuple(result)


def radius2_profile(space: PackedSpace, columns: tuple[int, ...]) -> list[dict]:
    """The full set-valued radius <=2 profile, one row per resulting permutation."""
    n = space.n
    pairs = tuple(combinations(range(n), 2))
    identity = tuple(range(n))
    permutations = {identity: 0}
    trans = [(pair, transposition_permutation(n, pair)) for pair in pairs]
    for _, permutation in trans:
        permutations[permutation] = 1
    for _, first in trans:
        for _, second in trans:
            product = compose_permutations(first, second)
            permutations[product] = min(permutations.get(product, 3), 2)
    return [
        {
            "distance": distance,
            "permutation": [value + 1 for value in permutation],
            "kd": space.kd(permute_columns(columns, permutation)),
        }
        for permutation, distance in sorted(permutations.items(), key=lambda item: (item[1], item[0]))
    ]


@dataclass
class Classification:
    kd: int
    local_maximum: bool = False
    twostep_failure: bool = False
    strict_local_maximum: bool = False
    u2_failure: bool = False
    one_step_profile: tuple[int, ...] = ()


def classify(space: PackedSpace, columns: tuple[int, ...]) -> Classification:
    """Classify a state; U2 and local maxima concern only kd<n states."""
    n = space.n
    k = space.kd(columns)
    if k == n:
        return Classification(kd=k)
    pairs = tuple(combinations(range(n), 2))
    neighbours: list[tuple[tuple[int, ...], int]] = []
    profile = []
    for pair in pairs:
        neighbour = swap_columns(columns, pair)
        value = space.kd(neighbour)
        profile.append(value)
        if value > k:
            return Classification(kd=k, one_step_profile=tuple(profile))
        neighbours.append((neighbour, value))

    strict = all(value < k for _, value in neighbours)
    u2_escape = False
    neutral_then_escape = False
    for neighbour, first_value in neighbours:
        need_this_branch = not u2_escape or (first_value == k and not neutral_then_escape)
        if not need_this_branch:
            continue
        for second_pair in pairs:
            second_value = space.kd(swap_columns(neighbour, second_pair))
            if second_value > k:
                u2_escape = True
                if first_value == k:
                    neutral_then_escape = True
                break
    return Classification(
        kd=k,
        local_maximum=True,
        twostep_failure=not neutral_then_escape,
        strict_local_maximum=strict,
        u2_failure=not u2_escape,
        one_step_profile=tuple(profile),
    )


M_ROWS = (
    (0, 0, 0, 1, 0, 0),
    (1, 0, 0, 0, 0, 0),
    (1, 1, 1, 1, 0, 1),
    (0, 0, 1, 0, 0, 0),
    (1, 0, 1, 1, 1, 0),
    (0, 0, 0, 0, 0, 1),
)

C_ROWS = (
    (0, 0, 0, 0, 1),
    (0, 1, 0, 0, 0),
    (1, 0, 0, 0, 0),
    (2, 1, 3, 1, 0),
    (3, 3, 3, 0, 2),
)

T_ROWS = (
    (0, 0, 0, 1, 0),
    (3, 3, 2, 2, 3),
    (0, 0, 1, 0, 0),
    (1, 0, 1, 2, 0),
    (2, 2, 2, 3, 1),
)


def named_matrix(name: str) -> tuple[PackedSpace, tuple[int, ...]]:
    if name == "M":
        space = PackedSpace(2, 6)
        return space, space.matrix_from_rows(M_ROWS)
    if name == "C":
        space = PackedSpace(4, 5)
        return space, space.matrix_from_rows(C_ROWS)
    if name == "T":
        space = PackedSpace(4, 5)
        return space, space.matrix_from_rows(T_ROWS)
    raise ValueError(f"unknown named matrix {name!r}")

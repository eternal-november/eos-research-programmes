#!/usr/bin/env python3
"""Exact finite regression tests, not a formal proof of the family theorem."""
from __future__ import annotations
from collections import defaultdict
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json


def T(xs):
    xs = tuple(xs)
    return tuple((x,) for x in xs) + tuple(product(xs, repeat=2))


def mu(rows):
    return tuple(x for row in rows for x in row)[:2]


def dist(items):
    total = defaultdict(F)
    for x, p in items:
        total[x] += p
    return tuple(sorted((x, p) for x, p in total.items() if p))


def pure(x):
    return ((x, F(1)),)


def dmap(f, p):
    return dist((f(x), w) for x, w in p)


def dmu(pp):
    return dist((x, a * b) for p, a in pp for x, b in p)


def sequence(ps):
    out = pure(())
    for p in ps:
        out = dist((xs + (x,), a * b) for xs, a in out for x, b in p)
    return out


def main():
    B = (0, 1)
    TB, TTB = T(B), T(T(B))
    TTTB = T(TTB)
    for w in TB:
        assert mu((w,)) == w
        assert mu(tuple((x,) for x in w)) == w
    for w in TTTB:
        assert mu(mu(w)) == mu(tuple(mu(row) for row in w))

    ps = (pure(0), pure(1), dist(((0, F(1, 2)), (1, F(1, 2)))))
    tps = T(ps)
    for p in ps:
        assert sequence((p,)) == dmap(lambda x: (x,), p)
    for w in TB:
        assert sequence(tuple(pure(x) for x in w)) == pure(w)
    for rows in T(tps):
        assert sequence(mu(rows)) == dmap(mu, sequence(tuple(sequence(row) for row in rows)))
    pps = tuple(dist(((ps[i], F(1, 2)), (ps[j], F(1, 2)))) for i in range(3) for j in range(i, 3))
    for w in T(pps):
        assert sequence(tuple(dmu(p) for p in w)) == dmu(dmap(sequence, sequence(w)))
    for images in product(B, repeat=2):
        for w in tps:
            assert sequence(tuple(dmap(lambda x: images[x], p) for p in w)) == dmap(lambda xs: tuple(images[x] for x in xs), sequence(w))

    source = tuple(product(B, repeat=4))
    marginal = dist(((xs[0], xs[1]), F(1, 16)) for xs in source)
    assert len(source) == 16 and len(marginal) == 4
    assert all(p == F(1, 4) for _, p in marginal)
    a, b = ((0, 0), (0, 0)), ((0, 0), (1, 1))
    assert a != b and mu(a) == mu(b)
    constant_image = lambda z: tuple(tuple(0 for _ in row) for row in z)
    assert constant_image(a) == constant_image(b)

    # A prior fair bit chooses binary a0 or unary c. The unused a1 has the
    # same binary label as a0 and remains in the full receipt grade.
    binary = tuple(product(range(2), range(4)))
    unary = tuple((x,) for x in range(4))
    history = [((0,) + xs, F(1, 16)) for xs in binary] + [((1,) + xs, F(1, 8)) for xs in unary]
    def history_map(xs):
        return (0, xs[1], xs[2] % 2) if xs[0] == 0 else (1, xs[1] % 2)
    pushed = dist((history_map(xs), p) for xs, p in history)
    assert len(history) == 12 and len(pushed) == 6
    assert sum(p for _, p in history) == sum(p for _, p in pushed) == 1
    assert all(p == (F(1, 8) if xs[0] == 0 else F(1, 4)) for xs, p in pushed)
    source_receipts = tuple((tag, xs) for tag in ("a0", "a1") for xs in binary) + tuple(("c", xs) for xs in unary)
    def receipt_map(r):
        tag, xs = r
        return ("m", (xs[0], xs[1] % 2)) if tag in ("a0", "a1") else ("n", (xs[0] % 2,))
    target_receipts = set(map(receipt_map, source_receipts))
    assert len(source_receipts) == 20 and len(target_receipts) == 6
    assert sum(tag == "a1" for tag, _ in source_receipts) == 8

    return {
        "status": "passed",
        "scope": "finite exact regression only; not a proof of universal law or coherence",
        "prefix_two_monad": {"base_cardinality": 2, "TB": len(TB), "TTB": len(TTB), "TTTB_associativity_cases": len(TTTB), "unit_cases_each": len(TB)},
        "ordinary_traversal": {"T_unit_cases": len(ps), "D_unit_cases": len(TB), "T_multiplication_cases": len(T(tps)), "D_multiplication_cases": len(T(pps)), "naturality_cases": 4 * len(tps)},
        "noncartesian_multiplication": {"distinct_witnesses": [a, b], "same_flattening": mu(a), "same_constant_base_image": True},
        "retained_projection": {"source_cardinality": 16, "target_cardinality": 4, "target_mass_each": "1/4", "invertible": False},
        "indexed_dependent_cell": {"source_histories": 12, "target_histories": 6, "source_binary_mass_each": "1/16", "source_unary_mass_each": "1/8", "target_binary_mass_each": "1/8", "target_unary_mass_each": "1/4", "full_source_receipts": 20, "full_target_receipts": 6, "unreachable_source_receipts_retained": 8},
    }


if __name__ == "__main__":
    result = main()
    output = json.dumps(result, indent=2) + "\n"
    Path(__file__).with_name("indexed_boundary_examples_results.json").write_text(output, encoding="utf-8")
    print(output, end="")

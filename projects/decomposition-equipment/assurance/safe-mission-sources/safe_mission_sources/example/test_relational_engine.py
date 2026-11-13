#!/usr/bin/env python3
"""Independent small-world checks for relational_engine (standard unittest).

The brute-force oracle below is test-only; the production engine does not
construct a joint world catalogue.
"""
import itertools
import json
from pathlib import Path
import random
import unittest
from relational_engine import Catalogue, ForestKnowledge, CycleError, iter_ids


def brute_worlds(cat, outputs, coords, sums):
    worlds = []
    contexts = {tuple(c) for _, c, _ in coords} | {tuple(c) for _, _, c, _ in sums}
    predictions = {c: [cat.evaluate(h, c) for h in range(cat.size)] for c in contexts}
    for world in itertools.product(range(cat.size), repeat=outputs):
        if all(predictions[tuple(c)][world[i]] == bit for i, c, bit in coords) and all(
            predictions[tuple(c)][world[i]] + predictions[tuple(c)][world[j]] == s
            for i, j, c, s in sums):
            worlds.append(world)
    return worlds


class TestCatalogue(unittest.TestCase):
    def test_counts_and_unique_functions(self):
        for n, L in [(1, 1), (2, 1), (2, 2), (3, 2)]:
            c = Catalogue(n, L)
            expected = 2 + 2*n*L + 10*(n*(n-1)//2)*L*L
            self.assertEqual(c.size, expected)
            contexts = list(itertools.product(range(L+1), repeat=n))
            signatures = {tuple(c.evaluate(h, x) for x in contexts) for h in range(c.size)}
            self.assertEqual(len(signatures), c.size)

    def test_find_and_eval_against_scalar(self):
        c = Catalogue(3, 3)
        for h in range(c.size):
            d = c.describe(h)
            self.assertEqual(c.find(d['features'], d['table']), h)
            for x in itertools.product(range(4), repeat=3):
                bits = [int(x[p] >= r) for p, r in d['features']]
                index = sum(v << k for k, v in enumerate(bits))
                expected = (d['table'] >> index) & 1
                self.assertEqual(c.evaluate(h, x), expected)

    def test_invalid_inputs(self):
        c = Catalogue(2, 2)
        for x in [(0,), (0, 3), (-1, 0), (0, 1.5)]:
            with self.assertRaises(ValueError):
                c.prediction_mask(x)
        with self.assertRaises(ValueError):
            c.find([(0, 1), (1, 1)], 3)  # table ignores first variable


class TestForestKnowledge(unittest.TestCase):
    def compare(self, k, coords, sums):
        c = k.catalogue
        worlds = brute_worlds(c, k.n_outputs, coords, sums)
        self.assertEqual(k.consistent(), bool(worlds))
        if worlds:
            for i in range(k.n_outputs):
                expected = set(w[i] for w in worlds)
                self.assertEqual(set(iter_ids(k.domains[i])), expected)
        contexts = list(itertools.product(range(c.L+1), repeat=c.n_ports))
        for x in contexts:
            for i in range(k.n_outputs):
                expected = tuple(sorted(set(c.evaluate(w[i], x) for w in worlds)))
                self.assertEqual(k.possible_coordinate(i, x), expected)
            for i, j in itertools.combinations(range(k.n_outputs), 2):
                expected = tuple(sorted(set(c.evaluate(w[i], x)+c.evaluate(w[j], x) for w in worlds)))
                self.assertEqual(k.possible_sum(i, j, x), expected)
        return worlds

    def test_random_tree_evidence_against_full_worlds(self):
        c = Catalogue(2, 1)  # all 16 two-bit truth functions
        rng = random.Random(20261029)
        for trial in range(8):
            truth = tuple(rng.randrange(c.size) for _ in range(3))
            k = ForestKnowledge(c, 3)
            coords, sums = [], []
            for step in range(8):
                x = tuple(rng.randrange(2) for _ in range(2))
                if step % 3 == 0:
                    i = rng.randrange(3)
                    y = c.evaluate(truth[i], x)
                    coords.append((i, x, y))
                    self.assertTrue(k.observe_coordinate(i, x, y))
                else:
                    i, j = ((0, 1) if step % 2 else (1, 2))
                    y = c.evaluate(truth[i], x) + c.evaluate(truth[j], x)
                    sums.append((i, j, x, y))
                    self.assertTrue(k.observe_sum(i, j, x, y))
                self.compare(k, coords, sums)

    def test_persistent_function_not_resampled(self):
        c = Catalogue(2, 1)
        k = ForestKnowledge(c, 2)
        for x in itertools.product(range(2), repeat=2):
            self.assertTrue(k.observe_sum(0, 1, x, 1))
        worlds = brute_worlds(c, 2, [], [(0, 1, x, 1) for x in itertools.product(range(2), repeat=2)])
        self.assertEqual(len(worlds), 16)
        self.assertEqual([d.bit_count() for d in k.domains], [16, 16])
        self.assertFalse(k.feasible([(0, (0, 0), 0), (1, (0, 0), 0)]))
        self.assertFalse(k.feasible([(0, (0, 0), 1), (0, (0, 0), 0)]))
        self.assertEqual(k.possible_vectors([(0, (1, 0)), (1, (1, 0))]), ((0, 1), (1, 0)))
        branch = k.copy()
        self.assertTrue(branch.observe_coordinate(0, (1, 0), 0))
        self.assertTrue(branch.guarantees([(1, (1, 0), 1)]))
        self.assertFalse(k.guarantees([(1, (1, 0), 1)]))

    def test_cycle_rejected_without_mutation(self):
        c = Catalogue(2, 1)
        k = ForestKnowledge(c, 3)
        k.observe_sum(0, 1, (0, 0), 1)
        k.observe_sum(1, 2, (0, 0), 1)
        prior = k.metrics()
        with self.assertRaises(CycleError):
            k.observe_sum(0, 2, (0, 0), 1)
        self.assertEqual(prior, k.metrics())
        self.assertTrue(k.observe_sum(1, 0, (1, 1), 0))  # existing edge allowed

    def test_inconsistency_no_vacuous_safety(self):
        c = Catalogue(2, 1)
        k = ForestKnowledge(c, 2)
        self.assertTrue(k.observe_sum(0, 1, (0, 0), 0))
        self.assertFalse(k.observe_coordinate(0, (0, 0), 1))
        self.assertFalse(k.consistent())
        self.assertFalse(k.guarantees([]))
        self.assertFalse(k.feasible([]))
        self.assertEqual(k.possible_sum(0, 1, (1, 1)), ())

    def test_discovered_memory_caps(self):
        c = Catalogue(3, 3)
        k = ForestKnowledge(c, 1)
        target = c.find([(0, 2), (2, 1)], 6)  # XOR
        for x in itertools.product(range(4), repeat=3):
            k.observe_coordinate(0, x, c.evaluate(target, x))
        report = k.discovered_interface(0)
        self.assertTrue(report['unique_response'])
        self.assertEqual(report['ports'], [0, 2])
        self.assertEqual(report['counter_caps'], [2, 0, 1])
        # Capping at the discovered maxima preserves updates and responses.
        caps = report['counter_caps']
        for old in itertools.product(range(4), repeat=3):
            for action in itertools.product((0, 1), repeat=3):
                full = tuple(min(3, r+1) if a else 0 for r, a in zip(old, action))
                compressed = tuple(min(cap, min(cap, r)+1) if a else 0
                                   for r, a, cap in zip(old, action, caps))
                self.assertEqual(c.evaluate(target, full), c.evaluate(target, compressed))


if __name__ == '__main__':
    unittest.main(verbosity=2)

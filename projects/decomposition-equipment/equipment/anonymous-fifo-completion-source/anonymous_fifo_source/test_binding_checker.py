import itertools
import random
import unittest
from fractions import Fraction
from binding_checker import check, from_windows, verify_positive


def brute(edges, roles, bits):
    outputs = set()
    for m in itertools.permutations(range(len(roles))):
        if all(v in edges[i] for i, v in enumerate(m)):
            out = [0] * (max(roles, default=-1) + 1)
            for i, v in enumerate(m):
                out[roles[i]] ^= bits[v]
            outputs.add(tuple(out))
    return 'NO_GRAPH_MATCHING' if not outputs else 'CERTIFIED' if len(outputs) == 1 else 'UNRESOLVED'


class Tests(unittest.TestCase):
    def test_cases(self):
        self.assertEqual(check([[0, 1], [0, 1]], ['A', 'A'], [0, 1])['status'], 'CERTIFIED')
        self.assertEqual(check([[0, 1], [0, 1]], ['A', 'B'], [1, 1])['status'], 'CERTIFIED')
        result = check([[0, 1], [0, 1]], ['A', 'B'], [0, 1])
        self.assertEqual(result['status'], 'UNRESOLVED')
        self.assertNotEqual(result['parity_mask'], result['other_parity_mask'])
        # Only identity and a single 4-cycle; cross-role unequal-payload ambiguity cancels.
        self.assertEqual(check([[0, 3], [1, 0], [2, 1], [3, 2]], ['A','B','A','B'], [1,1,0,0])['status'], 'CERTIFIED')
        # Cross-SCC edge 0 -> 1 cannot belong to any perfect matching.
        self.assertEqual(check([[0], [0, 1]], ['A', 'B'], [1, 0])['status'], 'CERTIFIED')
        self.assertEqual(check([[0], [0]], ['A', 'B'], [0,1])['status'], 'NO_GRAPH_MATCHING')
        self.assertEqual(check([], [], [])['status'], 'CERTIFIED')

    def test_certificate_verifier(self):
        edges, roles, bits = [[0, 1], [0, 1]], [0, 1], [1, 1]
        cert = check(edges, roles, bits)
        self.assertTrue(verify_positive(edges, roles, bits, cert))
        cert["potentials"][1] ^= 1
        self.assertFalse(verify_positive(edges, roles, bits, cert))

    def test_raw_ties_exact(self):
        self.assertEqual(from_windows([(Fraction(1,3), Fraction(1,3))]*2,
                                     [Fraction(1,3)]*2, ['A','A'], [0,1])['status'], 'CERTIFIED')

    def test_exhaustive_n3(self):
        n = 3
        for graph in range(1 << (n*n)):
            edges = [[v for v in range(n) if graph & (1 << (i*n+v))] for i in range(n)]
            for roles in itertools.product(range(2), repeat=n):
                for bits in itertools.product(range(2), repeat=n):
                    self.assertEqual(check(edges, roles, bits)['status'], brute(edges, roles, bits))

    def test_seeded_n4_to_n7(self):
        rng = random.Random(1729)
        for n in range(4, 8):
            for _ in range(100):
                edges = [[v for v in range(n) if rng.random() < .5] for i in range(n)]
                roles = [rng.randrange(3) for _ in range(n)]
                bits = [rng.randrange(2) for _ in range(n)]
                self.assertEqual(check(edges, roles, bits)['status'], brute(edges, roles, bits))

if __name__ == '__main__':
    unittest.main()

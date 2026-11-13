"""Deterministic tiny sanity tests; not mission/outcome experiments."""
import itertools
import math
import unittest
from fractions import Fraction
from unittest.mock import patch
from rehearsal_cache import CachedLinearEvidence


class CacheTests(unittest.TestCase):
    def test_recombines_equations_multiple_outputs(self):
        c = CachedLinearEvidence(3, 2, 0, 2)
        c.add_rows([[1, 1, 0], [0, 1, 0]], [[3, 4], [1, 0]])
        self.assertEqual(c.infer_vector([1, 0, 0]), (Fraction(2), Fraction(4)))
        self.assertIsNone(c.infer_vector([0, 0, 1]))
        self.assertIsNone(c.get_fully_identified_operator())
        c.add_rows([[0, 0, 1]], [[0, 1]])
        self.assertEqual(c.get_fully_identified_operator(), ((2, 1, 0), (4, 0, 1)))

    def test_exact_fraction_elimination(self):
        c = CachedLinearEvidence(3, 1, 0, 3)
        c.add_rows([[1, 1, 0], [1, 0, 1], [0, 1, 1]], [[3], [4], [5]])
        self.assertEqual(c.infer_vector([1, 0, 0]), (1,))
        self.assertEqual(c.get_fully_identified_operator(), ((1, 2, 3),))

    def test_zero_evidence_tightens_unseen_vector(self):
        c = CachedLinearEvidence(2, 1, 0, 1)
        c.add_rows([[1, 1]], [[0]])
        self.assertIsNone(c.infer_vector([1, 0]))
        self.assertEqual(c.bound_vector([1, 0], 0)['upper'], 0)

    def test_exact_certificates_cover_all_tiny_feasible_models(self):
        c = CachedLinearEvidence(3, 1, 0, 1)
        c.add_rows([[1, 1, 0]], [[2]])
        for a in ((1, 0, 1), (-1, 2, 1), (0, 0, 1), (1, 1, 0)):
            bound = c.bound_vector(a, 0)
            cert = bound['certificate']
            y, lam = cert['y'], cert['lambda_']
            residual = [Fraction(a[j])-sum(y[k]*c.A[k][j] for k in range(len(c.A)))-lam for j in range(c.d)]
            exact = sum(y[k]*c.b[k][0] for k in range(len(c.A)))+lam*4+4*sum(max(0, r) for r in residual)
            self.assertGreaterEqual(lam, 0)
            self.assertEqual(cert['exact_upper'], exact)
            self.assertEqual(bound['upper'], math.floor(exact))
            for g in itertools.product(range(5), repeat=3):
                # Check the entire integer sum-budget relaxation, not only sparse g.
                if sum(g) <= 4 and g[0]+g[1] == 2:
                    self.assertLessEqual(sum(x*z for x, z in zip(a, g)), bound['upper'])
            self.assertIsNone(bound['witness'])

    def test_solver_failure_is_not_unsat(self):
        c = CachedLinearEvidence(2, 1, 0, 1)
        with patch('scipy.optimize.linprog', side_effect=RuntimeError('synthetic failure')):
            result = c.bound_vector([1, 1], 0)
        self.assertEqual(result['upper'], 4)
        self.assertIn('failed', result['solver_status'])
        self.assertIsNone(result['witness'])

    def test_arbitrary_inexact_multipliers_still_certify(self):
        c = CachedLinearEvidence(2, 1, 0, 1)
        c.add_rows([[1, 1]], [[3]])
        cert = c._certificate([1, 0], 0, [Fraction(31, 29)], Fraction(1, 7))
        for g in ((3, 0), (0, 3)):
            self.assertLessEqual(g[0], math.floor(cert['exact_upper']))

    def test_atomic_inconsistent_and_malformed_rows(self):
        c = CachedLinearEvidence(2, 1, 0, 1)
        c.add_rows([[1, 0]], [[2]])
        with self.assertRaises(ValueError):
            c.add_rows([[0, 1], [1, 0]], [[3], [4]])
        self.assertEqual(c.stats['rank'], 1)
        self.assertEqual(len(c.A), 1)
        with self.assertRaises(ValueError):
            c.add_rows([[2, 0]], [[2]])
        with self.assertRaises(ValueError):
            c.add_rows([[0, 0]], [[1]])
        with self.assertRaises(ValueError):
            c.bound_vector([0.5, 0], 0)
        self.assertEqual(c.infer_vector([0, 0]), (0,))

    def test_empty_evidence_zero_budget_lags(self):
        c = CachedLinearEvidence(2, 2, 1, 0)
        self.assertEqual(c.d, 4)
        c.add_rows([], [])
        self.assertEqual(c.bound_vector([1, 0, 1, 0], 1)['upper'], 0)
        self.assertEqual(c.infer_vector([0, 0, 0, 0]), (0, 0))


if __name__ == '__main__':
    unittest.main()

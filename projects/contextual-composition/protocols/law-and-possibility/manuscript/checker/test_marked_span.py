import itertools
import json
import unittest
from fractions import Fraction
from pathlib import Path

from marked_span import inputs, solve, sparsify, verify


def example(name):
    return json.loads((Path(__file__).parent / "examples" / (name + ".json")).read_text())


class MarkedSpan(unittest.TestCase):
    def test_coverage_only(self):
        d = example("coverage_failure")
        a = solve(d)
        self.assertEqual(a, {"ok": False, "uncovered_candidate": ["high"], "deficient_cut": None})
        self.assertTrue(verify(d, a))

    def test_cut_only(self):
        d = example("mass_failure")
        a = solve(d)
        self.assertEqual(a, {"ok": False, "uncovered_candidate": [], "deficient_cut": {
            "candidate_subset": ["expensive"], "neighbors": ["dear"],
            "candidate_mass": "3/4", "reference_mass": "1/2"}})
        self.assertTrue(verify(d, a))
        a["deficient_cut"]["reference_mass"] = "1/4"
        self.assertFalse(verify(d, a))

    def test_duplicate_rows_and_zero_zero_filler(self):
        d = example("covered")
        a = solve(d)
        self.assertTrue(a["ok"])
        self.assertTrue(verify(d, a))
        self.assertEqual(len(a["span"]), 4)
        self.assertEqual({x["candidate"] for x in a["span"] if x["mass"] == "0"},
                         {"low_copy", "high"})
        self.assertIn({"candidate": "high", "reference": "high_only",
                       "mass": "0", "cost": ["10"]}, a["span"])
        a["span"] = [x for x in a["span"] if x["candidate"] != "low_copy"]
        self.assertFalse(verify(d, a))

    def test_unmatched_zero_reference_permitted(self):
        d = example("covered")
        d["reference"].append({"id": "unused", "cost": [0], "mass": 0})
        self.assertTrue(solve(d)["ok"])

    def test_cycle(self):
        flow = {(i, j): Fraction(1, 4) for i in "ab" for j in "xy"}
        self.assertEqual(len(sparsify(flow)), 2)
        self.assertEqual(sum(flow.values()), 1)
        for key in "abxy":
            self.assertEqual(sum(w for pair, w in flow.items() if key in pair), Fraction(1, 2))

    def test_all_two_by_two_relations_and_quarter_masses(self):
        edges = list(itertools.product("ab", "xy"))
        for bits, p, q in itertools.product(itertools.product((0, 1), repeat=4), range(5), range(5)):
            d = {"candidate": [{"id": i, "cost": [], "mass": str(Fraction(w, 4))}
                               for i, w in zip("ab", (p, 4-p))],
                 "reference": [{"id": j, "cost": [], "mass": str(Fraction(w, 4))}
                               for j, w in zip("xy", (q, 4-q))],
                 "allowed": [e for e, bit in zip(edges, bits) if bit]}
            P, Q, R = inputs(d)
            cut = any(sum(P[i][0] for i in A) >
                      sum(Q[j][0] for j in {j for i, j in R if i in A})
                      for A in ({"a"}, {"b"}, {"a", "b"}))
            covered = all(any(ii == i for ii, _ in R) for i in P)
            a = solve(d)
            self.assertEqual(a["ok"], covered and not cut)
            self.assertTrue(verify(d, a))
            if a["ok"]:
                self.assertLessEqual(len(a["span"]), len(P) + sum(q > 0 for q, _ in Q.values()) - 1)

    def test_not_a_subprobability_or_float_checker(self):
        d = example("covered")
        d["candidate"][0]["mass"] = 0
        with self.assertRaises(ValueError):
            solve(d)
        d["candidate"][0]["mass"] = 1.0
        with self.assertRaises(ValueError):
            solve(d)


if __name__ == "__main__":
    unittest.main()

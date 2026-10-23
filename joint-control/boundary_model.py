"""Exact arithmetic cross-checks for named boundary derivations.

This does not enumerate all policies or prove the prose source interpretation.
The parametric derivations in BOUNDARIES.md are the primary proof objects.
"""
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from pathlib import Path
import argparse
import json

HERE = Path(__file__).resolve().parent


def step(x, a, c, delta, effect):
    return (x[0] + delta * (a*x[0] + c*x[1] + effect[0]),
            x[1] + delta * (c*x[0] + a*x[1] + effect[1]))


def check():
    identities = 0
    # Enumerated rational cases check signs and source normalization, not an
    # empirical sampling claim or a universal proof inferred from the cases.
    for a, c, delta, r, e0, e1 in product(
        (F(45, 1000), F(55, 1000)),
        (F(45, 1000), F(55, 1000)),
        (F(1, 1000), F(1)),
        (F(1, 4), F(1, 2)),
        (F(-2), F(0), F(2)),
        (F(-2), F(0), F(2)),
    ):
        xp = step((r, -r), a, c, delta, (e0, e1))
        xm = step((-r, r), a, c, delta, (e0, e1))
        lam = 1 + delta*(a-c)
        assert xp[0]-xm[0] == 2*r*lam
        assert xp[1]-xm[1] == -2*r*lam
        assert sum(xp) == sum(xm)
        identities += 1

    # An exact finite losing separation at an allowed large-delay parameter.
    r, eps, t = F(1, 2), F(1, 100), 70
    assert r*(1+eps)**t > 1
    # Slow source: Bernoulli's proved lower bound already exceeds K's diameter.
    slow_eps, slow_t = F(1, 100000), 100001
    assert r*(1+slow_t*slow_eps) > 1

    # Check source input normalization in the authority lower bound for every
    # integer support size in these populations, at extremal actual outputs.
    capacity_cases = 0
    for n in range(5, 20):
        for bad in range(n+1):
            adverse = [-F(2)]*bad
            strongest_defence = [F(2)]*(n-bad)
            outward = -sum(adverse + strongest_defence)/n
            assert outward == F(4*bad, n)-2
            if 2*bad >= n:
                assert outward >= 0
            capacity_cases += 1

    # Passive partial views in general do not imply control impossibility:
    # two different local rows support decentralized diagonal feedback here.
    closed = ((F(9, 10), F(1, 20)), (F(1, 20), F(9, 10)))
    assert max(sum(abs(v) for v in row) for row in closed) == F(19, 20)

    # Summation of a shared stock law; capped replenishment cannot defeat it.
    e0, supply, service_cost, periods = F(10), F(1), F(2), 11
    assert periods*service_cost > e0 + periods*supply

    sources = {name: sha256((HERE/name).read_bytes().replace(b"\r\n", b"\n")).hexdigest()
               for name in ("BOUNDARIES.md", "boundary_model.py", "SOURCE.md")}
    return {
        "scope": "Exact arithmetic checks accompanying parametric prose proofs; independent semantic review pending",
        "paired_step_cases": identities,
        "finite_exact_separation": {"r": "1/2", "epsilon": "1/100", "tick": t},
        "bernoulli_slow_source_bound": {"epsilon": "1/100000", "tick": slow_t},
        "influence_normalization_cases": capacity_cases,
        "rank_one_blanket_claim_countercertificate": "closed-loop infinity norm 19/20",
        "resource_exhaustion_ticks": periods,
        "sources_sha256_lf": sources,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    result = check()
    output = HERE/"boundary_results.json"
    rendered = json.dumps(result, indent=2, sort_keys=True)+"\n"
    if args.write:
        output.write_text(rendered, encoding="utf-8", newline="\n")
    else:
        assert output.read_text(encoding="utf-8") == rendered, "Source/result mismatch"
    print("PASS: exact boundary arithmetic; universal/source claims require their proofs and review")


if __name__ == "__main__":
    main()

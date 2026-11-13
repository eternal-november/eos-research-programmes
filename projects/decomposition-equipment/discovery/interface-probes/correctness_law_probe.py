#!/usr/bin/env python3
"""Finite audit for four typed correctness-judgment probes.

The tests check small witnesses and bounded instances. They are not a proof
of the general theorems discussed in the accompanying answer.
Only the Python standard library is required. Run with Python 3.10+.
"""
from __future__ import annotations
import itertools
import json
from fractions import Fraction as F
from pathlib import Path
from typing import FrozenSet, Iterable, TypeVar

T = TypeVar('T')

def powerset(items: Iterable[T]) -> list[FrozenSet[T]]:
    xs = tuple(items)
    return [frozenset(c) for n in range(len(xs)+1)
            for c in itertools.combinations(xs, n)]

S = frozenset({0, 1})
PREDS = powerset(S)
RELS = powerset(itertools.product(S, S))

def wlp(rel: FrozenSet[tuple[int, int]], q: FrozenSet[int]) -> FrozenSet[int]:
    return frozenset(x for x in S if all(y in q for a, y in rel if a == x))

def compose(r: FrozenSet[tuple[int, int]], s: FrozenSet[tuple[int, int]]) -> FrozenSet[tuple[int, int]]:
    return frozenset((x, z) for x, y in r for yy, z in s if y == yy)

def run() -> dict:
    result: dict = {'scope': 'Finite checks and exact rational counterexamples; not a completeness theorem.'}
    checks = {'monotonicity': 0, 'binary_meets': 0, 'sequential_composition': 0}
    for r in RELS:
        for p, q in itertools.product(PREDS, repeat=2):
            if p <= q:
                assert wlp(r,p) <= wlp(r,q)
                checks['monotonicity'] += 1
            assert wlp(r,p & q) == (wlp(r,p) & wlp(r,q))
            checks['binary_meets'] += 1
        for s in RELS:
            for q in PREDS:
                assert wlp(compose(r,s),q) == wlp(r,wlp(s,q))
                checks['sequential_composition'] += 1
    branch = frozenset({(0,0),(0,1)})
    q0, q1 = frozenset({0}), frozenset({1})
    assert 0 in wlp(branch,q0 | q1)
    assert 0 not in (wlp(branch,q0) | wlp(branch,q1))
    assert wlp(frozenset(), frozenset()) == S  # Liberal/partial correctness.
    result['hoare_partial'] = {'state_count': 2, 'relation_count': len(RELS),
                              'verified_instances': checks, 'join_counterexample_verified': True,
                              'divergence_vacuity_verified': True}

    # Environment selects b, controller observes b and chooses y=policy[b].
    policies = tuple(itertools.product((0,1), repeat=2))
    blind_policies = tuple(p for p in policies if p[0] == p[1])
    outcomes = frozenset(itertools.product((0,1), repeat=2))
    objectives = powerset(outcomes)
    def winning(q, candidates=policies):
        return frozenset(p for p in candidates if all((b,p[b]) in q for b in (0,1)))
    fixed_meet_checks = 0
    existence_meet_failures = 0
    for p, q in itertools.product(objectives, repeat=2):
        assert winning(p & q) == winning(p) & winning(q)
        fixed_meet_checks += 1
        if bool(winning(p & q)) != (bool(winning(p)) and bool(winning(q))):
            existence_meet_failures += 1
    zero = frozenset({(0,0),(1,0)})
    one = frozenset({(0,1),(1,1)})
    equality = frozenset({(0,0),(1,1)})
    assert winning(zero) and winning(one) and not winning(zero & one)
    assert winning(equality) == frozenset({(0,1)})
    assert not winning(equality, blind_policies)
    result['reactive_game'] = {
        'visible_policies': len(policies), 'blind_policies': len(blind_policies),
        'objective_count': len(objectives),
        'winning_set_meet_equalities_verified': fixed_meet_checks,
        'synthesis_existence_meet_failures': existence_meet_failures,
        'conjunction_witness': {'winning_for_y0': sorted(winning(zero)),
                                'winning_for_y1': sorted(winning(one)),
                                'winning_for_both': sorted(winning(zero & one))},
        'observation_witness': {'visible_equality_winners': sorted(winning(equality)),
                                'blind_equality_winners': sorted(winning(equality,blind_policies))}}

    # Two-hypothesis Bayesian toy: prior 1/2; conditional IID Bernoulli
    # probabilities P(1|h+) = 3/4 and P(1|h-) = 1/4.
    def odds(data: str) -> F:
        value = F(1)
        for datum in data:
            if datum not in '01':
                raise ValueError('Data must contain only 0 and 1.')
            value *= F(3) if datum == '1' else F(1,3)
        return value
    def posterior(data: str) -> F:
        v = odds(data)
        return v/(1+v)
    def accept(data: str) -> bool:
        return posterior(data) >= F(9,10)
    values = {d: str(posterior(d)) for d in ['', '1', '11', '110', '111', '1110']}
    assert accept('11') and not accept('110')
    assert accept('11') == accept('111')
    assert accept('110') != accept('1110')
    assert not accept('1') and accept('11')
    histories = [''.join(x) for n in range(5) for x in itertools.product('01',repeat=n)]
    update_checks = 0
    for d, e in itertools.product(histories,repeat=2):
        assert odds(d+e) == odds(d)*odds(e)
        assert posterior(d+e) == posterior(e+d)
        update_checks += 1
    # A different finite hypothesis space for a conjunction witness.
    mass = {'a': F(1,10), 'b': F(1,10), 'c': F(8,10)}
    def prob(event):
        return sum((mass[x] for x in event), F(0))
    events = powerset(mass)
    failures = 0
    for p,q in itertools.product(events,repeat=2):
        if p <= q:
            assert prob(p) <= prob(q)
        lhs = prob(p&q) >= F(9,10)
        rhs = prob(p) >= F(9,10) and prob(q) >= F(9,10)
        failures += lhs != rhs
    p, q = {'a','c'}, {'b','c'}
    assert prob(p) == prob(q) == F(9,10) and prob(p&q) == F(4,5)
    result['bayesian_toy'] = {
        'exact_posteriors': values,
        'update_composition_and_order_checks': update_checks,
        'threshold_conjunction_failures_on_three_atoms': failures,
        'persistence_failure_verified': True,
        'verdict_only_update_impossible_witness_verified': True,
        'independent_repetition_changes_acceptance_verified': True}

    # Copy one random output vs independently sample twice.
    p = F(3,4)
    copied_mismatch_probability = F(0)
    independent_mismatch_probability = (1-p)*p
    assert copied_mismatch_probability != independent_mismatch_probability
    result['stochastic_copy_witness'] = {
        'Pr_(0,1)_copy_one_sample': str(copied_mismatch_probability),
        'Pr_(0,1)_independent_resampling': str(independent_mismatch_probability)}

    # A fair bit is exposed before an adaptive guess; an oblivious guess
    # is constant. These are success probabilities, not worst-case verdicts.
    def guess_success(policy):
        return sum((F(1,2) for b in (0,1) if policy[b] == b), F(0))
    oblivious_best = max(guess_success(p) for p in blind_policies)
    adaptive_best = max(guess_success(p) for p in policies)
    assert oblivious_best == F(1,2) and adaptive_best == F(1)
    result['challenger_adaptivity_witness'] = {
        'best_oblivious_success_probability': str(oblivious_best),
        'best_adaptive_success_probability': str(adaptive_best)}
    return result

if __name__ == '__main__':
    report = run()
    text = json.dumps(report, indent=2)
    output = Path(__file__).with_name('correctness_law_probe_results.json')
    output.write_text(text + '\n', encoding='utf-8')
    print(text)

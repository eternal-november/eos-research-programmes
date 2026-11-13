#!/usr/bin/env python3
"""Exact finite history regressions, not proof of the general interaction theorem."""
from fractions import Fraction as F
from itertools import product
from math import prod
from pathlib import Path
import json

outer = {'A': {'x': F(1, 2), 'z': F(1, 2)}, 'B': {'b': F(1)}}
continuation = {('A', 'x'): {'u': F(1, 3), 'v': F(2, 3)},
                ('A', 'z'): {'w': F(1)}, ('B', 'b'): {'done': F(1)}}

def sequential(job):
    return {(x, y): p*q for x, p in outer[job].items()
            for y, q in continuation[job, x].items()}

def accumulate_then_cross(jobs):
    stages = [sequential(j) for j in jobs]
    return {tuple(trace): prod((stages[i][t] for i, t in enumerate(trace)), start=F(1))
            for trace in product(*(s.keys() for s in stages))}

def cross_then_accumulate(jobs):
    out = {}
    for xs in product(*(outer[j].keys() for j in jobs)):
        for ys in product(*(continuation[j, x].keys() for j, x in zip(jobs, xs))):
            out[tuple(zip(xs, ys))] = (
                prod((outer[j][x] for j, x in zip(jobs, xs)), start=F(1)) *
                prod((continuation[j, x][y] for j, x, y in zip(jobs, xs, ys)), start=F(1)))
    return out

assert sequential('A') == {('x', 'u'): F(1, 6), ('x', 'v'): F(1, 3), ('z', 'w'): F(1, 2)}
words = 0
for n in range(6):
    for jobs in product(('A', 'B'), repeat=n):
        lhs, rhs = accumulate_then_cross(jobs), cross_then_accumulate(jobs)
        assert lhs == rhs
        assert sum(lhs.values(), F(0)) == 1
        words += 1
fixture = accumulate_then_cross(('A', 'A', 'B'))
assert len(fixture) == 9
assert fixture[(('x', 'u'), ('z', 'w'), ('b', 'done'))] == F(1, 12)
# An explicitly declared zero-weight branch is retained, never removed by normalization.
outer['Z'] = {'live': F(1), 'zero': F(0)}
continuation['Z', 'live'] = {'done': F(1)}
continuation['Z', 'zero'] = {'retained': F(1)}
zero_fixture = accumulate_then_cross(('Z', 'A'))
assert len(zero_fixture) == 6
assert sum(p == 0 for p in zero_fixture.values()) == 3
assert zero_fixture == cross_then_accumulate(('Z', 'A'))
result = {
    'status': 'passed', 'arithmetic': 'exact rational',
    'scope': 'finite regression only, not a universal mathematical proof',
    'job_words_lengths_0_through_5': words,
    'A_completed_weights': {str(k): str(v) for k, v in sequential('A').items()},
    'AAB_histories': len(fixture),
    'AAB_total_mass': str(sum(fixture.values(), F(0))),
    'zero_fixture_retained_histories': len(zero_fixture),
    'zero_weight_histories_retained': 3,
    'empty_occurrence_family': {str(k): str(v) for k, v in accumulate_then_cross(()).items()},
}
Path(__file__).with_name('probability_fixture_results.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2))

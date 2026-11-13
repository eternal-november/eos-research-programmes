#!/usr/bin/env python3
"""Exact finite regression fixture; the general proof is in the bundled TeX dossier."""
from itertools import product
from collections import Counter


def add(*xs):
    return tuple(map(sum, zip(*xs))) if xs else (0, 0)


outer = {'A': {'x': (1, 2), 'z': (2, 1)}, 'B': {'b': (1, 0)}}
continuation = {('A', 'x'): {'u': (2, 0), 'v': (1, 1)},
                ('A', 'z'): {'w': (0, 2)}, ('B', 'b'): {'done': (0, 1)}}
receipts = {'q1': ('A',), 'q2': ('A', 'B'), 'q3': ('A', 'A', 'B')}


def sequential(job):
    return { (x, y): add(cx, cy)
             for x, cx in outer[job].items()
             for y, cy in continuation[job, x].items() }


def accumulate_then_cross(jobs):
    stages = [sequential(j) for j in jobs]
    return {tuple(trace): add(*(stages[i][t] for i, t in enumerate(trace)))
            for trace in product(*(s.keys() for s in stages))}


def cross_then_accumulate(jobs):
    answer = {}
    for xs in product(*(outer[j].keys() for j in jobs)):
        for ys in product(*(continuation[j, x].keys() for j, x in zip(jobs, xs))):
            trace = tuple(zip(xs, ys))
            answer[trace] = add(*(outer[j][x] for j, x in zip(jobs, xs)),
                                *(continuation[j, x][y] for j, x, y in zip(jobs, xs, ys)))
    return answer


def certifies(b, trace_costs):
    return all(all(bi >= ci for bi, ci in zip(b, c)) for c in trace_costs.values())


expected = {'q1': Counter({(3, 2): 1, (2, 3): 2}),
            'q2': Counter({(4, 3): 1, (3, 4): 2}),
            'q3': Counter({(7, 5): 1, (6, 6): 4, (5, 7): 4})}
for q, jobs in receipts.items():
    left, right = accumulate_then_cross(jobs), cross_then_accumulate(jobs)
    assert left == right
    assert Counter(left.values()) == expected[q]
    print(q, 'histories=', len(left), 'cost multiset=', dict(Counter(left.values())))
assert certifies((3, 3), accumulate_then_cross(receipts['q1']))
assert certifies((4, 4), accumulate_then_cross(receipts['q2']))
assert not certifies((4, 3), accumulate_then_cross(receipts['q2']))
assert certifies((7, 7), accumulate_then_cross(receipts['q3']))
for r in product(range(4), repeat=2):
    if r != (0, 0):
        assert not all(a >= b for a, b in zip(r, add(r, r)))
# Parameterized finite regression: all job words of lengths 0 through 5.
for n in range(6):
    for jobs in product(('A', 'B'), repeat=n):
        assert accumulate_then_cross(jobs) == cross_then_accumulate(jobs)
print('All capability fixture checks passed (including empty occurrence family).')

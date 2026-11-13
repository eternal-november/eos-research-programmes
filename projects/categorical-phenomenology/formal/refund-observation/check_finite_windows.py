#!/usr/bin/env python3
"""Finite integer sanity tests; not a substitute for the universal Lean proof."""
import json
from pathlib import Path

def observe(threshold, region):
    return tuple(threshold is not None and threshold <= x for x in sorted(region))

def composition(s, t, region):
    return tuple(s is not None and t is not None and s+t <= z for z in sorted(region))

def congruent(l, r, cap, A, B):
    # All possible profile patterns affecting these bounded outputs, plus empty.
    left = list(range(l, max(l, cap-r)+2)) + [None]
    right = list(range(r, max(r, cap-l)+2)) + [None]
    output = range(l+r, cap+1)
    cache = {}
    for s in left:
        for t in right:
            key = observe(s, A), observe(t, B)
            value = composition(s, t, output)
            if key in cache and cache[key] != value:
                return False
            cache[key] = value
    return True

cases = 0
removed = 0
empty = 0
for l in range(-3,4):
    for r in range(-3,4):
        for cap in range(-4,7):
            A = set(range(l, cap-r+1))
            B = set(range(r, cap-l+1))
            assert congruent(l,r,cap,A,B), (l,r,cap,'sufficiency')
            cases += 1
            empty += cap < l+r
            for a in A:
                assert not congruent(l,r,cap,A-{a},B), (l,r,cap,'left missing',a)
                removed += 1
            for b in B:
                assert not congruent(l,r,cap,A,B-{b}), (l,r,cap,'right missing',b)
                removed += 1
assert not congruent(-2,1,3,set(range(-2,4)),set(range(1,4)))
report = {'all_passed': True, 'lower_bound_range': [-3,3], 'total_cap_range': [-4,6],
          'parameter_cases': cases, 'empty_output_cases': empty,
          'single_relevant_point_removals_rejected': removed,
          'naive_total_cap_rejected': True,
          'scope': 'Finite threshold-profile sanity check; universal result is proved separately in Lean.'}
Path(__file__).with_name('finite_checks.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))

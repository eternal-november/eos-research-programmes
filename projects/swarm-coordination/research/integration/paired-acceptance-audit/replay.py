from copy import deepcopy
from itertools import combinations, product
import json
from audit import compare_supports, check_transcript, digest

primitives = list(product((False, True), (False, True), (-1, 0, 1)))
supports = [(x,) for x in primitives] + list(combinations(primitives, 2))
checks = 0
for left, right in product(supports, repeat=2):
    completions = [(all(x[0] and x[1] for x in pair), sum(x[2] for x in pair))
                   for pair in product(left, right)]
    vals = [v for _, v in completions]
    for threshold in (-1, 0, 1):
        passes = [good and val >= threshold for good, val in completions]
        verdict = 'certain-pass' if all(passes) else 'ruled-out' if not any(passes) else 'unresolved'
        assert compare_supports([left, right], threshold) == (min(vals), max(vals), verdict)
        checks += 1

plan = dict(arms=[dict(id='stack', build='1'), dict(id='direct', build='2')],
            interface='3', evaluator='4', threshold=1)
roster = dict(plan=digest('plan-v1', plan), cases=[dict(id='a', source='R')])
opening = 'public-fixture-only'
seal = digest('roster-v1', opening, roster)
row = dict(case='a', arm='stack', build='1', interface='3', source='R', status='complete')
assert check_transcript(plan, seal, roster, opening, [row]) == {
    ('a','stack'):'complete', ('a','direct'):'unresolved'}
rejects = 0
for k, v in dict(case='x', arm='x', build='9', interface='9', source='S', status='n/a').items():
    try:
        check_transcript(plan, seal, roster, opening, [row | {k:v}])
    except ValueError:
        rejects += 1
roster2 = deepcopy(roster)
roster2['cases'][0]['source'] = 'S'
for args in [(plan, seal, roster2, opening, [row]),
             (plan | dict(threshold=0), seal, roster, opening, [row]),
             (plan, seal, roster, opening, [row, row])]:
    try:
        check_transcript(*args)
    except ValueError:
        rejects += 1
assert rejects == 9
# Same armwise marginal service results, different semantics of the paired endpoint.
always_tied = [(True, True, 0)]
opposite = [(True, True, -1), (True, True, 1)]
assert compare_supports([always_tied], 0) == (0, 0, 'certain-pass')
assert compare_supports([opposite], 0) == (-1, 1, 'unresolved')
# An apparent gain exists only in the unsafe completion.
assert compare_supports([[(False,True,1),(True,True,0)]],1) == (0,1,'ruled-out')
# Product relaxation across cases discards a single shared cause.
shared = [((-1),1), (1,(-1))]
assert {a+b for a,b in shared} == {0}
assert compare_supports([opposite, opposite],0) == (-2,2,'unresolved')
print(json.dumps(dict(exhaustive_profile_checks=checks, rejected_transcript_mutations=rejects,
                      controls=4), sort_keys=True))

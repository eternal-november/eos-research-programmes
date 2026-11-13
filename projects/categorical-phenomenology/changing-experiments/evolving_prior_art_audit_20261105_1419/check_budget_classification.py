#!/usr/bin/env python3
"""Finite regression of the audit's allocation-poset classification.

The general proof is in exact_square_candidate_audit.md. These bounded checks
do not constitute proof over all matrices or all budgets.
"""
from itertools import product
from collections import deque
from pathlib import Path
import json


def vecs(bounds):
    return product(*(range(b + 1) for b in bounds))


def leq(x, y):
    return all(a <= b for a, b in zip(x, y))


def allocations(a):
    return [(r, s) for r in vecs(a)
            for s in vecs(tuple(x-y for x, y in zip(a, r)))]


def apply(C, x):
    return tuple(sum(c*v for c, v in zip(row, x)) for row in C)


def aleq(x, y):
    return leq(x[0], y[0]) and leq(x[1], y[1])


def connected(xs):
    if not xs:
        return False
    seen = {0}
    todo = deque([0])
    while todo:
        i = todo.popleft()
        for j in range(len(xs)):
            if j not in seen and (aleq(xs[i], xs[j]) or aleq(xs[j], xs[i])):
                seen.add(j)
                todo.append(j)
    return len(seen) == len(xs)


def classify(C):
    d, m = len(C), len(C[0])
    columns = [tuple(C[i][j] for i in range(d)) for j in range(m)]
    boolean = all(sum(v) <= 1 for v in columns)
    nonzero = [v for v in columns if sum(v)]
    sets = boolean and len(set(nonzero)) == len(nonzero)
    witnesses = sets and len(nonzero) == m
    return boolean, sets, witnesses


def check(C, bound=2):
    m = len(C[0])
    observed = [True, True, True]
    examples = [None, None, None]
    number_lifts = 0
    for a in product(range(bound+1), repeat=m):
        src = allocations(a)
        tgt = allocations(apply(C, a))
        image = [(apply(C, r), apply(C, s)) for r, s in src]
        for p, q in tgt:
            lifts = [rs for rs, pq in zip(src, image)
                     if leq(p, pq[0]) and leq(q, pq[1])]
            number_lifts += 1
            for k, ok in enumerate((bool(lifts), connected(lifts))):
                if not ok:
                    observed[k] = False
                    if examples[k] is None:
                        examples[k] = dict(a=a, p=p, q=q, lifts=lifts)
        equiv = (len(image) == len(set(image)) and set(image) == set(tgt)
                 and all(not aleq(image[i], image[j]) or aleq(src[i], src[j])
                         for i in range(len(src)) for j in range(len(src))))
        if not equiv:
            observed[2] = False
            if examples[2] is None:
                examples[2] = dict(a=a, source_objects=len(src),
                                   target_objects=len(tgt),
                                   image_objects=len(set(image)))
    return tuple(observed), examples, number_lifts


def main():
    count = 0
    lifts = 0
    mismatches = []
    for d, m in product((1, 2), repeat=2):
        for entries in product(range(3), repeat=d*m):
            C = tuple(tuple(entries[i*m:(i+1)*m]) for i in range(d))
            predicted = classify(C)
            actual, examples, n = check(C)
            count += 1
            lifts += n
            if predicted != actual:
                mismatches.append(dict(C=C, predicted=predicted, actual=actual,
                                       examples=examples))
    named = {}
    for name, C in {
        'split_one_unit': ((2,),),
        'split_two_resource_types': ((1,), (1,)),
        'merge_two_source_units': ((1, 1),),
        'erase_source_dimension': ((1, 0),),
        'injective_rename': ((0, 1), (1, 0)),
    }.items():
        actual, examples, n = check(C)
        named[name] = dict(matrix=C, predicted=classify(C), observed=actual,
                           first_failures=examples)
    result = dict(status='PASS' if not mismatches else 'FAIL',
                  scope={'dimensions': [1, 2], 'matrix_entries': [0, 1, 2],
                         'budget_coordinates': [0, 1, 2]},
                  matrices=count, lift_posets_checked=lifts,
                  mismatches=mismatches, named_examples=named,
                  limitation='Finite regression only; universal proof is in the audit note.')
    out = Path(__file__).with_name('budget_classification_checks.json')
    out.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ('status', 'matrices', 'lift_posets_checked')}))
    assert not mismatches


if __name__ == '__main__':
    main()

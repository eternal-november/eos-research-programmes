"""Exact bounded-alphabet check, not a proof of the all-size theorem."""
from itertools import product, permutations
from math import prod, factorial
import json
from pathlib import Path


def check(shape, odds, target, expected):
    xs = list(product(*[range(k) for k in shape]))
    weights = [prod(odds[i][x[i]] for i in range(len(shape))) for x in xs]
    ys = list(product(*[range(k) for k in target]))
    z = sum(weights)
    passes = 0
    min_bad_numerator = None
    for perm in permutations(range(len(xs))):
        marg = [[0] * k for k in target]
        for y, a in zip(ys, perm):
            for j, v in enumerate(y):
                marg[j][v] += weights[a]
        errors = [abs(weights[a] * z**(len(target)-1)
                      - prod(marg[j][v] for j, v in enumerate(y)))
                  for y, a in zip(ys, perm)]
        err = max(errors)
        if err == 0:
            passes += 1
        elif min_bad_numerator is None or err < min_bad_numerator:
            min_bad_numerator = err
    assert passes == expected, (shape, target, passes, expected)
    return {'source_shape': shape, 'target_shape': target,
            'permutations_checked': factorial(len(xs)),
            'product_preserving_permutations': passes,
            'expected_coarsening_permutations': expected,
            'minimum_nonproduct_independence_residual':
                min_bad_numerator / z**len(target)}


def main():
    rows = [check((2, 2), ((1, 3), (1, 5)), (2, 2), 8),
            check((2, 3), ((1, 2), (1, 3, 5)), (2, 3), 12),
            check((2, 2, 2), ((1, 3), (1, 5), (1, 7)), (2, 2, 2), 48),
            check((2, 2, 2), ((1, 3), (1, 5), (1, 7)), (2, 4), 144)]
    result = {'status': 'PASS', 'arithmetic': 'exact integer independence tests',
              'scope': 'Four rational fixtures; generic all-size claim requires the proof.',
              'checks': rows}
    Path(__file__).with_name('Product_Rigidity_QA.json').write_text(
        json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()

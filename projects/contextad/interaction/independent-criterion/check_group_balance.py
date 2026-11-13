#!/usr/bin/env python3
"""Exact finite regression only; the manuscript supplies the general proof.

Checks pure-middle balance failure for the original subgroup/quotient
PB-image-PO recipe. No general claim is inferred from enumeration.
"""
import itertools
import json
from pathlib import Path

G = frozenset(itertools.permutations(range(3)))
e = (0, 1, 2)
def mul(a, b):
    return tuple(a[b[i]] for i in range(3))
def inv(a):
    return tuple(a.index(i) for i in range(3))
def generated(seeds, identity, product):
    out = set(seeds) | {identity}
    while True:
        nxt = out | {product(a, b) for a in out for b in out}
        if nxt == out:
            return frozenset(out)
        out = nxt
def normal_closure(H, ambient, identity, product, inverse):
    return generated({product(product(g, h), inverse(g))
                      for g in ambient for h in H}, identity, product)
def quotient_size(ambient, normal, product, inverse):
    assert normal <= ambient
    identity = product(next(iter(ambient)), inverse(next(iter(ambient))))
    assert generated(normal, identity, product) == normal
    assert all(product(product(g, n), inverse(g)) in normal
               for g in ambient for n in normal)
    cosets = {frozenset(product(g, n) for n in normal) for g in ambient}
    assert len(cosets) * len(normal) == len(ambient)
    return len(cosets)

def check_case(ambient, H, K, identity, product, inverse):
    nh = normal_closure(H, ambient, identity, product, inverse)
    left_kernel = K & nh
    right_kernel = normal_closure(H & K, K, identity, product, inverse)
    left = quotient_size(K, left_kernel, product, inverse)
    right = quotient_size(K, right_kernel, product, inverse)
    assert left_kernel != right_kernel
    assert left != right
    return {
        'ambient_order': len(ambient), 'H_order': len(H), 'K_order': len(K),
        'intersection_order': len(H & K), 'normal_closure_H_order': len(nh),
        'pushout_first_kernel_order': len(left_kernel),
        'pullback_first_kernel_order': len(right_kernel),
        'pushout_first_quotient_order': left,
        'pullback_first_quotient_order': right,
        'balance_fails': True,
    }

H = frozenset({e, (1, 0, 2)})
K = frozenset({e, (1, 2, 0), (2, 0, 1)})
assert generated(H, e, mul) == H
assert generated(K, e, mul) == K
first = check_case(G, H, K, e, mul, inv)
assert first['pushout_first_quotient_order'] == 1
assert first['pullback_first_quotient_order'] == 3

GG = frozenset(itertools.product(G, repeat=2))
ee = (e, e)
def pmul(a, b):
    return mul(a[0], b[0]), mul(a[1], b[1])
def pinv(a):
    return inv(a[0]), inv(a[1])
diagonal = frozenset((a, a) for a in G)
g, h = (1, 0, 2), (1, 2, 0)
assert mul(g, h) != mul(h, g)
x = (mul(mul(g, h), inv(g)), h)
cyclic = generated({x}, ee, pmul)
assert x not in diagonal
assert x in normal_closure(diagonal, GG, ee, pmul, pinv)
second = check_case(GG, diagonal, cyclic, ee, pmul, pinv)
assert second['pushout_first_quotient_order'] == 1
assert second['pullback_first_quotient_order'] == 3

result = {
    'status': 'pass',
    'scope': 'Exact finite regression, not proof of the general group iff theorem',
    'S3_C2_C3': first,
    'S3_squared_diagonal_cyclic': second,
}
path = Path(__file__).with_name('check_group_balance_results.json')
path.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))

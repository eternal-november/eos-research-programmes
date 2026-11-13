#!/usr/bin/env python3
"""Exact finite checks for semidirect writer contexts and their braid obstruction."""
import itertools as it
import json

V = tuple(it.product(range(2), repeat=2))
E = (0, 0)
add = lambda u, v: tuple(x ^ y for x, y in zip(u, v))
P = lambda a: (a[1], a[0])
Q = lambda a: (a[0] ^ a[1], a[1])
act = lambda f, b, a: f(a) if b else a

def verify_pair(f):
    # Exactly the two unit and two multiplication equations for B A -> A B.
    count = 0
    for a in V:
        assert act(f, 0, a) == a
    for b in range(2):
        assert act(f, b, E) == E
        for a, d in it.product(V, repeat=2):
            assert act(f, b, add(a, d)) == add(act(f, b, a), act(f, b, d))
            count += 1
        for c, a in it.product(range(2), V):
            assert act(f, b ^ c, a) == act(f, b, act(f, c, a))
            count += 1
    return count

def normal_product(x, y):
    # Proposed normal form A B C, with B and C incorrectly assumed independent.
    a, b, c = x
    d, e, f = y
    return add(a, act(P, b, act(Q, c, d))), b ^ e, c ^ f

def compose(g, h):
    return tuple(g[V.index(a)] for a in h)

def main():
    pair_checks = verify_pair(P) + verify_pair(Q)
    braid_failures = []
    for b, c, a in it.product(range(2), range(2), V):
        left = act(Q, c, act(P, b, a))
        right = act(P, b, act(Q, c, a))
        if left != right:
            braid_failures.append(dict(b=b, c=c, a=a, left=left, right=right))
    assert len(braid_failures) == 3
    T = list(it.product(V, range(2), range(2)))
    associativity_failures = sum(
        normal_product(normal_product(x, y), z) != normal_product(x, normal_product(y, z))
        for x, y, z in it.product(T, repeat=3))
    assert associativity_failures > 0
    # Repair: retain the actual generated transformation, not two parity bits.
    identity = tuple(V)
    generators = [tuple(map(P, V)), tuple(map(Q, V))]
    G = {identity}
    while True:
        enlarged = G | {compose(g, h) for g in G for h in generators}
        if enlarged == G:
            break
        G = enlarged
    assert len(G) == 6
    assert {tuple(g[V.index(a)] for a in V if a != E) for g in G} == set(it.permutations(V[1:]))
    def mul(x, y):
        a, g = x
        d, h = y
        return add(a, g[V.index(d)]), compose(g, h)
    S = list(it.product(V, G))
    for x, y, z in it.product(S, repeat=3):
        assert mul(mul(x, y), z) == mul(x, mul(y, z))
    # All affine transformations are observationally distinct on four probes.
    observations = {tuple(add(a, g[V.index(d)]) for d in V) for a, g in S}
    assert len(observations) == 24
    # The repair is not merely a larger independent-bit product: order is observable.
    p, q = generators
    assert compose(p, q) != compose(q, p)
    assert compose(compose(p, q), compose(p, q)) != identity
    assert compose(compose(compose(p, q), compose(p, q)), compose(p, q)) == identity
    # Parity-vector collision: identity and the word P Q P Q have equal parities.
    assert compose(compose(p, q), compose(p, q)) != identity
    # Positive control: commuting P and identity DOES give the 16-state product.
    old_Q = globals()['Q']
    globals()['Q'] = lambda a: a
    for x, y, z in it.product(T, repeat=3):
        assert normal_product(normal_product(x, y), z) == normal_product(x, normal_product(y, z))
    globals()['Q'] = old_Q
    return dict(status='passed', pair_multiplication_checks=pair_checks,
                braid_cases=16, braid_failures=braid_failures,
                attempted_product_associativity_cases=16**3,
                attempted_product_associativity_failures=associativity_failures,
                repaired_mode_states=len(G), repaired_total_states=len(S),
                repaired_associativity_cases=len(S)**3,
                distinguishable_affine_behaviors=len(observations),
                commuting_positive_control_cases=16**3)

if __name__ == '__main__':
    print(json.dumps(main(), indent=2))

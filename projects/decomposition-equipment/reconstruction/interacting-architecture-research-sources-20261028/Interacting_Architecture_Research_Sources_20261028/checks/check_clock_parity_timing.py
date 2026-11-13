"""Exact finite check of clock decoder timing and the all-state quotient.

Uses abstract Toffolis to test the algebra/timing, not nearest-neighbor routing.
"""
import itertools
from collections import Counter
import sympy as sp

n = 3
edges = [(0, 1), (0, 2), (1, 2)]
gates = edges + edges[::-1]
L = len(gates)
zs = list(itertools.product([0, 1], repeat=n + 1))
states = [(t, z) for t in range(L) for z in zs]

def gate(z, edge):
    a, b = edge
    return z[:-1] + (z[-1] ^ (z[a] & z[b]),)

def step(s):
    t, z = s
    return (t + 1) % L, gate(z, gates[t])

def emit(s):
    t, z = s
    return int(t == 0) * z[-1]

def suffix_bit(t, z):
    # At t=0 the next phase-zero emission is the current one.
    if t == 0:
        return z[-1]
    for edge in gates[t:]:
        z = gate(z, edge)
    return z[-1]

def cls(s):
    t, z = s
    return -1 if suffix_bit(t, z) == 0 else (-t) % L

def class_step(c):
    return -1 if c == -1 else (c - 1) % L

patterns = {}
for s in states:
    w, cur = [], s
    for _ in range(L):
        w.append(emit(cur))
        cur = step(cur)
    assert cur == s
    c = cls(s)
    expected = tuple(int(j == c) for j in range(L))
    assert tuple(w) == expected
    assert cls(step(s)) == class_step(c)
    assert emit(s) == int(c == 0)
    patterns.setdefault(c, tuple(w))
assert len(patterns) == L + 1
assert len(set(patterns.values())) == L + 1
counts = Counter(map(cls, states))
assert counts[-1] == len(states) // 2
assert all(counts[k] == len(states) // (2 * L) for k in range(L))

M = len(edges)
for x in itertools.product([0, 1], repeat=n):
    q = 0
    for i, j in edges:
        q ^= x[i] & x[j]
    assert suffix_bit(M, x + (0,)) == q
    assert int(cls((M, x + (0,))) == (-M) % L) == q

print({"n": n, "clock_length": L, "hidden_states": len(states),
       "predictive_classes": L + 1, "zero_class_count": counts[-1],
       "each_pulse_class_count": counts[0], "all_state_intertwining": True,
       "halfway_quadratic_slice": True})

# Independent per-time BSC noise preserves all-state and initialized rank.
eps = sp.Rational(1, 4)
classes = [-1] + list(range(L))
likelihood = sp.Matrix([
    [sp.prod((1-eps) if y[j] == int(j == c) else eps for j in range(L))
     for c in classes]
    for y in itertools.product([0, 1], repeat=L)
])
assert likelihood.rank() == L + 1
weights = sp.diag(*[sp.Rational(counts[c], len(states)) for c in classes])
assert (weights * likelihood.T).rank() == L + 1
P = sp.zeros(L + 1)
for j, c in enumerate(classes):
    P[classes.index(class_step(c)), j] = 1
dets = []
for y in (0, 1):
    Ty = P * sp.diag(*[(1-eps) if y == int(c == 0) else eps for c in classes])
    assert Ty.det() != 0
    dets.append(Ty.det())
print({"BSC_error": eps, "noisy_observable_rank": likelihood.rank(),
       "noisy_reachable_rank": (weights * likelihood.T).rank(),
       "noisy_symbol_determinants": dets})

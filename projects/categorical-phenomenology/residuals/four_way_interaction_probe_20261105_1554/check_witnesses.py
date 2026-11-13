"""Finite regressions for the mathematical witnesses, not a novelty proof."""
from itertools import product, combinations
from functools import lru_cache
import json
from pathlib import Path

X = tuple(product((0, 1), repeat=2))
FULL = (1 << len(X)) - 1

@lru_cache(None)
def depth_functions(k):
    """All truth tables of native adaptive coordinate-query trees of depth <= k.
    Each query destroys one supplied same-state specimen. Leaves output a bit.
    """
    fs = {0, FULL}
    if k:
        prev = depth_functions(k - 1)
        for j in range(2):
            for lo, hi in product(prev, repeat=2):
                fs.add(sum((((hi if x[j] else lo) >> i) & 1) << i
                           for i, x in enumerate(X)))
    return frozenset(fs)

def meet_closure(fs):
    out = {FULL}
    for f in fs:
        out |= {g & f for g in tuple(out)}
    return out

and_table = sum((x[0] and x[1]) << i for i, x in enumerate(X))
assert [len(depth_functions(k)) for k in range(3)] == [2, 6, 16]
assert len(meet_closure(depth_functions(1))) == 10
assert and_table not in depth_functions(1)
assert and_table in meet_closure(depth_functions(1))
assert and_table in depth_functions(2)

@lru_cache(None)
def knows_how(B, b, diagnostic_cost, stock=1, destructive=False):
    """Goal: actuate the correct hidden bit. Actuation costs 1 and needs stock.
    A diagnostic reports the hidden bit and optionally destroys the stock.
    The recursive cases enumerate every legal first action.
    """
    if stock and b >= 1 and len(B) == 1:
        return True
    if b >= diagnostic_cost and diagnostic_cost > 0 and stock:
        return all(knows_how((w,), b-diagnostic_cost, diagnostic_cost,
                             0 if destructive else stock, destructive)
                   for w in B)
    return False

epistemic = []
for k in range(1, 5):
    truth = [knows_how((0, 1), b, k) for b in range(k+3)]
    assert truth == [b >= k+1 for b in range(k+3)]
    assert all(knows_how((w,), 1, k) for w in (0, 1))
    assert not any(knows_how((0, 1), b, k, destructive=True)
                   for b in range(12))
    epistemic.append({"diagnostic_cost": k, "pointwise_minimum": 1,
                      "uniform_minimum": k+1,
                      "truth_by_budget": truth})

def subsets(xs):
    xs = tuple(xs)
    return [frozenset(c) for k in range(len(xs)+1) for c in combinations(xs, k)]

def is_complex(H):
    return frozenset() in H and all(A in H for B in H for A in subsets(B))

universality = []
for n in range(1, 5):
    W = frozenset(range(n))
    subs = subsets(W)
    count = 0
    for bits in range(1 << len(subs)):
        H = {subs[i] for i in range(len(subs)) if bits >> i & 1}
        if not is_complex(H):
            continue
        facets = {F for F in H if not any(F < G for G in H)}
        reconstructed = {B for B in subs if any(B <= F for F in facets)}
        assert H == reconstructed
        count += 1
    universality.append({"ambient_worlds": n, "complexes_checked": count})

result = {
    "specimen_test": {
        "state_order": X,
        "native_function_counts_at_budget_0_1_2": [2,6,16],
        "meet_completion_at_budget_1": 10,
        "conjunction_in_completion_but_not_native_1": True,
        "conjunction_native_2": True,
    },
    "epistemic_budget_tests": epistemic,
    "all_finite_complexes_reconstruction_checks": universality,
    "limits": "Enumeration corroborates only these finite instances; proofs are in REPORT.md."
}
out = Path(__file__).with_name('checks.json')
out.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))

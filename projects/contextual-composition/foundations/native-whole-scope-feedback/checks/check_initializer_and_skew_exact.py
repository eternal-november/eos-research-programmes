"""Finite exact diagnostics only; categorical claims use the written proofs."""
from fractions import Fraction as F
from itertools import product
import json
from pathlib import Path

def push(law, fn):
    out = {}
    for atom, mass in law.items():
        key = fn(atom)
        out[key] = out.get(key, F(0)) + mass
    return out

def marg(law, indices):
    return push(law, lambda a: tuple(a[i] for i in indices))

def fair(n):
    return {a: F(1, 2**n) for a in product((0,1), repeat=n)}

def conditional(law, given_indices, given, result_indices):
    row = {a:p for a,p in law.items() if tuple(a[i] for i in given_indices)==given}
    mass = sum(row.values(), F(0))
    if not mass:
        return None # no zero-fibre conditional is inferred
    return {a:p/mass for a,p in marg(row,result_indices).items()}

def assert_law(law):
    assert all(x >= 0 for x in law.values()) and sum(law.values(),F(0)) == 1

results = {}
# Correct singleton marginals do not repair a fixed independent expanded row.
diag = {a: (F(1,2) if a in ((0,0,0),(1,1,1)) else F(0))
        for a in product((0,1),repeat=3)}
assert_law(diag)
assert all(marg(diag,(i,)) == fair(1) for i in range(3))
assert marg(diag,(0,2)) != fair(2)
results['fixed_independent_expanded_row_obstruction'] = True
# Remote dependence alone is not an obstruction to a correct complete local row.
remote = {(0,y,z):(F(1,2) if y==z else F(0)) for y,z in product((0,1),repeat=2)}
assert_law(remote)
assert marg(remote,(0,2)) == {(0,0):F(1,2),(0,1):F(1,2)}
results['remote_seed_correlation_admitted_with_fixed_local_row'] = True
# Full raw functions are retained on zero atoms, independently of conditional choices.
raw = (0,1,2)
mu = {0:F(1,2),1:F(1,2),2:F(0)}
r = {0:0,1:0,2:1}; s = {0:0,1:0}
nu = push(mu,lambda z:r[z])
assert nu == {0:F(1),1:F(0)} and r[2] == 1
assert push(nu,lambda z:s[z]) == push(mu,lambda z:s[r[z]])
zero_branch = {(z,k): mu[z]*F(1,2) for z in raw for k in (0,1)}
assert conditional(zero_branch,(0,),(2,),(1,)) is None
results['all_zero_raw_maps_and_composition_retained'] = True
# Noninjective paid-root transport forms the exact convex mixture.
mixture = {(x,z):(F(1,3) if (x,z)==(0,0) else F(2,3) if (x,z)==(1,1) else F(0))
           for x,z in product((0,1),repeat=2)}
collapsed = push(mixture,lambda a:(0,a[1]))
assert conditional(collapsed,(0,),(0,),(1,)) == {(0,):F(1,3),(1,):F(2,3)}
results['noninjective_positive_fibre_convex_mixture'] = True
# Augmented tensor dimensions, retaining complete expanded tensors inside product.
expanded_dim = 2*2
atomic_product_dim = 2*expanded_dim-1
global_seed_tensor_dim = (2+2-1)*2*2
assert (atomic_product_dim,global_seed_tensor_dim)==(7,12)
results['coefficient_dimensions'] = {'atomic_expanded_product':7,'global_seed_tensor':12}
# Strict directed associativity: pairwise local constraints hold, full-root constraints fail.
crossswap = {a:(F(1,4) if a[2]==a[1] and a[3]==a[0] else F(0))
             for a in product((0,1),repeat=4)}
assert_law(crossswap)
assert len(crossswap)==16 and sum(p==0 for p in crossswap.values())==12
assert marg(crossswap,(0,2))==fair(2) and marg(crossswap,(1,3))==fair(2)
assert conditional(crossswap,(0,1),(0,0),(2,)) != fair(1)
results['skew_crossswap_right_admitted_left_excluded'] = True
# Distinguished old product is admitted in BOTH bracketings and is unchanged by flattening.
ind = fair(4)
for xy in product((0,1),repeat=2):
    for i in (2,3):
        assert conditional(ind,(0,1),xy,(i,))==fair(1)
assert marg(ind,(0,2))==fair(2) and marg(ind,(1,3))==fair(2)
assert push(ind,lambda a:a)==ind
results['comonoidal_product_inclusion_both_bracketings'] = True
# Silent initialization must include zero branches in its well-foundedness check.
def acyclic(edges):
    active, done = set(), set()
    def visit(v):
        if v in active: return False
        if v in done: return True
        active.add(v)
        if not all(visit(w) for w in edges.get(v,())): return False
        active.remove(v); done.add(v); return True
    return all(visit(v) for v in edges)
assert acyclic({'u':['v'],'v':[]})
assert not acyclic({'u':['v'],'v':['u']})
results['zero_branch_cycle_rejected_all_raw_guard'] = True
out = Path(__file__).with_name('initializer_and_skew_exact_results.json')
out.write_text(json.dumps({'status':'PASS','scope':'finite exact diagnostics, not a proof assistant',
                           'checks':results}, indent=2)+'\n')
print(out.read_text())

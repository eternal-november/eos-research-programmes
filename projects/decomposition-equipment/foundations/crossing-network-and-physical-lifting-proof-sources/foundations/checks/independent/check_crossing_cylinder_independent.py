#!/usr/bin/env python3
"""Independent cylinder tests versus direct actual alpha/beta construction."""
from itertools import product,permutations
from pathlib import Path
import json
perms=list(permutations(range(4)))

def direct(m,q):
    good=set()
    for alpha in perms: # (r,t) -> p
        ai={p:divmod(i,2) for i,p in enumerate(alpha)}
        for betas in product(((0,1),(1,0)),repeat=m):
            whole=[]
            for ell in range(m):
                per=tuple(2*ai[p][0]+betas[ell][ai[p][1]] for p in range(4))
                whole.extend([per]*q)
            good.add(tuple(whole))
    return good

def descriptors(per):
    inv={x:p for p,x in enumerate(per)}
    return tuple(tuple(inv[2*r+n] for r in range(2)) for n in range(2))

results=[]
for m,q in ((1,1),(1,2),(2,1),(2,2)):
    good=direct(m,q);total=passes=weaksets=0
    for theta in product(perms,repeat=m*q):
        ds=[descriptors(p) for p in theta]
        f=all(ds[ell*q+j]==ds[ell*q] for ell in range(m) for j in range(q))
        level=all(set(ds[ell*q])==set(ds[0]) for ell in range(m))
        actual=f and level
        assert actual==(theta in good)
        total+=1;passes+=actual
        weaksets+=all(set(d)==set(ds[0]) for d in ds)
    assert passes==(24 if m==1 else 48)
    results.append({'parallel_levels':m,'q_witnesses_per_level':q,'q_preserving_whole_matchings':total,'cylinder_fillable':passes,'weaker_descriptor_set_only_passes':weaksets})
# q-dependent permutation preserves unordered descriptor set but fails actual factor identity.
identity=(0,1,2,3);swap_t=(1,0,3,2)
assert set(descriptors(identity))==set(descriptors(swap_t))
assert descriptors(identity)!=descriptors(swap_t)
assert (identity,swap_t) not in direct(1,2)
# Two-level controlled twist changes even the descriptor set.
twist=(0,1,3,2)
assert set(descriptors(identity))!=set(descriptors(twist))
assert (identity,twist) not in direct(2,1)
out={'status':'PASS','scope':'Singleton A,B,C,K,D; R has2 witnesses,P4; one or two lower interface values; one or two actual Q witnesses at each; S_l1,N_l2. All actual Q-preserving whole matchings, independently compared against every alpha0,beta realization with T2. Ordinary square fills throughout; tests isolate F and L. This does not enumerate every four-corner type/profile.','profiles':results,'q_dependent_permutation_counterexample':'PASS','controlled_twist_counterexample':'PASS'}
Path(__file__).with_name('Crossing_Cylinder_Independent_Checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))

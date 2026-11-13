#!/usr/bin/env python3
from itertools import product,combinations
from pathlib import Path
import json
triples=list(product(range(2),repeat=3));universe={(part,v) for part in range(3) for v in range(2)}
covered_count=yes_count=positive_vectors=unprescribed_vectors=0
for bits in product((0,1),repeat=8):
    bs=[t for t,take in zip(triples,bits) if take]
    if {(i,v) for t in bs for i,v in enumerate(t)}!=universe:continue
    covered_count+=1
    # Direct combinatorial perfect matching, independent of integer equations.
    covers=[pair for pair in combinations(range(len(bs)),2) if all(bs[pair[0]][i]!=bs[pair[1]][i] for i in range(3))]
    deg={a:sum(t[a[0]]==a[1] for t in bs) for a in universe}
    positive=[]
    for ns in product((1,2),repeat=len(bs)):
        positive_vectors+=1
        if all(sum(ns[j] for j,t in enumerate(bs) if t[a[0]]==a[1])==deg[a]+1 for a in universe):positive.append(ns)
    assert len(positive)==len(covers)
    assert {tuple(j for j,n in enumerate(ns) if n==2) for ns in positive}==set(covers)
    unprescribed=[]
    for ns in product((0,1,2),repeat=len(bs)):
        unprescribed_vectors+=1
        if all(sum(ns[j] for j,t in enumerate(bs) if t[a[0]]==a[1])==1 for a in universe):unprescribed.append(ns)
    assert len(unprescribed)==len(covers)
    assert all(max(ns,default=0)<=1 for ns in unprescribed)
    yes_count+=bool(covers)
# The stated covered negative instance.
negative=[(0,0,0),(0,1,1),(1,0,1)]
assert {(i,v) for t in negative for i,v in enumerate(t)}==universe
assert not any(all(x[i]!=y[i] for i in range(3)) for x,y in combinations(negative,2))
out={'status':'PASS','all_triplet_families_tested':256,'covered_families':covered_count,'covered_yes_instances':yes_count,'positive_multiplicity_vectors_checked':positive_vectors,'unprescribed_vectors_checked':unprescribed_vectors,'scope':'All B subsets of the 8 possible triples on three two-element parts. Exact cover pairs independently compared with positive-support shifted and unprescribed multiplicity equations. Finite reduction regression, not an independent proof that 3DM is NP-complete.'}
Path(__file__).with_name('Grid_Complexity_Reduction_Independent_Checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))

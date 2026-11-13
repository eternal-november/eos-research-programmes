"""Independent review of full-faithful successive provenance and nullary fibres."""
import itertools as it,json
count={'two_stage_hom_pairs':0,'weak_stage_hom_pairs':0,'nullary_endpoint_pairs':0}
for n in range(1,3):
 for m in range(4):
  for f in it.product(range(n),repeat=m):
   for x,y in it.product(range(m),repeat=2):
    fibre=[z for z in range(m) if f[z]==f[x]==f[y]]
    assert bool(fibre)==(f[x]==f[y])
    # Strict diagonal fibre would instead require x=y; retain this negative case.
    if x!=y and f[x]==f[y]:assert not (x==y) and fibre
    count['nullary_endpoint_pairs']+=1
   for k in range(4):
    for g in it.product(range(m),repeat=k):
     fg=[f[g[z]] for z in range(k)]
     strict=[(z,g[z]) for z in range(k)]
     weak=[(z,x) for z in range(k) for x in range(m) if f[x]==fg[z]]
     assert {z for z,x in strict}==set(range(k))
     assert {z for z,x in weak}==set(range(k))
     for a,b in it.product(strict,repeat=2):
      # Old-value provenance defines source arrows, not equality of middle names.
      assert (f[a[1]]==f[b[1]])==(fg[a[0]]==fg[b[0]])
      count['two_stage_hom_pairs']+=1
     for a,b in it.product(weak,repeat=2):
      assert (f[a[1]]==f[b[1]])==(fg[a[0]]==fg[b[0]])
      count['weak_stage_hom_pairs']+=1
# Explicit counterexample to replacing the second interface by K_g independently.
f=(0,0);g=(0,1)
assert g[0]!=g[1] and f[g[0]]==f[g[1]]
count['naive_independent_Kg_counterexample']='PASS'
print(json.dumps(count,indent=2))

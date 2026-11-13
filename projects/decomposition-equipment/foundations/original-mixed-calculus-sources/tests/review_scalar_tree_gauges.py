"""Independent scalar-sector checks: C2/C3 with an absorbing nonunit root.
Combinatorial rooted trees and ancestral positive-graph supports; no coefficient claim.
"""
import itertools as it,json
checks=0
for n in (2,3):
 for size in range(1,6):
  for tail in it.product(*(range(v) for v in range(1,size))):
   par=(None,)+tail
   for flags in it.product((False,True),repeat=size):
    if any(flags[v] and not flags[par[v]] for v in range(1,size)):continue
    pos=[v for v in range(1,size) if flags[v]]
    for vals in it.product(range(n),repeat=len(pos)):
     s=dict(zip(pos,vals))
     # Local edge gauge at v adds g_v at v and subtracts it at parent.
     # Invert resulting node scalars from leaves to root.
     g={}
     for v in reversed(pos):g[v]=(s[v]+sum(g.get(w,0) for w in range(1,size) if par[w]==v))%n
     recovered={v:(g[v]-sum(g.get(w,0) for w in range(1,size) if par[w]==v))%n for v in pos}
     assert recovered==s
     rootshift=(-sum(g.get(w,0) for w in range(1,size) if par[w]==0))%n
     assert rootshift==(-sum(vals))%n
     # All unit-root choices preserve total; absorbing root stays fixed but
     # distinct nonroot assignments still distinguish objects.
     def mul(a,b):return n if n in (a,b) else (a+b)%n
     for root in range(n+1):
      aggregate=mul(root,rootshift)
      for val in vals:aggregate=mul(aggregate,val)
      assert aggregate==root
     checks+=1
# Arbitrary graft closure is false for a proper subgroup: 0=1+3 in C4.
H={0,2}
assert (1+3)%4 in H and 1 not in H and 3 not in H
# Lawful quotient-normalized grafts do remain in H.
for parent in H:
 for a,b in it.product(H,repeat=2):assert (parent-a-b)%4 in H
print(json.dumps({'arbitrary_graft_counterexample':'PASS', 'scalar_tree_assignments':checks,'status':'PASS','scope':'scalar gauges only; no graph or coefficient lifting assertion'},indent=2))

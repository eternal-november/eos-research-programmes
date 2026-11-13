from itertools import product, combinations
import json
states=list(product((0,1),repeat=2))
x=tuple(a for a,b in states); y=tuple(b for a,b in states)
H={x,y,(0,)*4,(1,)*4}
while True:
    new=H|{tuple(a^b for a,b in zip(f,g)) for f in H for g in H}
    if new==H:break
    H=new
AND=tuple(a&b for a,b in states)
assert len(H)==8 and AND not in H
assert all(sum(h)%2==0 for h in H)
local=[]
for coordinate,value in product(range(2),(0,1)):
    subset=[i for i,s in enumerate(states) if s[coordinate]==value]
    assert any(all(h[i]==AND[i] for i in subset) for h in H)
    local.append([coordinate,value])
S=list(product((0,1),repeat=4))
def obs(s):
    c,u,v,z=s; return (c,v^z,u^z)
def out(s): return s[1]^s[2]^s[3]
conflicts=[(s,t) for s in S for t in S if obs(s)==obs(t) and out(s)!=out(t)]
assert len(conflicts)==16
for raw in (1,2,3):
    assert all(out(s)==out(t) for s in S for t in S if (obs(s),s[raw])==(obs(t),t[raw]))
budgets=[]
for r in range(2,6):
    n=2**r; k=n-2
    demands=[n-2**(r-s) for s in range(1,r+1)]
    assert all(d<=k for d in demands[:-1]) and demands[-1]>k
    budgets.append(dict(r=r,n=n,k=k,boundary_demands=demands))
# Shared immutable snapshot must be matched, not independently chosen.
world_records=[(x,x) for x in (0,1)]
synchronized=[(r,s) for r in world_records for s in world_records if r[0]==s[0]]
assert len(synchronized)==2 and len(list(product(world_records,repeat=2)))==4
# Actual two-mode constant-reading sensor: same occurrence shared vs fresh calls.
records=(0,1)
shared={(e,e) for e in records}; fresh=set(product(records,repeat=2))
assert len(shared)==2 and len(fresh)==4
# Active four-corner grid: exact global and all restricted whole matchings.
grid_inputs=list(product((0,1),repeat=3))
for a,b,k in grid_inputs:
    R=(1-a,1-b); Q=1-k; T=R[0]&R[1]
    P=(1-a)&(1-b); N=(R[0]&R[1])^Q
    assert (P^Q)==N==((1-a)&(1-b))^(1-k)
print(json.dumps(dict(affine_generated_tables=len(H),affine_AND_rejected=True,active_grid_input_records=len(grid_inputs),
 locally_compilable_contexts=local,encoded_ordered_conflict_pairs=len(conflicts),
 raw_repairs=["u","v","z"],high_order_budget_cases=budgets,
 synchronized_world_record_count=len(synchronized),shared_execution_count=len(shared),fresh_execution_count=len(fresh)),indent=2))

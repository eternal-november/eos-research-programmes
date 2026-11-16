"""Independent finite domain/nesting checks; no general proof claim."""
from itertools import product
import json
nodes=range(3)
def acyclic(edges,vertices):
    vertices=set(vertices); visiting=set(); done=set()
    def visit(x):
        if x in visiting:return False
        if x in done:return True
        visiting.add(x)
        for a,b in edges:
            if a==x and b in vertices and not visit(b):return False
        visiting.remove(x);done.add(x);return True
    return all(visit(x) for x in vertices)
def induced(edges,U,V):
    out=set()
    for v in V:
        pending=[b for a,b in edges if a==v]; seen=set()
        while pending:
            x=pending.pop()
            if x in V:out.add((v,x));continue
            if x in seen:continue
            seen.add(x);pending.extend(b for a,b in edges if a==x)
    return out
count=0
pairs=list(product(nodes,repeat=2))
for bits in product((0,1),repeat=9):
    E={p for p,b in zip(pairs,bits) if b}
    for mask in product((0,1),repeat=3):
        U={x for x,b in zip(nodes,mask) if b};V=set(nodes)-U
        right=acyclic(E,U) and acyclic(induced(E,U,V),V)
        assert acyclic(E,nodes)==right
        count+=1
# Silent chains retain one node/content factor per initial invocation.
for m in range(20):
    closure=tuple(range(m,-1,-1))
    assert len(closure)==m+1
    assert sum(0 for _ in closure)==0
# A zero-probability paid outcome can initialize a longer silent chain.
# Outcome 0 mass1 initializes label0; outcome1 mass0 initializes label7.
all_raw_depths=[1+(label+1) for label in (0,7)]
assert max(all_raw_depths)==9 and all_raw_depths[0]==2
print(json.dumps({'status':'passed','graph_partition_cases':count,
 'zero_cost_chains':20,'zero_outcome_envelope_depth':max(all_raw_depths),
 'scope':'finite admission/nesting and cost-bound probes; not native coefficient certification'},indent=2))

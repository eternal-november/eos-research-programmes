#!/usr/bin/env python3
"""Independent C5 partition/forest normal-form checks (edgeless graphs)."""
from itertools import product
import json

def partitions(n,k):
    return list(product(range(k),repeat=n)) if k else ([()] if n==0 else [])
def sizes(p,k): return tuple(p.count(j) for j in range(k))
def substitute(p,k,children,arities):
    offsets=[]; s=0
    for a in arities: offsets.append(s);s+=a
    ranks=[0]*k; result=[]
    for j in p:
        result.append(offsets[j]+children[j][ranks[j]])
        ranks[j]+=1
    return tuple(result)
def inverse_request(p,k,target,arities):
    offsets=[];total=0
    for a in arities: offsets.append(total);total+=a
    if len(target)!=len(p) or any(t<0 or t>=total for t in target): return None
    children=[[] for _ in range(k)]
    for j,t in zip(p,target):
        if not offsets[j]<=t<offsets[j]+arities[j]: return None
        children[j].append(t-offsets[j])
    return tuple(tuple(c) for c in children)
counts={'inverse_request_cases':0,'identity_obstruction_pairs':0,'associativity_cases':0}
for n in range(4):
    for k in range(4):
        for p in partitions(n,k):
            for arities in product(range(3),repeat=k):
                cdomains=[partitions(p.count(j),arities[j]) for j in range(k)]
                forward={substitute(p,k,cs,arities):cs for cs in product(*cdomains)}
                for target in partitions(n,sum(arities)):
                    inverse=inverse_request(p,k,target,arities)
                    assert (inverse is not None)==(target in forward)
                    if inverse is not None:
                        assert inverse==forward[target]
                        assert substitute(p,k,inverse,arities)==target
                    counts['inverse_request_cases']+=1
            # For complete parallel edgeless profiles, boundary forgetting is valid
            # but an identity skeleton cannot change the outer partition.
            ident=tuple(tuple(0 for _ in range(p.count(j))) for j in range(k))
            assert substitute(p,k,ident,(1,)*k)==p
            for q in partitions(n,k):
                if q!=p and sizes(q,k)==sizes(p,k):
                    assert inverse_request(p,k,q,(1,)*k) is None
                    counts['identity_obstruction_pairs']+=1
# Genuine enabled nullary child and repeated empty occurrences.
p=(0,2); arities=(1,0,1)
assert substitute(p,3,((0,),(),(0,)),arities)==(0,1)
assert inverse_request(p,3,(0,1),arities)==((0,),(),(0,))
assert partitions(0,0)==[()] and partitions(1,0)==[]
# Independent nested flattening agrees with sequential substitution.
for n in range(4):
    for p in partitions(n,2):
        for cs in product(partitions(p.count(0),2),partitions(p.count(1),2)):
            flat=substitute(p,2,cs,(2,2))
            for ds in product(*(partitions(flat.count(i),2) for i in range(4))):
                seq=substitute(flat,4,ds,(2,)*4)
                nested=tuple(substitute(cs[j],2,ds[2*j:2*j+2],(2,2)) for j in range(2))
                assert seq==substitute(p,2,nested,(4,4))
                counts['associativity_cases']+=1
# Scalars illustrate that contraction is not bijective on local forest data.
M=(0,1)
for root in M:
    fibre={(a,b) for a,b in product(M,repeat=2) if (a+b)%2==root}
    assert len(fibre)==2
counts['noninjective_scalar_product_fibres']=2
# Induced-subgraph checks on every undirected ordered graph through four vertices.
def edges_from_mask(n,mask):
    pairs=[(a,b) for a in range(n) for b in range(a+1,n)]
    return frozenset(e for j,e in enumerate(pairs) if mask>>j&1)
def induced(edges,verts):
    return frozenset((a,b) for a in range(len(verts)) for b in range(a+1,len(verts))
                     if (verts[a],verts[b]) in edges)
graph_cases=0
for n in range(5):
    for mask in range(1<<(n*(n-1)//2)):
        edges=edges_from_mask(n,mask)
        for flat in partitions(n,4):
            outer=tuple(j//2 for j in flat)
            for j in range(2):
                vertices=tuple(v for v in range(n) if outer[v]==j)
                local_edges=induced(edges,vertices)
                for k in range(2):
                    inner_local=tuple(a for a,v in enumerate(vertices) if flat[v]==2*j+k)
                    actual=tuple(vertices[a] for a in inner_local)
                    assert induced(local_edges,inner_local)==induced(edges,actual)
            graph_cases+=1
counts['ordered_graph_nested_induction_cases']=graph_cases
print(json.dumps({'status':'PASS','checks':counts},indent=2))

"""Finite regression checks; mathematical proofs are in the companion note."""
from itertools import product
import json
from pathlib import Path

def compose(R,S):
    return {(a,c) for a,b in R for b2,c in S if b==b2}
def abstract(R,qsrc,qtgt):
    return {(qsrc[a],qtgt[b]) for a,b in R}
def partitions(xs):
    if not xs:
        yield []
        return
    x,*rest=xs
    for p in partitions(rest):
        yield [{x}]+[set(b) for b in p]
        for i in range(len(p)):
            q=[set(b) for b in p];q[i].add(x);yield q

def qmap(p):return {x:i for i,b in enumerate(p) for x in b}
def powerset(edges):
    for bits in product((0,1),repeat=len(edges)):
        yield {e for e,take in zip(edges,bits) if take}
def exact_middle(R,S,q):
    prod={(a,q[b],c) for a,b in R for b2,c in S if q[b]==q[b2]}
    actual={(a,q[b],c) for a,b in R for b2,c in S if b==b2}
    return prod==actual
A=range(2);B=range(3);C=range(2)
qs=[qmap(p) for p in partitions(list(B))]
checks=0
for R in powerset(list(product(A,B))):
  for S in powerset(list(product(B,C))):
    E=compose(R,S)
    K={(b,d) for b in B for d in B if all((a,c) in E for a,b1 in R for d1,c in S if b1==b and d1==d) and all((a,c) in E for a,d1 in R for b1,c in S if b1==b and d1==d)}
    safe=[]
    for q in qs:
      Q={(b,d) for b in B for d in B if q[b]==q[d]}
      actual=compose(abstract(R,{a:a for a in A},q),abstract(S,q,{c:c for c in C}))==E
      assert actual==(Q<=K)
      if actual:safe.append(Q)
      checks+=1
    greatest=[Q for Q in safe if all(P<=Q for P in safe)]
    trans=all((b,e) in K for b,d in K for d2,e in K if d==d2)
    assert bool(greatest)==trans
# No greatest safe quotient.
R={(0,0),(1,0),(0,1),(0,2)}
S={(0,0),(1,0),(2,0),(2,1)}
E=compose(R,S)
q01={0:0,1:0,2:1};q12={0:0,1:1,2:1};qall={0:0,1:0,2:0}
assert exact_middle(R,S,q01) and exact_middle(R,S,q12)
assert not exact_middle(R,S,qall)
assert (1,1) not in E
# Two individually safe boundary abstractions, unsafe together.
R={(0,0),(1,1),(1,2)}
T={(0,2),(1,1),(2,0)}
S={(0,0),(1,1),(2,1)}
id2={i:i for i in range(2)};id3={i:i for i in range(3)}
qB={0:0,1:0,2:1};qC={0:0,1:0,2:1}
E=compose(compose(R,T),S)
EB=compose(compose(abstract(R,id2,qB),abstract(T,qB,id3)),S)
EC=compose(compose(R,abstract(T,id3,qC)),abstract(S,qC,id2))
EBC=compose(compose(abstract(R,id2,qB),abstract(T,qB,qC)),abstract(S,qC,id2))
assert E==EB==EC=={(0,1),(1,0),(1,1)}
assert EBC-E=={(0,0)}
assert exact_middle(R,compose(T,S),qB)
assert exact_middle(compose(R,T),S,qC)
# Explicit apparent path with empty concrete realization.
fibres=[{0},{0,1},{0,1},{0}]
reach={0};prefixes=[sorted(reach)]
for rel,fibre in zip([R,T,S],fibres[1:]):
    reach={b for a,b in rel if a in reach}&fibre
    prefixes.append(sorted(reach))
assert prefixes==[[0],[0],[],[]]
result={'endpoint_criterion_cases':checks,'coarsest_criterion_relation_pairs':64*64,'no_coarsest_example':'PASS','simultaneous_abstraction_example':'PASS','false_path_prefix_reachability':prefixes,'scope':'All 2-by-3 and 3-by-2 relation pairs and all five three-element interface partitions; no general-network exhaustive claim.'}
Path(__file__).with_name('check_wiring_exactness_results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))

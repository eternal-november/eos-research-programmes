#!/usr/bin/env python3
"""Finite graph/retained-record controls, not a proof of arbitrary path coherence."""
import json
from itertools import product
from pathlib import Path
G=frozenset({(1,2),(3,4),(0,5),(2,3)})
blocks=[(0,),(1,2),(3,4),(5,)]
def induced(vertices):
    ix={v:i for i,v in enumerate(vertices)}
    return (len(vertices),tuple(sorted((ix[a],ix[b]) for a,b in G if a in ix and b in ix)))
assert induced(blocks[1])==induced(blocks[2])==(2,((0,1),))
assert sorted(v for b in blocks for v in b)==list(range(6))
assert (0,5) in G and not any(0 in b and 5 in b for b in blocks)
def refine_at(i):
    return blocks[:i]+[(v,) for v in blocks[i]]+blocks[i+1:]
assert refine_at(1)!=refine_at(2)
def mul(x,y,n=5):
    a,b=x;c,d=y
    return ((a+(-1 if b else 1)*c)%n,(b+d)%2)
assert [mul((1,1),z) for z in [(2,0),(3,1)]]==[(4,1),(3,0)]
assert [mul((1,0),z) for z in [(2,0),(3,1)]]==[(3,0),(4,1)]
assert mul((1,1),(2,0))[0] != (1+2)%5
# Exact parent/children twist is joint: one outer is reused for all children.
labels=list(product(range(5),range(2)))
star_cases=0
for parent,left,right in product(labels,repeat=3):
    a,b=parent;c,d=left;e,f=right
    roots=[mul(parent,left),mul(parent,right)]
    transported=[a,((-1 if b else 1)*c)%5,((-1 if b else 1)*e)%5]
    assert [(a+transported[j+1])%5 for j in range(2)]==[z[0] for z in roots]
    recovered=[(((-1 if b else 1)*transported[1])%5,d),(((-1 if b else 1)*transported[2])%5,f)]
    assert recovered==[left,right]
    star_cases+=1
# Iterated marked chain, retaining all three original factors. Prefix untwist
# followed by inverse must recover every intermediate edge, not only product.
chain_cases=0
for x,y,z in product(labels,repeat=3):
    pref=0;ts=[];bs=[]
    for a,b in [x,y,z]:
        ts.append(((-1 if pref else 1)*a)%5);bs.append(b);pref=(pref+b)%2
    assert mul(mul(x,y),z)==mul(x,mul(y,z))==(sum(ts)%5,sum(bs)%2)
    pref=0;recovered=[]
    for t,b in zip(ts,bs):
        recovered.append((((-1 if pref else 1)*t)%5,b));pref=(pref+b)%2
    assert recovered==[x,y,z]
    chain_cases+=1
# Different marked records flatten to same unit: MUST remain distinct records.
unit=(0,0)
marked1=[unit,unit];marked2=[(0,1),(0,1)]
assert marked1!=marked2 and mul(*marked1)==mul(*marked2)==unit
# Full original-slot tuples distinguish deletion of first vs second empty input.
source=[(),(),(0,)]
forest1=[[],[()],[ (0,) ]];forest2=[[()],[],[ (0,) ]]
assert forest1!=forest2
assert [x for entry in forest1 for x in entry]==[x for entry in forest2 for x in entry]==[(),(0,)]
# A0 absorbing yields parallel Ref arrows (entry1 vs entry0), same root endpoint.
def zero_monoid(x,y):return x*y
assert zero_monoid(0,1)==zero_monoid(0,0)==0 and 1!=0
# Mixed-MIn invariant: distribution uses actual partition vertex cardinalities.
for j in range(3):
    assert (6*j)%3==sum(len(U)*j for U in blocks)%3
assert 1%3!=2%3 # Bs Aa versus Aa^2 Bs at one-vertex colour
report={'status':'PASS','graph_vertices':6,'retained_cross_edges':len(G),
'nonidentity_interface_profile':['h:0->1','id_1','id_1','k:1->2'],
'repeated_induced_component':induced(blocks[1]),'joint_star_cases':star_cases,
'retained_three_factor_chain_cases':chain_cases,
'negative_controls':['naive_A_projection','merge_repeated_occurrences','forget_marked_inverse_factors','replace_original_slot_tuple_by_endpoint','replace_entry_label_by_total_product','omit_mixed_sorting_MIn'],
'limit':'finite semantic/weight fixtures; no executable general rewriting or path-completion engine'}
Path(__file__).with_suffix('.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))

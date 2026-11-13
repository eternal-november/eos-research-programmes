#!/usr/bin/env python3
"""Exact finite regression tests for the paper, not substitutes for its proofs."""
from fractions import Fraction as F
from itertools import product
import json
from pathlib import Path

def compose(h,k):
    out={}
    for a,entries in h.items():
        out[a]={}
        for x,(p,bs) in entries.items():
            for ys in product(*(tuple(k[b]) for b in bs)):
                w=p; ds=[]
                for b,y in zip(bs,ys):
                    q,cs=k[b][y]; w*=q; ds+=cs
                out[a][(x,ys)]=(w,ds)
    return out

def normalized(h):
    return all(sum((p for p,_ in entries.values()),F(0))==1 and all(p>0 for p,_ in entries.values()) for entries in h.values())

def assert_measure_map(source,target,f):
    masses={t:F(0) for t in target}
    for s,(p,output) in source.items():
        t=f(s); masses[t]+=p
        assert output==target[t][1]
    assert all(masses[t]==target[t][0] for t in target)

h={'a':{'x0':(F(2,3),['b','b']),'x1':(F(1,3),[])}}
k={'b':{'y0':(F(1,4),['c']),'y1':(F(3,4),['c','c'])}}
l={'c':{'z0':(F(1,3),[]),'z1':(F(2,3),['d'])}}
left=compose(compose(h,k),l)
right=compose(h,compose(k,l))
assert normalized(left) and normalized(right)

def assoc(sample):
    (x,ys),zs=sample
    bs=h['a'][x][1]; i=0; nested=[]
    for b,y in zip(bs,ys):
        n=len(k[b][y][1]); nested.append((y,tuple(zs[i:i+n])));i+=n
    assert i==len(zs)
    return x,tuple(nested)

assert_measure_map(left['a'],right['a'],assoc)
assert len({assoc(s) for s in left['a']})==len(right['a'])
# Genuine noninvertible grade cells and distinct parallel cells.
p2={'a':{'0':(F(1,2),['b','b']),'1':(F(1,2),['b','b'])}}
p1={'a':{'*':(F(1),['b','b'])}}
r2={'b':{'0':(F(1,2),['c']),'1':(F(1,2),['c'])}}
r1={'b':{'*':(F(1),['c'])}}
assert_measure_map(p2['a'],p1['a'],lambda x:'*')
assert_measure_map(p2['a'],p2['a'],lambda x:x)
assert_measure_map(p2['a'],p2['a'],lambda x:'1' if x=='0' else '0')
assert_measure_map(compose(p2,r2)['a'],compose(p1,r1)['a'],lambda xy:('*',tuple('*' for _ in xy[1])))
# Two repeated occurrences have independent coordinates, including unequal samples.
repeated=compose(p1,r2)['a']
assert len(repeated)==4
assert ('*',('0','1')) in repeated and ('*',('1','0')) in repeated
# A noninjective pure relabeling merges labels, not positions.
labels=['b0','b1']; relabel=lambda b:'b'
assert list(map(relabel,labels))==['b','b']
before=list(product(('0','1'),('0','1')))
after=list(product(*(('0','1') for _ in map(relabel,labels))))
assert before==after and len(after)==4
# Empty output has exactly the inherited context sample and no extra random sample.
empty=compose({'a':{'x':(F(1),[])}},r2)
assert empty=={'a':{('x',()):(F(1),[])}}
result={'status':'passed','arithmetic':'exact fractions','associativity_left_sample_count':len(left['a']),
 'associativity_right_sample_count':len(right['a']), 'checks':['normalization and full support','variable-list-length associator is weight/output preserving bijection','empty list','independent repeated occurrences','noninjective pure relabeling retains positions','noninvertible measure-preserving grade map','two distinct parallel grade automorphisms','horizontal composition of noninvertible cells'],
 'scope':'Finite regression examples only. General coherence and global weak bridge are proved in the TeX paper and proof notes.'}
p=Path(__file__).resolve().parent/'probability_list_regression.json'
p.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))

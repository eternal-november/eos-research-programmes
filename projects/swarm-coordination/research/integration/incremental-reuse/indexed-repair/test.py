"""Stateful receiver tested against full construction and prior exact indexes."""
from collections import defaultdict
from hashlib import sha1
from pathlib import Path
from random import Random
from itertools import product
import sys,json
src=Path(sys.argv[1]).resolve()
for row in Path(__file__).with_name('SOURCE.tsv').read_text().splitlines():
    p,h=row.split('\t');b=(src/p).read_bytes()
    assert sha1(f'blob {len(b)}\0'.encode()+b).hexdigest()==h
sys.path.insert(0,str(src))
from reuse import Graph,Edits,Fact,Observation,full,witnesses,validate_path,new_graph,update
from direct_incremental import update_with_witnesses
from scenarios import instances,large,cost_cases
import plant
from dependency import Producer
from indexed import Indexed
LABELS=('safety','deadline')

def nonempty(o):
    return {k for k,v in o.items() if v}

def info(m):
    return {k:{a:set(v) for a,v in row.items() if v} for k,row in m.items() if row}

def cmp(g,I,oracle,other):
    assert I.out==g.out and I.facts==g.facts and I.roots==g.roots
    assert I.rev==g.rev
    assert set(I.cache.parent)==set(oracle.parent)==set(other.parent)
    assert nonempty(I.cache.bad)==nonempty(oracle.bad)
    assert {k:v for k,v in I.cache.bad.items() if v}=={k:v for k,v in oracle.bad.items() if v}
    assert info(I.cache.views)==info(oracle.views)
    assert I.cache.conflicts==oracle.conflicts
    w=witnesses(I.cache,LABELS)
    assert nonempty(w)==nonempty(witnesses(oracle,LABELS))==nonempty(witnesses(other,LABELS))
    for k,trace in w.items():
        if not trace:continue
        if k=='realizability':
            p,q=trace
            assert validate_path(g,p) and validate_path(g,q)
            a,b=(g.facts[s[-1]].obs for s in (p,q))
            assert a[:3]==b[:3] and a.action!=b.action
        else:
            assert validate_path(g,trace) and k in g.facts[trace[-1]].bad
    check=defaultdict(set)
    for v,p in I.cache.parent.items():
        if p is None:
            assert v in g.roots
        else:
            assert p in I.cache.parent and v in g.out[p]
            check[p].add(v)
    assert {k:x for k,x in I.children.items() if x}==dict(check)

def change(I,g,c,e):
    count=I.update(e)
    fresh,bw=full(new_graph(g,e))
    actual,work,old=update_with_witnesses(g,c,e)
    cmp(actual,I,fresh,work)
    return actual,work,dict(persistent=count,old_index_worklist=old,cold=bw)

named={}
for name,g,e,w in instances:
    i=Indexed(g)
    new,c,cost=change(i,g,full(g)[0],e)
    assert nonempty(witnesses(c,LABELS))==w
    named[name]=cost

counts={}
for name,e in cost_cases.items():
    i=Indexed(large)
    new,c,w=change(i,large,full(large)[0],e)
    counts[name]=w

from fixture import modeled

h,P=modeled(4096)
i=Indexed(h);c=full(h)[0]
pipeline=[]
for changed,verdict in [
 ({'choose_backup':True},set()),
 ({'main_bound':True},set()),
 ({'other_bound':True},{'safety'}),
 ({'late':True},{'safety','deadline'}),
 ({'other_bound':False},{'deadline'}),
]:
    rows,dirty=P.update(changed,{})
    h,c,w=change(i,h,c,Edits(out=rows))
    assert nonempty(witnesses(i.cache,LABELS))==verdict
    pipeline.append(dict(cell=list(changed),producer_rechecks=len(dirty),emitted=len(rows),
                         verdict=sorted(verdict),measure=w))
assert pipeline[0]['measure']['persistent']['out_rows_read']==0
assert pipeline[1]['measure']['persistent']['out_rows_read']==0
assert pipeline[1]['producer_rechecks']==0
assert pipeline[2]['measure']['persistent']['out_rows_read']==12
assert pipeline[2]['measure']['old_index_worklist']['tree_vertices_indexed']==4101

rng=Random(89372)
nn=0
for n,q in product(range(1,20),(0,.06,.18,.35,.72)):
    for _ in range(25):
        xs=[f'{k:03}' for k in range(n)]
        randrow=lambda:frozenset(x for x in xs if rng.random()<q)
        randroot=lambda:frozenset(x for x in xs if rng.randrange(8)==0)
        def marker():
            flags=frozenset(x for x in LABELS if rng.randrange(9)==0)
            d=Observation('a',str(rng.randrange(2)),str(rng.randrange(4)),str(rng.randrange(3)))
            return Fact(flags,d if rng.randrange(2)==0 else None)
        g=Graph(randroot(),{x:randrow() for x in xs},{x:marker() for x in xs})
        i=Indexed(g);c=full(g)[0]
        for step in range(3):
            e=Edits(roots=randroot() if rng.randrange(4)==0 else None,
                    out={x:randrow() for x in xs if rng.randrange(4)==0},
                    facts={x:marker() for x in xs if rng.randrange(4)==0})
            g,c,_=change(i,g,c,e);nn+=1
print(json.dumps(dict(named=named,bench=counts,pipeline=pipeline,chained_edits=nn),
                 sort_keys=True,indent=2))

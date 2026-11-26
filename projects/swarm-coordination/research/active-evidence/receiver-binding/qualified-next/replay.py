"""Native whole-world receipts and exact root-hypothesis refinement."""
from itertools import product
from pathlib import Path
import json,subprocess,sys
from filter import History,check
sys.path.insert(0,str(Path(sys.argv[2]).resolve()))
from reuse import Graph,Fact,Edits,full,update,witnesses,validate_path

def direct(c,q,p,x,y,z,same,shared,drop):
    rb=q if shared else 0
    spent=x if x<=p else 0
    tx=spent if same else 0
    seen=(x<=p and not drop and rb+x<=p)
    if seen:rb+=x
    call=[]
    for k in (y,z):
        funded=tx+k<=c
        if funded:tx+=k
        got=funded and rb+k<=c
        if got:rb+=k
        call.append(got)
    return (int(seen),*map(int,call),spent,tx,rb)

checks=[]
for c in range(1,7):
    for q,p,d,same,shared,drop in product(range(c+1),range(1,c+1),range(1,c+1),(0,1),(0,1),(0,1)):
        if same and p!=c:continue
        for x in range(1,p+2):
            for y,z in ((d,1),(1,d),(d,d)):
                checks.append((c,q,p,x,y,z,same,shared,drop))
checks.extend((5,2,2,1,2,z,0,a,d) for z,a,d in product((2,3),(0,1),(0,1)))
s=''.join(' '.join(map(str,row))+'\n' for row in checks)
result=subprocess.run([sys.argv[1]],input=s,text=True,stdout=subprocess.PIPE,check=True)
rows={}
for q,s in zip(checks,result.stdout.splitlines(),strict=True):
    y=tuple(map(int,s.split()))
    assert direct(*q)==y,(q,y,direct(*q))
    rows[q]=y

def world(q):
    y=rows[q];_,_,_,_,_,_,_,alias,drop=q
    return History("shared" if alias else "distinct",*map(bool,y[:3]),
                   f"alias{alias}-drop{drop}")

labels=('old','next')
def build(worlds):
    nodes={}
    info={}
    for w in worlds:
        v=w.source
        nodes[v]=frozenset({v+'-after'})
        nodes[v+'-after']=frozenset()
        info[v]=Fact()
        info[v+'-after']=Fact(frozenset(k for k,p in zip(labels,(w.old_receipt,w.next_receipt)) if not p))
    return Graph(frozenset(w.source for w in worlds),nodes,info)

def classify_graph(g,c,sources):
    graph,cache,cost=update(g,c,Edits(roots=frozenset(sources)))
    direct_cache,_=full(graph)
    assert set(cache.parent)==set(direct_cache.parent)
    found=witnesses(cache,labels)
    for l in labels:
        if found[l] is not None:
            assert validate_path(graph,found[l]) and l in graph.facts[found[l][-1]].bad
    return found,cost

def scenario(params,may_drop):
    worlds=[world((*params,a,d)) for a,d in product((0,1),range(1+may_drop))]
    g=build(worlds)
    cache,_=full(g)
    out={}
    for seen in (False,True):
        kind,h=check(worlds,seen)
        keep={w.source for w in h}
        w,cost=classify_graph(g,cache,keep)
        bad={w0.source for w0 in h if not (w0.old_receipt and w0.next_receipt)}
        assert (kind=='inconsistent')==(not keep)
        if keep:
            assert (kind=='carries')==(not bad)
            assert (kind=='refuted')==(bad==keep)
            assert (kind=='undecided')==bool(bad and keep-bad)
            assert (w['old'] is None)==all(t.old_receipt for t in h)
            assert (w['next'] is None)==all(t.next_receipt for t in h)
        out[str(seen)]=dict(judgment=kind,program_witnesses=w,reach_work=cost,
                           complete_histories=[t.__dict__ for t in h])
    return out

ranks={}
for due,drop in product((2,3),(False,True)):
    key=f"next{due}-drop{drop}"
    ranks[key]=scenario((5,2,2,1,2,due,0),drop)
assert ranks['next2-dropFalse']['True']['judgment']=='carries'
assert ranks['next2-dropFalse']['False']['judgment']=='refuted'
assert ranks['next2-dropTrue']['False']['judgment']=='undecided'
assert ranks['next3-dropTrue']['True']['judgment']=='refuted'
assert ranks['next3-dropTrue']['False']['judgment']=='undecided'
print(json.dumps(dict(variants=ranks, native_rows=len(checks),
       direct_parameters=len(rows)),sort_keys=True,indent=2))

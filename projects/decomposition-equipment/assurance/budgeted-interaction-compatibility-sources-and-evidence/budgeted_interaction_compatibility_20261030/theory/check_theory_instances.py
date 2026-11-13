#!/usr/bin/env python3
"""Exact regression witnesses for the theorem; not main workload evidence."""
import itertools as it, json, hashlib
from pathlib import Path

BAGS=((0,1),(1,2),(2,3)); EDGES=((0,1),(1,2)); TUPLES=tuple(it.product((0,1),repeat=2))
def proj(t,b,sub): return tuple(t[b.index(i)] for i in sub)
def supported(bags,rels,edges):
    adj={v:[] for v in range(len(bags))}
    for u,v in edges: adj[u].append(v); adj[v].append(u)
    cache={}
    def msg(v,u):
        if (v,u) in cache:return cache[v,u]
        sep=tuple(sorted(set(bags[v])&set(bags[u])))
        good=[]
        for t in rels[v]:
            if all(proj(t,bags[v],tuple(sorted(set(bags[v])&set(bags[k])))) in msg(k,v) for k in adj[v] if k!=u):good.append(t)
        cache[v,u]={proj(t,bags[v],sep) for t in good};return cache[v,u]
    out=[]
    for v,b in enumerate(bags):
        out.append({t for t in rels[v] if all(proj(t,b,tuple(sorted(set(b)&set(bags[k])))) in msg(k,v) for k in adj[v])})
    return out

def worlds(rels):return [w for w in it.product((0,1),repeat=4) if all(tuple(w[i] for i in b) in r for b,r in zip(BAGS,rels))]

join_checks=0; crs_checks=0; nonempty=0
allrels=[{TUPLES[i] for i in range(4) if mask>>i&1} for mask in range(1,16)]
for rels in it.product(allrels,repeat=3):
    ws=worlds(rels); sup=supported(BAGS,rels,EDGES)
    assert sup==[{tuple(w[i] for i in b) for w in ws} for b in BAGS]
    join_checks+=1
    if not ws: continue
    nonempty+=1
    # Check paired-world support reduction for a genuinely local record.
    # Output retains both parity and first-bit physical transition.
    F=lambda w:(w[0]^w[1],w[0])
    for D in ((),(0,),(1,),(0,1)):
        expected=all(F(w)==F(z) for w in ws for z in ws if all(w[i]==z[i] for i in D))
        tbags=tuple(b+tuple(i+4 for i in b) for b in BAGS)
        tr=[]
        for b,r in zip(BAGS,rels):
            tr.append({x+y for x in r for y in r if all(x[b.index(i)]==y[b.index(i)] for i in D if i in b)})
        # Search for a disagreement at the first bag in the doubled join tree.
        tr[0]={t for t in tr[0] if (t[0]^t[1],t[0])!=(t[2]^t[3],t[2])}
        actual=not supported(tbags,tr,EDGES)[0]
        assert actual==expected
        crs_checks+=1

# Exact probe/service game. Hazard is evaluated against ALL compatible worlds.
def win(K,t,diagnose=False):
    if diagnose and K==frozenset({'broken'}):return True
    if t<=0:return False
    # Service completion must be correct for every world.
    if any(K==frozenset({m}) for m in ('L','R')):return True
    # Probe costs two; outcomes reveal the actual world.
    if t>=2 and all(win(frozenset({m}),t-2,diagnose) for m in K):return True
    return False
assert not win(frozenset({'L','R'}),2)
assert win(frozenset({'L','R'}),3)
assert not win(frozenset({'L','R','broken'}),3)
assert win(frozenset({'L','R','broken'}),3,True)
assert not win(frozenset({'L','R','broken'}),2,True)
# Correlation omission witness; identical marginal support, different certified action.
eq={(0,0),(1,1)};ne={(0,1),(1,0)};rect=set(TUPLES)
def actions(K):return [label for label,p in [('same',lambda a,b:a==b),('different',lambda a,b:a!=b)] if all(p(*w) for w in K)]
assert actions(eq)==['same'] and actions(ne)==['different'] and actions(rect)==[]
assert [{w[i] for w in eq} for i in range(2)]==[{w[i] for w in ne} for i in range(2)]
result={'exact_join_relations_checked':join_checks,'nonempty_relations':nonempty,'doubled_tree_CRS_checks':crs_checks,'budget_and_diagnosis_assertions':5,'correlation_omission_witness':True,'status':'PASS','scope':'finite theorem regressions only; not performance or mission workload results'}
path=Path(__file__).with_name('theory_instance_checks.json');path.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

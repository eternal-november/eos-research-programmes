#!/usr/bin/env python3
"""Exhaust finite resource exactness; no external dependencies.

For every matrix in the stated finite suite and every source budget of
l1 norm <=2, enumerate every target decomposition and its exact lifting
poset. Tests Boolean nonemptiness, Set connectedness, and witness poset
isomorphism independently of the proposed matrix classification.
"""
from itertools import product
from collections import Counter
from pathlib import Path
import json, time

def budgets(m):
    return [r for r in product(range(3), repeat=m) if sum(r)<=2]

def decompositions(r):
    choices=[[(a,b) for a in range(v+1) for b in range(v-a+1)] for v in r]
    return [(tuple(x[0] for x in p),tuple(x[1] for x in p)) for p in product(*choices)]

def mv(C,x):
    return tuple(sum(c*v for c,v in zip(row,x)) for row in C)

def le(x,y): return all(a<=b for a,b in zip(x,y))
def dle(x,y): return le(x[0],y[0]) and le(x[1],y[1])

def component_count(ids, adj):
    unseen=set(ids); count=0
    while unseen:
        count+=1; work=[unseen.pop()]
        while work:
            u=work.pop()
            new=unseen.intersection(adj[u])
            unseen.difference_update(new); work.extend(new)
    return count

def predicted(C):
    d=len(C);m=len(C[0]); cols=[tuple(C[i][j] for i in range(d)) for j in range(m)]
    boolean=all(sum(c)<=1 for c in cols)
    nz=[c for c in cols if sum(c)]
    sets=boolean and len(nz)==len(set(nz))
    witness=sets and len(nz)==m
    return boolean,sets,witness

def inspect(C):
    m=len(C[0]); flags=[True]*3; examples={}; counts=Counter()
    for r in budgets(m):
        src=decompositions(r); trg=decompositions(mv(C,r))
        image=[(mv(C,a),mv(C,b)) for a,b in src]
        adj=[{j for j,y in enumerate(src) if dle(x,y) or dle(y,x)} for x in src]
        for t in trg:
            ids=[j for j,im in enumerate(image) if dle(t,im)]
            cc=component_count(ids,adj)
            counts['fibers']+=1
            if cc==0:
                flags[0]=False;examples.setdefault('empty',{'budget':r,'demand':t})
            if cc!=1:
                flags[1]=False;examples.setdefault('disconnected_or_empty',{'budget':r,'demand':t,'components':cc})
        iso=(len(set(image))==len(src) and set(image)==set(trg)
             and all(not dle(image[i],image[j]) or dle(src[i],src[j]) for i in range(len(src)) for j in range(len(src))))
        if not iso:
            flags[2]=False;examples.setdefault('witness_non_equivalence',{'budget':r,'source_objects':len(src),'target_objects':len(trg)})
        counts['budgets']+=1
    return tuple(flags),examples,counts

def main():
    started=time.time(); counts=Counter(); errors=[]; examples=[]
    suites=[(d,m,(0,1,2)) for d in (1,2) for m in (1,2)]+[(3,3,(0,1))]
    for d,m,entries in suites:
        for flat in product(entries,repeat=d*m):
            C=tuple(tuple(flat[i*m+j] for j in range(m)) for i in range(d))
            actual,ex,cnt=inspect(C); expected=predicted(C)
            counts.update(cnt);counts['matrices']+=1
            counts['bool_exact']+=actual[0];counts['set_exact']+=actual[1];counts['witness_exact']+=actual[2]
            if actual!=expected: errors.append({'matrix':C,'expected':expected,'actual':actual,'examples':ex})
    for C in (((2,),),((1,1),),((1,0),),((1,), (0,))):
        actual,ex,cnt=inspect(C); examples.append({'matrix':C,'exactness':actual,'obstructions':ex})
    result={'suite':'All 1x1,1x2,2x1,2x2 entries 0..2; all 3x3 entries 0..1; every source budget with l1<=2; all binary target decompositions',
            'counts':dict(counts),'errors':errors,'examples':examples,'seconds':round(time.time()-started,3),
            'scope':'Finite independent enumeration, not a substitute for the universal proof.'}
    Path(__file__).with_name('resource_checks.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
    if errors: raise SystemExit(1)
if __name__=='__main__': main()

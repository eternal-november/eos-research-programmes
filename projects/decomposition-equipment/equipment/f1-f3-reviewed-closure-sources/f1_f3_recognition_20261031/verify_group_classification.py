#!/usr/bin/env python3
"""Exhaustive literal R/E check, n<=4. No timing-dependent stop or external dependencies."""
if not __debug__:
    raise RuntimeError("Verification requires assertions; do not use -O or PYTHONOPTIMIZE.")

import itertools as it
import json
from pathlib import Path


def compose(p,q): return tuple(p[q[i]] for i in range(len(p)))
def closure(gens,n):
    identity=tuple(range(n)); found={identity}; todo=[identity]
    while todo:
        p=todo.pop()
        for g in gens:
            q=compose(p,g)
            if q not in found: found.add(q); todo.append(q)
    return frozenset(found)
def subgroups(n):
    perms=list(it.permutations(range(n))); trivial=frozenset([tuple(range(n))])
    found={trivial}; todo=[trivial]
    while todo:
        h=todo.pop()
        for p in perms:
            if p not in h:
                k=closure(tuple(h)+(p,),n)
                if k not in found: found.add(k); todo.append(k)
    return sorted(found,key=lambda h:(len(h),sorted(h)))
def pairs(n): return list(it.combinations(range(n),2))
def edges(n,mask): return {p for k,p in enumerate(pairs(n)) if mask>>k&1}
def induced(n,mask,u):
    e=edges(n,mask)
    return sum(1<<k for k,(i,j) in enumerate(pairs(len(u))) if (u[i],u[j]) in e)
def subsets(n):
    return [u for k in range(n) for u in it.combinations(range(n),k)]
def compatible(n,mask,h,children):
    # Direct R and E only. No graph-component, automorphism, inversion,
    # interval, or flag criterion occurs in this predicate.
    for u in subsets(n):
        child=children[(len(u),induced(n,mask,u))]
        if child is None: return False
        for g in h:
            gu=tuple(sorted(g[i] for i in u))
            if induced(n,mask,u)!=induced(n,mask,gu): return False
            rank={v:i for i,v in enumerate(gu)}
            rho=tuple(rank[g[i]] for i in u)
            if rho not in child: return False
        for q in child:
            ext=list(range(n))
            for i,v in enumerate(u): ext[v]=u[q[i]]
            if tuple(ext) not in h: return False
    return True

def predicted(n,mask,edgeflag,nonedgeflag):
    ee=edges(n,mask); pp=pairs(n)
    selected={p for p in pp if (edgeflag if p in ee else nonedgeflag)}
    unseen=set(range(n)); blocks=[]
    while unseen:
        component={min(unseen)}; todo=list(component); unseen-=component
        while todo:
            a=todo.pop()
            adjacent={b for b in unseen if tuple(sorted((a,b))) in selected}
            unseen-=adjacent; component|=adjacent; todo.extend(adjacent)
        blocks.append(component)
    if edgeflag and nonedgeflag:
        if ee and len(ee)!=len(pp): return None
    elif edgeflag or nonedgeflag:
        for c in blocks:
            if max(c)-min(c)+1!=len(c): return None
            if any(p not in selected for p in it.combinations(sorted(c),2)): return None
    return frozenset(p for p in it.permutations(range(n)) if all({p[i] for i in c}==c for c in blocks))

def main():
    groups={n:subgroups(n) for n in range(5)}
    assert [len(groups[n]) for n in range(5)]==[1,1,2,6,30]
    result={'scope':'All 76 ordered simple graphs on n=0..4; all subgroups of S_n; four edge/nonedge flags. Literal R/E compatibility, then comparison to predicted classification.', 'subgroup_counts':{str(n):len(groups[n]) for n in groups},'flags':{}}
    total=0
    for ef,nf in it.product([False,True],repeat=2):
        children={(0,0):groups[0][0],(1,0):groups[1][0]}
        for mask in range(2): children[(2,mask)]=groups[2][int(ef if mask else nf)]
        summary={}
        for n in range(3,5):
            accepted=0; invalid=0; checks=0
            for mask in range(1<<len(pairs(n))):
                matches=[h for h in groups[n] if compatible(n,mask,h,children)]
                checks+=len(groups[n]); total+=len(groups[n])
                expected=predicted(n,mask,ef,nf)
                assert matches==([] if expected is None else [expected]), (ef,nf,n,mask,matches,expected)
                children[(n,mask)]=matches[0] if matches else None
                accepted+=bool(matches); invalid+=not bool(matches)
            summary[str(n)]={'graphs':accepted+invalid,'unique_compatible_group':accepted,'no_compatible_group':invalid,'candidate_group_checks':checks}
        for (n,mask),h in children.items():
            assert h==predicted(n,mask,ef,nf)
        result['flags'][f'edge={int(ef)},nonedge={int(nf)}']=summary
    result['candidate_group_checks_n3_n4']=total
    result['status']='PASS: exact uniqueness/nonexistence classification for every checked graph and flag'
    dest=Path(__file__).with_name('verify_group_classification_results.json')
    dest.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__': main()

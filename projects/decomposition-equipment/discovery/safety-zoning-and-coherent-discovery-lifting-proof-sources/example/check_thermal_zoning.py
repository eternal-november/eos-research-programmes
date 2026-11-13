#!/usr/bin/env python3
"""Finite deterministic owner model; exact CFG relation saturation, not bounded paths."""
from itertools import product
import json
B=list(product(range(2), repeat=3)) # heat, reserve, regime
# Every component is a DISCRETE graph whose states are one-shot episode records.
components={}
productions={}
for n in range(2):
    a,b,c,d=(0,1,n),(1,1,n),(0,0,n),(1,0,n)
    components[f'H{n}']=[(a,b),(c,d)]
    components[f'C{n}']=[(b,c)]
    components[f'I{n}']=[(s,s) for s in B if s[2]==n]
    components[f'R{n}']=[(a,d)]
    productions[f'H{n}']=[(f'I{n}',f'H{n}')]
    productions[f'R{n}']=[(f'H{n}',f'C{n}',f'H{n}')]

def reachable_colors(root):
    colors={root}
    while True:
        new=colors|{e for c in colors for p in productions.get(c,[]) for e in p}
        if new==colors:return colors
        colors=new

def compose(A,C):
    by={}
    for (v,w),p in C.items():by.setdefault(v,[]).append((w,p))
    out={}
    for (u,v),p in A.items():
        for w,r in by.get(v,[]):out.setdefault((u,w),p+r)
    return out

def fullness(root,q):
    records=components[root]; m=len(records)
    left=tuple(r[0] for r in records); right=tuple(r[1] for r in records)
    colors=reachable_colors(root)
    maps={e:list(product(range(len(components[e])),repeat=m)) for e in colors}
    boundary={left}
    for e in colors:
        boundary.update(tuple(components[e][i][1] for i in f) for f in maps[e])
    states=[(h,d) for h in boundary for d in (False,True)]
    rel={e:{} for e in colors}
    for e in colors:
        lookup={}
        for f in maps[e]:
            l=tuple(components[e][i][0] for i in f)
            r=tuple(components[e][i][1] for i in f)
            lookup.setdefault(tuple(map(q,l)),[]).append((l,r,f))
        for h,d in states:
            for l,r,f in lookup.get(tuple(map(q,h)),[]):
                rel[e].setdefault(((h,d),(r,d or h!=l)),((e,f),))
    rounds=0
    while True:
        changed=False;rounds+=1
        for e in colors:
            for p in productions.get(e,[]):
                run={ (s,s):() for s in states }
                for leaf in p:run=compose(run,rel[leaf])
                for pair,witness in run.items():
                    if pair not in rel[e]:rel[e][pair]=witness;changed=True
        if not changed:break
    initial=(left,False)
    bad=[]
    for (u,(h,d)),w in rel[root].items():
        if u==initial and tuple(map(q,h))==tuple(map(q,right)) and (d or h!=right):
            bad.append(w)
    return {'full':not bad,'states':len(states),'fixed_point_rounds':rounds,
            'relation_pairs':sum(map(len,rel.values())),
            'short_counterexample':min(bad,key=len) if bad else None}

def step(s,action):
    h,c,n=s
    if action=='H' and h==0:return (1,c,n)
    if action=='C' and h==1 and c==1:return (0,0,n)
    if action=='I':return s
    return None

def permissions(word):
    out=set()
    for s in B:
        t=s
        for a in word:
            t=step(t,a)
            if t is None:break
        if t is not None:out.add(s)
    return out

def permission_partition():
    # Partition refinement implements Boolean closure and demonic preimages.
    sig={s:tuple(step(s,a) is not None for a in 'HCI') for s in B}
    def quotient(sig):
        ids={v:i for i,v in enumerate(sorted(set(sig.values())))}
        return {s:ids[v] for s,v in sig.items()}
    classes=quotient(sig);rounds=0
    while True:
        rounds+=1
        nxt=quotient({s:(classes[s],)+tuple(-1 if step(s,a) is None else classes[step(s,a)] for a in 'HCI') for s in B})
        if all((classes[s]==classes[t])==(nxt[s]==nxt[t]) for s in B for t in B):break
        classes=nxt
    return sorted([sorted(s for s in B if classes[s]==i) for i in set(classes.values())]),rounds

if __name__=='__main__':
    atoms,rounds=permission_partition()
    assert len(atoms)==4 and all(len(a)==2 and a[0][:2]==a[1][:2] for a in atoms)
    assert permissions('HCH')=={(0,1,0),(0,1,1)}
    assert permissions('HCHCH')==set()
    results={name:{c:fullness(c,q) for c in sorted(components)}
             for name,q in [('adequate',lambda s:s[:2]),('heat_only',lambda s:s[0])]}
    assert all(r['full'] for r in results['adequate'].values())
    assert not results['heat_only']['R0']['full']
    # Explicit nontrivial source-profile counterexample: second H resets reserve.
    route=[components['H0'][0],components['C0'][0],components['H0'][0]]
    assert all(x[1][0]==y[0][0] for x,y in zip(route,route[1:]))
    assert route[1][1] != route[2][0]
    print(json.dumps({'permission_atoms':atoms,'partition_rounds':rounds,
      'two_aisle_permission':sorted(permissions('HCH')),
      'three_aisle_permission':sorted(permissions('HCHCH')),
      'fullness':results},indent=2))

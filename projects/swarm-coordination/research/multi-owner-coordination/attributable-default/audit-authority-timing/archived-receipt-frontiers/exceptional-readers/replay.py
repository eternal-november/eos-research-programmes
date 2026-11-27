"""Exact residual choice criterion with one exceptional receipt reader."""
from collections import Counter
from itertools import combinations, combinations_with_replacement, product
from pathlib import Path
import importlib.util
import json
import random
import sys
import tempfile

up=Path(sys.argv[1]).resolve()
spec=importlib.util.spec_from_file_location('archive_sources',up/'archived_matcher.py')
V=importlib.util.module_from_spec(spec);spec.loader.exec_module(V)

def allowed(subjects,times,fronts):
    ranked=sorted(subjects,key=lambda i:(-times[i],i))
    need=[times[i] for i in ranked]
    n=len(need)
    c=(sorted(fronts,reverse=True)+[0]*n)[:n]
    bad_original=next((j for j in range(n) if need[j]>c[j]),None)
    if bad_original is None:
        return True,[]
    if any(need[j+1]>c[j] for j in range(n-1)):
        return False,[] # Dropping even the hardest subject is insufficient.
    return False,ranked[:bad_original+1]

def clean_native(root):
    result=V.native(root)
    names=tuple(result['tick_by_subject'])
    times=result['tick_by_subject']
    scopes=[set(row['named']) for row in result['sparse_archives']]
    assert len({len(s) for s in scopes})==1
    slots=[{i for i in names if times[i]<=t} for t in (27,)]
    for X in V.all_subsets(names):
        passed,drop=allowed(X,times,[27])
        for s in scopes:
            assert (passed or bool(s.intersection(drop)))==V.match_order(X,slots+[s])
    return dict(qualified_names=names,native_special_sets=[sorted(x) for x in scopes])

def compressed(T,times,fronts,exceptions):
    values=sorted({c for c in fronts if c>0}|{times[i] for i in T})
    n=len(T); l=len(values); z=len(exceptions)
    S=n+l+z; U=S+1; g=[{} for _ in range(U+1)]; edges=0
    def add(a,b,c):
        nonlocal edges
        assert b not in g[a]
        g[a][b]=c;g[b][a]=0;edges+=1
    levels={v:n+j for j,v in enumerate(values)}
    for a,b in zip(values,values[1:]):add(levels[a],levels[b],n)
    for c,count in sorted(Counter(fronts).items()):
        if c>0:add(levels[c],U,count)
    for j,_ in enumerate(exceptions):add(n+l+j,U,1)
    for k,i in enumerate(T):
        add(S,k,1);add(k,levels[times[i]],1)
        for j,X in enumerate(exceptions):
            if i in X:add(k,n+l+j,1)
    out=0
    while True:
        seen={S:None}; pending=[S]
        for a in pending:
            if a==U:break
            for b,c in g[a].items():
                if c and b not in seen:seen[b]=a;pending.append(b)
        if U not in seen:break
        out+=1;v=U
        while v!=S:
            a=seen[v];g[a][v]-=1;g[v][a]+=1;v=a
    return out==n,edges

def multiple():
    rng=random.Random(919431)
    for _ in range(1024):
        n=rng.randrange(1,8); T=tuple(range(n))
        times={i:rng.randrange(1,6) for i in T}
        c=[rng.randrange(7) for _ in range(rng.randrange(1,5))]
        exceptions=[{i for i in T if rng.randrange(2)} for _ in range(rng.randrange(1,5))]
        base=[{i for i in T if times[i]<=p} for p in c]
        assert compressed(T,times,c,exceptions)[0]==V.match_order(T,base+exceptions)
    T=tuple(range(1,101));c=list(T);times={x:x for x in T}
    exp=[{i for i in T if i%2==0},{77,100}]
    ok,compact=compressed(T,times,c,exp);assert ok
    adjacency=sum(i<=c0 for i in T for c0 in c)+sum(map(len,exp))
    explicit_supply=len(T)+len(c)+len(exp)
    return dict(comparisons=1024,large_compact_edges=compact,
                large_explicit_edges=adjacency+explicit_supply)

def exact():
    check=0;negative=0
    names=(0,1,2,3)
    S=V.all_subsets(names)
    for rs in product(range(1,4),repeat=4):
        times=dict(zip(names,rs))
        for k in range(1,4):
          for cs in combinations_with_replacement(range(4),k):
            base=[{i for i in names if times[i]<=c} for c in cs]
            for X in S:
              enough,drop=allowed(X,times,cs)
              if not enough:
                viewed={i for i in X if V.match_order(tuple(j for j in X if j!=i),base)}
                assert viewed==set(drop)
              for exc in S:
                act=enough or bool(set(exc).intersection(drop))
                exp=V.match_order(X,base+[set(exc)])
                assert act==exp
                negative+=int(not act)
                check+=1
    # Only the top two ranks can repair this first failure.
    p,fixes=allowed((0,1,2),{0:3,1:2,2:1},[3,1])
    assert not p and fixes==[0,1]
    # Even removing the hardest does not yield a feasible prefix.
    p,fixes=allowed((0,1,2),{0:3,1:2,2:1},[1,1])
    assert not p and fixes==[]
    # An exact singleton critical prefix is possible (drop the hardest).
    p,fixes=allowed((0,1,2),{0:4,1:3,2:1},[3,1])
    assert not p and fixes==[0]
    return dict(checked=check, refused=negative)

if __name__=='__main__':
    with tempfile.TemporaryDirectory() as d: n=clean_native(Path(d))
    print(json.dumps(dict(native=n,exhaustive=exact(),several=multiple()),indent=2,sort_keys=True))

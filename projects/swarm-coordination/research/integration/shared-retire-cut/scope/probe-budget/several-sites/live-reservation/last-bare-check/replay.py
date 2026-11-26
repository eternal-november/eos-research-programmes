#!/usr/bin/env python3
"""Compare the last-check criterion with explicit causal policy search."""
from functools import lru_cache
from itertools import product
import json
from random import Random

INF=10**6


def distance(n,E):
    D=[[INF]*n for _ in range(n)]
    for i in range(n):D[i][i]=0
    for i,j in E:D[i][j]=1
    for k,i,j in product(range(n),repeat=3):
        D[i][j]=min(D[i][j],D[i][k]+D[k][j])
    return D


def last_choices(m,W,D,s):
    return [tuple(j for j in range(m) if all(
          y==x or D[i][k]>s or (x^y)>>j&1 for k,y in enumerate(W)))
          for i,x in enumerate(W)]


def oracle(m,W,D,s,h):
    @lru_cache(None)
    def go(b,P,left):
        possible=[i for i,r in enumerate(b) if r>=0]
        if len(possible)==1:
            x=W[possible[0]]
            if all(P>>(2*j+((x>>j)&1))&1 for j in range(m)):return True
        if not left:return False
        ext=tuple(max([-1]+[b[i]-D[i][j] for i in possible]) for j in range(len(W)))
        for g,v in product(range(m),(0,1)):
            for q in (False,True):
                c=tuple(r if (((x>>g)&1)==v)==q else -1 for x,r in zip(W,ext))
                if max(c)<0:continue
                if not go(c,P|(1<<(2*g+v)) if q else P,left-1):break
            else:return True
        return False
    return go((s,)*len(W),0,h)


def simulate(m,W,D,s):
    choices=last_choices(m,W,D,s)
    assert all(choices)
    @lru_cache(None)
    def step(i,b,r,mode,pos,reps,first,mask):
        # One read now. No hidden state is passed to the control decisions.
        if mode=='verify':
            x=W[first]
            g=choices[first][0]
            same=not ((W[i]^x)>>g&1)
            if same:
                assert W[i]==x
                return 1,1
            assert r>0
            child=r-1,'scan',0,0,-1,0
        else:
            g,v=divmod(pos,2)
            ok=((W[i]>>g)&1)==v
            if ok:mask|=1<<pos
            if pos+1<2*m:
                child=(r,'scan',pos+1,reps,first,mask)
            else:
                bits=[(mask>>(2*j))&3 for j in range(m)]
                onehot=all(x in (1,2) for x in bits)
                val=sum((x==2)<<j for j,x in enumerate(bits))
                accepted=onehot and val in W and (first<0 or W[first]==val)
                if not accepted:
                    assert r>0
                    child=(r-1,'scan',0,0,-1,0)
                elif reps==r:
                    child=(r,'verify',0,0,W.index(val),0)
                else:
                    child=(r,'scan',0,reps+1,W.index(val),0)
        out=[step(j,b-D[i][j],*child) for j in range(len(W)) if D[i][j]<=b]
        return (1+max(a for a,c in out),sum(c for a,c in out))
    out=[step(i,s,s,'scan',0,0,-1,0) for i in range(len(W))]
    return max(a for a,c in out),sum(c for a,c in out)


def run():
    rng=Random(528)
    search=accepted=rejected=paths=0
    for _ in range(170):
        m=rng.choice((2,3))
        W=tuple(sorted(rng.sample(range(1<<m),rng.randrange(2,5))))
        E=[(i,j) for i,j in product(range(len(W)),repeat=2) if i!=j and rng.random()<.35]
        D=distance(len(W),E)
        for s in range(3):
            ok=all(last_choices(m,W,D,s))
            if ok:
                limit,seen=simulate(m,W,D,s)
                assert limit<=m*(s+1)*(s+2)+(s+1)
                assert oracle(m,W,D,s,limit)
                accepted+=1
                paths+=seen
            else:
                assert not oracle(m,W,D,s,2*m+4)
                rejected+=1
            search+=1
    det=(0,3)
    assert all(last_choices(2,det,distance(2,[(0,1),(1,0)]),5))
    path=(0,6,3,5)
    DD=distance(4,[(0,1),(1,2),(2,3)])
    assert all(last_choices(3,path,DD,2))
    assert not all(last_choices(3,path,DD,3))
    # Arbitrary difference-set family represented as an outward directed star.
    scope_checks=0
    for m in range(2,7):
        Q=1<<m
        for _ in range(40):
            leaves=tuple(sorted(rng.sample(range(1,Q),rng.randrange(1,min(8,Q)))))
            worlds=(0,)+leaves
            D=distance(len(worlds),[(0,j) for j in range(1,len(worlds))])
            best=min(mask.bit_count() for mask in range(Q) if all(mask&leaf for leaf in leaves))
            full=min(mask.bit_count() for mask in range(Q) if all(
                all(i==k or D[i][k]>1 or mask & (x^y) for k,y in enumerate(worlds))
                for i,x in enumerate(worlds)))
            assert best==full
            scope_checks+=1
    return dict(causal_search_comparisons=search,atomic_scope_star_comparisons=scope_checks,admitted_instances=accepted,
                inadmissible_control_instances=rejected,
                joined_terminating_state_sequences=paths,
                directed_path_radius_two_passes_radius_three_fails=True)


if __name__=="__main__":
    print(json.dumps(run(),indent=2))

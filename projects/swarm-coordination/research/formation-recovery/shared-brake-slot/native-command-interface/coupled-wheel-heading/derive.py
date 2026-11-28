#!/usr/bin/env python3
"""Exact quantized differential-drive viability; no inferred hardware dynamics."""
from functools import lru_cache
from itertools import product
import json
import sys

# Each stored wheel distance is twice its physical distance.
# Body travel and heading follow the exact differential-drive integrals:
# s=(XL+XR)/4, theta=(XR-XL)/(2*wheelbase).
@lru_cache(None)
def speed_paths(u,h,b):
    if h==0:
        return ((),) if u==0 else ()
    return tuple((v,)+tail for v in range(max(0,u-b),u+1)
                 for tail in speed_paths(v,h-1,b))

def distance(u,path):
    return u + 2*sum(path[:-1]) + path[-1]

def direct(u,h,pair,delay):
    supports=[]
    for (bl,br),theta in pair:
        cost={}
        for l,r in product(speed_paths(u,h,bl),speed_paths(u,h,br)):
            ds,dt=distance(u,l),distance(u,r)
            if dt-ds!=theta:
                continue
            pref=(l[:delay],r[:delay])
            row=(ds+dt,l,r)
            if pref not in cost or row<cost[pref]:
                cost[pref]=row
        supports.append(cost)
    common=supports[0].keys() & supports[1].keys()
    if not common:
        return None
    return min((max(c[p][0] for c in supports),p,tuple(c[p] for c in supports)) for p in common)

def trans(x,y,dl,dr,bl,br):
    for i in range(max(0,x-bl),x+1):
        for j in range(max(0,y-br),y+1):
            yield i,j,dl+x+i,dr+y+j

def dp(u,h,pair,delay):
    @lru_cache(None)
    def value(k,x,y,l,r,w):
        bound,target=pair[w]
        if k==0:
            return l+r if x==0 and y==0 and r-l==target else None
        candidates=[z for a in trans(x,y,l,r,*bound) if (z:=value(k-1,*a,w)) is not None]
        return min(candidates,default=None)
    bound=tuple(min(v) for v in zip(pair[0][0],pair[1][0]))
    pre={(u,u,0,0)}
    for _ in range(delay):
        pre={n for xy in pre for n in trans(*xy,*bound)}
    scores=[]
    for x in pre:
        goals=[value(h-delay,*x,w) for w in range(2)]
        if all(v is not None for v in goals):
            scores.append(max(goals))
    return min(scores,default=None)

def write_rows():
    pair=(((1,2),0),((2,1),4))
    for d in range(4):
        _,pref,rows=direct(4,5,pair,d)
        for w,(_,l,r) in enumerate(rows):
            assert (l[:d],r[:d])==pref
            print(w,d,*(y for x in zip(l,r) for y in x))

def main():
    if sys.argv[1:]==["--rows"]:
        write_rows()
        return
    cases=0
    for u,h,bw,bs,g0,g1 in product(range(2,6),(3,4,5,6),(1,2),(2,3),
                                    (0,2,4,6),(0,-2,2,4,6)):
        if bw>=bs:
            continue
        pair=(((bw,bs),g0),((bs,bw),g1))
        for delay in range(h+1):
            expected=direct(u,h,pair,delay)
            optimum=dp(u,h,pair,delay)
            assert (expected[0] if expected else None)==optimum,(u,h,pair,delay,optimum,expected)
            cases+=1
    pair=(((1,2),0),((2,1),4))
    witness=tuple(direct(4,5,pair,t) for t in range(6))
    minima=[r[0] if r else None for r in witness]
    assert minima==[32,32,32,36,None,None]
    dec=[(direct(4,5, (row,row),0)[0]) for row in pair]
    assert dec==[32,28]
    print(json.dumps(dict(cases=cases,minima=minima,known=dec,witness=witness),sort_keys=True))
if __name__=="__main__":
    main()

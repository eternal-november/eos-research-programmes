"""Source rotations for anonymous carts and a reserve admission check.

Every track-pair belongs to an edge uv of a physical linkage graph. Each
vertex actuator can have flipped once while unobserved. Its local operation
swaps the two carts in *every* incident pair. A series of operations composes
by parity; no position or duty change other than the indicated swaps is
permitted. The actuator choices are not inferred from a camera.
"""
from itertools import combinations
from random import Random

def source_max(n, edges, w, offset):
    best=-1
    witness=None
    for q in range(1<<n):
        z=tuple(a^((q>>u)&1)^((q>>v)&1) for (u,v),a in zip(edges,offset))
        count=sum(b*d for b,d in zip(w,z))
        if count>best:best=count;witness=z
    return best,witness

def cycle_columns(n, edges):
    """One bit per fundamental cycle, in column representation."""
    adj=[[] for _ in range(n)]; out=[0]*len(edges); basis=0
    for i,(u,v) in enumerate(edges):
        stack=[(u,())]; visited={u}; path=None
        while stack:
            j,p=stack.pop()
            if j==v:path=p;break
            for k,e in adj[j]:
                if k not in visited:
                    visited.add(k);stack.append((k,p+(e,)))
        if path is None:
            adj[u].append((v,i));adj[v].append((u,i))
        else:
            for j in path+(i,):out[j]|=1<<basis
            basis+=1
    return out,basis

def syndrome(cols, bits):
    s=0
    for col,b in zip(cols,bits):
        if b:s^=col
    return s

def low_defect(cols, w, target):
    # Map achievable parity to minimum reserved demand lost relative to all 1.
    D={0:0}
    for c,d in zip(cols,w):
        R=D.copy()
        for p,v in D.items():
            q=p^c
            if q not in R or v+d<R[q]:R[q]=v+d
        D=R
    return D[target]

def exact_capacity(n, edges, w, offset):
    cols,r=cycle_columns(n,edges)
    target=syndrome(cols,(1^x for x in offset))
    return sum(w)-low_defect(cols,w,target),r

def main():
    E=((0,1),(0,2),(1,2));all_old=[1,1,1]
    assert exact_capacity(3,E,all_old,[0,0,0])==(2,1)
    assert exact_capacity(3,E,all_old,[1,0,0])==(3,1)
    print('triangle with identical per-slot identity sets: exact reserve 2 or 3')
    rng=Random(1843); count=0
    for n in range(1,13):
        G=list(combinations(range(n),2))
        for i in range(84):
            rng.shuffle(G)
            E=G[:rng.randrange(min(len(G),n+6)+1)]
            w=[rng.randrange(1,6) for e in E]; off=[rng.randrange(2) for e in E]
            p,t=source_max(n,E,w,off); q,r=exact_capacity(n,E,w,off)
            assert p==q
            cols,_=cycle_columns(n,E)
            assert syndrome(cols,t)==syndrome(cols,off)
            count+=1
    print(count,'direct actuator choices vs exact cycle-space weighted admission checks')
if __name__=='__main__':main()

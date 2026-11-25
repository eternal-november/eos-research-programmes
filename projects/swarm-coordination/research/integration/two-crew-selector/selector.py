"""Two civil recovery crews; each needs one exclusive final effect.

The source table at the decision has the two separately visible probe labels.
Each label advertises the slots for which that crew has both restored physical
readiness and authority. The independent physical validator rejects duplicate
uses of a slot even if both controllers request one.
"""
from dataclasses import dataclass
from itertools import product
from collections import defaultdict,deque
from random import Random

@dataclass(frozen=True)
class Source:
    edges: tuple
    left: tuple
    right: tuple

def oracle(S, subset=None):
    w=range(len(S.edges)) if subset is None else subset
    w=tuple(w)
    if not w:return {}
    ll={S.edges[k][0] for k in w};rr={S.edges[k][1] for k in w}
    keys=[(0,v) for v in sorted(ll)]+[(1,v) for v in sorted(rr)]
    for choices in product(*[(S.left,S.right)[side][v] for side,v in keys]):
        M=dict(zip(keys,choices))
        if all(M[(0,S.edges[k][0])]!=M[(1,S.edges[k][1])] for k in w):
            return M
    return None

def solve(S, subset=None):
    w=tuple(range(len(S.edges)) if subset is None else subset)
    adj=defaultdict(list)
    for k in w:
        a,b=S.edges[k]
        u,v=(0,a),(1,b)
        adj[u].append((v,k));adj[v].append((u,k))
    out={};seen=set()
    for s in adj:
        if s in seen:continue
        todo=deque([s]); parent={s:None}; pin={}
        while todo:
            u=todo.popleft();seen.add(u)
            avail=(S.left,S.right)[u[0]][u[1]]
            orientations={x^u[0] for x in avail}
            # Each choice of component orientation fixes all assigned slots.
            if not orientations:return None,(u,u,())
            if len(orientations)==1:pin.setdefault(next(iter(orientations)),u)
            for v,k in adj[u]:
                if v not in parent:
                    parent[v]=(u,k);todo.append(v)
        if len(pin)>1:
            segment={}
            def root(u):
                B=[]
                while parent[u] is not None:
                    v,k=parent[u];B.append(k);u=v
                return B
            u,v=pin[0],pin[1]
            a,b=root(u),root(v)
            return None,(u,v,tuple(sorted(set(a)^set(b))))
        r=next(iter(pin),0)
        out.update({u:r^u[0] for u in parent})
    assert all(out[(0,S.edges[k][0])]!=out[(1,S.edges[k][1])] for k in w)
    return out,None

def path(n):
    # n edges; planted endpoint pins imply inconsistent left orientations.
    # Each edge corresponds to a distinct allowed second-fault history.
    seq=[(i%2,i//2) for i in range(n+1)]
    L=[(0,1)]*((n+2)//2);R=[(0,1)]*((n+1)//2)
    L[0]=(0,)
    side,i=seq[-1];(L,R)[side][i]=(1^side,)
    E=tuple((u[1],v[1]) if u[0]==0 else (v[1],u[1]) for u,v in zip(seq,seq[1:]))
    return Source(E,tuple(L),tuple(R))

def with_report(S,outcome):
    cells=defaultdict(list)
    for k,x in enumerate(outcome):cells[x].append(k)
    return all(solve(S,w)[0] is not None for w in cells.values())

def minimum_features(S,features):
    for q in range(len(features)+1):
        from itertools import combinations
        for uses in combinations(range(len(features)),q):
            report=[tuple(features[i][j] for i in uses) for j in range(len(S.edges))]
            if with_report(S,report): return q,uses
    return None

if __name__=='__main__':
    rng=Random(872); k=0
    states=((0,),(1,),(0,1))
    for n in range(1,6):
        for _ in range(400):
            E=tuple(e for e in product(range(n),repeat=2) if rng.random()<0.4)
            S=Source(E,tuple(rng.choice(states) for _ in range(n)),tuple(rng.choice(states) for _ in range(n)))
            p,w=solve(S)
            assert (p is not None)==(oracle(S) is not None)
            if w is not None:
                assert len(w[2])>0 and oracle(S,w[2]) is None
            k+=1
    for n in range(2,50):
        S=path(n)
        p,w=solve(S)
        assert p is None and len(w[2])==n
        for j in range(n):assert solve(S,[k for k in range(n) if k!=j])[0] is not None
        bit=[i>=n//2 for i in range(n)]
        assert with_report(S,bit) and not with_report(S,[0]*n)
    assert minimum_features(path(7),[[0]*7, [0,0,0,1,1,1,1]])==(1,(1,))
    print(k,'actual finite local-policy enumerations agree with the pinned-component test')
    print('minimal inconsistent source paths of every size 2 to 49 verified')
    print('one common timely bit splitting a path repairs every checked paired family')

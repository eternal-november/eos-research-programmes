"""Physically acquired observations and sharp Hall history certificates."""
from collections import defaultdict
from itertools import product,combinations
from random import Random

def common(G):
    return [set.intersection(*(S[d] for S in G)) for d in range(len(G[0]))]

def matching(G):
    q={}
    def add(j,seen):
        for r in G[j]-seen:
            seen.add(r)
            if r not in q or add(q[r],seen):
                q[r]=j;return True
        return False
    return all(add(j,set()) for j in range(len(G)))

def proof(G,m):
    n=len(G[0]);X=common(G)
    slots=set(range(m))
    for s in range(1,n+1):
        for J in combinations(range(n),s):
            N=set.union(*(X[j] for j in J))
            if len(N)>=s:continue
            keys=list(sorted(slots-N))[:m-s+1]
            ids={next(i for i,h in enumerate(G) if k not in h[j]) for j in J for k in keys}
            assert not matching(common([G[i] for i in sorted(ids)]))
            return tuple(sorted(ids))
    return None

def tight(n,m,s):
    return tuple([set(range(m))-{k} if i==j else set(range(m)) for i in range(n)]
                 for j,k in product(range(s),range(s-1,m)))

def count_proof():
    rng=Random(222609);count=t=0
    for m in range(1,10):
        for n in range(1,m+1):
            for s in range(1,n+1):
                G=tight(n,m,s)
                assert len(G)==s*(m-s+1)
                assert not matching(common(G))
                assert all(matching(common(G[:j]+G[j+1:]))
                           for j in range(len(G)) if len(G)>1)
                assert len(proof(G,m))==len(G)
                t+=1
    for _ in range(9000):
        m=rng.randrange(1,9);n=rng.randrange(1,m+1)
        G=tuple([set(k for k in range(m) if rng.randrange(4)) for i in range(n)]
                for j in range(rng.randrange(1,10)))
        p=proof(G,m)
        assert (p is None)==matching(common(G))
        est=max(s*(m-s+1) for s in range(1,n+1))
        assert p is None or len(p)<=est
        count+=1
    print(count,"exact witness-to-matching checks and",t,"sharp witness families")

def mechanical(fault,mode,sub,late=False,visible=True):
    # Source process tests both outgoing pressure pairs. Individual
    # actuator positions are private; the probe returns only the
    # continuity detector, a conjunction of each pair's physical contacts.
    A,B=0,1;S,X,Y=range(3)
    j,k=fault
    contacts={(u,v):(u,v)!=fault for u,v in product((A,B),(X,Y))}
    status=tuple(all(contacts[u,v] for v in (X,Y)) for u in (A,B))
    # Actual source cut at tick 2. A timed out latch owns physical helper
    # S through [1,3) when the pulse used the shared relay. Independent
    # feed recovers the other work on its own circuit instead.
    captured=not sub
    if visible and not late:
        payload=("sample",*status) if captured else ("partial-at-1",status[0])
    else:payload=()
    active_cleanup=not captured and mode=="shared"
    # Keep the post-measurement resource facts distinct from receipt data.
    G=[{v for v in (S,X,Y) if (u,v)!=fault and (v!=S or not active_cleanup)}
       for u in (A,B)]
    return payload,G

def physical():
    w=tuple(product(range(2),range(1,3)))
    def one(mode,sub,late=False,visible=True):
        Q=defaultdict(list)
        for x in w:
            p,g=mechanical(x,mode,sub,late,visible)
            Q[p].append(g)
        return (all(matching(common(G)) for G in Q.values()),
                [proof(G,3) for G in Q.values() if not matching(common(G))])
    assert one("shared",False)[0]
    f,witness=one("shared",True)
    assert not f and witness
    assert one("separate",True)[0]
    assert not one("separate",True,visible=False)[0]
    assert not one("separate",False,late=True)[0]
    print("shared-feed timeout excludes a real slot; independent feed preserves service at the same cut")
    print("private or late physical sample does not help the downstream receiver")
    print("timeout rejection replays from",witness,"source history indices within the receiving classes")
if __name__=="__main__":count_proof();physical()

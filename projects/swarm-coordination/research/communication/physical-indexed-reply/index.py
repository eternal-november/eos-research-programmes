"""Finite synthesis for a deterministic three-cut, physically guarded INDEX."""
from itertools import product

def fibers(xs,p):
    # Quotient-renaming the early labels is harmless in this interface.
    buckets=[]
    def visit(i):
        if i==len(xs):
            yield tuple(tuple(b) for b in buckets)
            return
        for b in buckets:
            b.append(xs[i])
            yield from visit(i+1)
            b.pop()
        if len(buckets)<p:
            buckets.append([xs[i]])
            yield from visit(i+1)
            buckets.pop()
    yield from visit(0)

def options(F,allowed,K,Q):
    return {j:tuple(sorted(set(range(Q)).intersection(*(set(allowed[x,j]) for x in F if (x,j) in allowed))))
            for j in range(K) if any((x,j) in allowed for x in F)}

def color(adj,R):
    order=sorted(adj,key=lambda x:-len(adj[x]))
    colored={}
    def visit(i):
        if i==len(order):return True
        x=order[i]
        for c in range(R):
            if all(colored.get(y)!=c for y in adj[x]):
                colored[x]=c
                if visit(i+1):return True
                del colored[x]
        return False
    return dict(colored) if visit(0) else None

def by_fibers(K,p,q,r,allowed):
    assert allowed
    X=sorted({x for x,_ in allowed})
    for partition in fibers(X,1<<p):
        answer={}
        for i,F in enumerate(partition):
            avail=options(F,allowed,K,1<<q)
            for m in product(*(avail[j] for j in avail)):
                g=dict(zip(avail,m))
                reply={}
                for f in set(m):
                    js=[j for j in g if g[j]==f]
                    adj={x:{y for y in F if any((x,j) in allowed and (y,j) in allowed
                                                   and (x^y)>>j&1 for j in js)} for x in F}
                    c=color(adj,1<<r)
                    if c is None:break
                    reply[f]=c
                else:
                    answer[i]=(F,g,reply)
                    break
            else:break
        else:
            return answer
    return None

def brute(K,p,q,r,D):
    # Different exact oracle: enumerate actual encoders and response symbols,
    # then ask whether a decoder would need opposite bits on one input.
    X=sorted({x for x,_ in D})
    Q=1<<q;R=1<<r
    for E in product(range(1<<p),repeat=len(X)):
        active=[(j,e) for j in range(K) for e in set(E)
                        if any((x,j) in D and q0==e for x,q0 in zip(X,E))]
        for flags in product(range(Q),repeat=len(active)):
            G=dict(zip(active,flags))
            t=[(x,j,e,G[j,e]) for x,e in zip(X,E) for j in range(K) if (x,j) in D]
            if any(g not in D[x,j] for x,j,e,g in t):continue
            relevant=sorted({(e,g) for x,j,e,g in t})
            for e,g in relevant:
                used=sorted({x for x,j,u,v in t if (e,g)==(u,v)})
                for colors in product(range(R),repeat=len(used)):
                    reply=dict(zip(used,colors))
                    ded={}
                    for x,j,u,v in t:
                        if (e,g)!=(u,v):continue
                        bit=(x>>j)&1
                        key=(j,reply[x])
                        if key in ded and ded[key]!=bit:break
                        ded[key]=bit
                    else:break
                else:break
            else:return True
    return False

def validate(K,p,q,r,D,answer):
    assert len(answer)<=1<<p
    dec={}
    covered=set()
    for e,(states,g,reply) in answer.items():
        assert max(g.values(),default=0)<1<<q
        for x in states:
            assert x not in covered
            covered.add(x)
            for j in range(K):
                if (x,j) not in D:continue
                f=g[j]; b=reply[f][x]
                assert f in D[x,j] and b<1<<r
                key=(e,f,b,j);target=(x>>j)&1
                assert key not in dec or dec[key]==target
                dec[key]=target
    assert covered=={x for x,j in D}

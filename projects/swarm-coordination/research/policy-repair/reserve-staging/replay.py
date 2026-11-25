"""Exact civil emergency-supply fixture; no external dependencies."""
from itertools import combinations, product
from random import Random
from json import dumps

def subset(s):
    return (x for n in range(len(s)+1) for x in combinations(sorted(s),n))

def adjacency(edges):
    out = [[] for _ in range(len(edges)+1)]
    for a,b in edges:
        out[a].append(b); out[b].append(a)
    return out

def path(g, a, b):
    def go(x,last):
        if x == b: return (x,)
        for y in g[x]:
            if y != last and (tail:=go(y,x)):
                return (x,)+tail
    return go(a,-1)

def fit(g, r, f, notice, due, clear, cal):
    t=notice
    for u,v in zip((p:=path(g,r,f)),p[1:]):
        t=min((s+k for s,k in cal[u,v]
               if t<=s and (v!=f or clear<=s)), default=due+1)
        if t>due: return False
    return t<=due

def backwards(g, f, notice, due, clear, cal):
    q={f:due}; todo=[(f,-1)]
    while todo:
        v,p=todo.pop()
        for u in g[v]:
            if u==p: continue
            q[u]=max((s for s,k in cal[u,v] if s+k<=q[v]
                      and (v!=f or clear<=s)),default=-1)
            todo.append((u,v))
    return {u for u,t in q.items() if notice<=t}

def physical(edges, r, f, notice, due, clear, cal):
    """Transition on actual assignment + in-flight reserve, not spare-path arrays."""
    n=len(edges)+1
    legal=next(a for a in product(*edges) if len(set(a))==n-1 and r not in a)
    # Physical f no longer supplies its old duty. Its ledger binding survives.
    states={(legal,None)}
    for t in range(due+1):
        todo=set()
        for a, busy in states:
            if busy is not None:
                i,d,end=busy
                if t<end:
                    todo.add((a,busy))
                    continue
                assert end==t and d not in a and d!=f
                new=list(a); new[i]=d; a=tuple(new)
            if f not in a: return True
            todo.add((a,None))
            if t<notice: continue
            for i,e in enumerate(edges):
                u=next(x for x in e if x!=a[i]); v=a[i]
                if u in a or u==f or (v==f and t<clear): continue
                for s,k in cal[u,v]:
                    if t==s and t+k<=due:
                        todo.add((a,(i,u,t+k)))
        states=todo
    return False

def components(g,S):
    work=set(S); out=[]
    while work:
        active=[work.pop()]; found=set(active)
        while active:
            for v in g[active.pop()]:
                if v in work:
                    work.remove(v); active.append(v); found.add(v)
        out.append(found)
    return out

def certify(g, S, balls):
    if not S: return ()
    if not balls: return None
    depth={0:0}; todo=[(0,-1)]
    while todo:
        v,p=todo.pop()
        for u in g[v]:
            if u!=p: depth[u]=depth[v]+1; todo.append((u,v))
    for i,b in enumerate(balls):
        if not b: return (i,)
    tops=[min(b,key=depth.get) for b in balls]
    j=max(range(len(balls)),key=lambda i:depth[tops[i]])
    for i,b in enumerate(balls):
        if tops[j] not in b:
            assert not balls[j]&b
            return (j,i)
    left = components(g,S)
    cert=[]
    for C in left:
        bad=next((i for i,b in enumerate(balls) if not C & b),None)
        if bad is None: return None
        cert.append(bad)
    return tuple(sorted(set(cert)))

def recognized(e, f, i):
    r = Random(i)
    notice = r.randrange(4); due = r.randrange(notice, 11); clear=r.randrange(notice,12)
    cal={(u,v):tuple((s,k) for s in range(11) for k in range(1,4)
                     if r.randrange(9)<1)
         for a,b in e for u,v in [(a,b),(b,a)]}
    return f,notice,due,clear,cal

def main():
    rng=Random(6265); checks=solves=nonfifo=witness_singles=0
    for i in range(840):
        n=2+i%5
        e=[(j,rng.randrange(j)) for j in range(1,n)]
        g=adjacency(e)
        F=set(rng.sample(range(n),rng.randrange(1,n)))
        S={v for v in range(n) if v not in F and rng.randrange(3)!=0}
        B=[]
        for f in sorted(F):
            args=recognized(e,f,50751*i+f)
            if any(s<s2 and s+k>s2+k2 for slots in args[4].values()
                   for s,k in slots for s2,k2 in slots): nonfifo+=1
            b={f}
            for r in range(n):
                if r==f: continue
                reached=fit(g,r,*args)
                assert reached==physical(e,r,*args),(e,r,args)
                checks+=1
                if reached: b.add(r); solves+=1
            for a,b2 in product(b,repeat=2): assert set(path(g,a,b2))<=b
            assert b==backwards(g,*args)
            B.append(b)
        brute=set(S).intersection(*B)
        cert=certify(g,S,B)
        assert (cert is None)==bool(brute)
        if cert is not None:
            assert not set(S).intersection(*(B[j] for j in cert))
            assert len(cert)<=max(2,len(components(g,S)))
            if len(cert)==1: witness_singles+=1
    e=[(0,1),(1,2)]; g=adjacency(e)
    cal={(0,1):((0,4),(1,1)),(1,2):((2,1),),(1,0):(),(2,1):()}
    assert 0 in backwards(g,2,0,3,2,cal)
    assert fit(g,0,2,0,3,2,cal) and physical(e,0,2,0,3,2,cal)
    controls=[]
    for m in range(2,9):
        e=[(i,0) for i in range(1,m+1)]; g=adjacency(e); S=set(range(1,m+1))
        # A fault on the hub with circumstance i means leaf i has no
        # start permission early enough. All other leaves can take its duty.
        B=[]
        for ban in S:
            cal={(v,0):(() if v==ban else ((1,1),)) for v in S}
            cal.update({(0,v):() for v in S})
            args=(0,0,2,1,cal)
            accepted={v for v in S if fit(g,v,*args)}
            assert accepted=={v for v in S if physical(e,v,*args)}==S-{ban}
            B.append({0}|accepted)
        assert len(certify(g,S,B))==m
        for J in subset(range(m)):
            assert bool(set(S).intersection(*(B[i] for i in J)))==(len(J)<m)
        controls.append([m,m,2**m])
    # If the stalled incumbent is isolated one later tick, a path that
    # remains physically unchanged and has the same route length can fail.
    e=[(0,1),(1,2),(2,3)]; g=adjacency(e)
    cal={(0,1):((0,1),),(1,2):((1,1),),(2,3):((2,1),),
         (1,0):(),(2,1):(),(3,2):()}
    assert fit(g,0,3,0,3,2,cal) and not fit(g,0,3,0,3,3,cal)
    assert physical(e,0,3,0,3,2,cal) and not physical(e,0,3,0,3,3,cal)
    # An application demand set (leaf) is excluded in each scenario that
    # represents a set containing it. Compare exact min cover to min cert.
    setcover=0
    for _ in range(256):
        m=5; e=[(i,0) for i in range(1,m+1)]; g=adjacency(e); S=set(range(1,m+1))
        exclude=[{v for v in S if rng.randrange(2)} for i in range(6)]
        B=[{0}|(S-E) for E in exclude]
        C=certify(g,S,B)
        for J in subset(range(6)):
            assert (set().union(*(exclude[j] for j in J))==S)==(
                not set(S).intersection(*(B[j] for j in J)))
            setcover+=1
        assert (C is None)==(set().union(*exclude)!=S)
    print(dumps(dict(physical_controls=checks,feasible=solves,nonfifo_scenarios=nonfifo,
                     cases=840,non_fifo_wait_control=True,single_case_refusals=witness_singles,sharp_star=controls,
                     set_cover_controls=setcover),sort_keys=True))
if __name__=='__main__': main()

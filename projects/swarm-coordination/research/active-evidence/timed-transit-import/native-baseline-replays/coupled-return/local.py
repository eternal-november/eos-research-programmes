"""Two worlds; causal choices based on each actor's own observable history."""
from functools import lru_cache
from itertools import product
from coupled import adj,radio,Env
import sys

def decentralized(es,D,H,sites,channel='private',scan=False):
    assert len(es)==2
    ENDPOINT={13:42,42:13,2:3,3:2}
    WAIT=-1; DO=-2; SCAN=-4
    @lru_cache(None)
    def bound(w,t,x):
        e=es[w]
        from collections import deque
        q=deque([(x,0)]);seen={x}
        while q:
            p,c=q.popleft()
            if p==0:return c
            for u in adj[p]:
                if u not in seen and not e.blocked(p,u,t):
                    seen.add(u);q.append((u,c+1))
        return 200
    def actions(t,w,s,j):
        b,i,relay,paid=s
        x=b if j==0 else i
        a=[WAIT]+list(adj[x])
        if j==0 and not paid and t<D and t>0:
            # If relay position is private, even an attempt that won't reach
            # the receiver is allowed, and may supply a negative observation.
            a.insert(0,DO)
        if j==1 and relay==-1 and t>=es[w].receipt and i in sites:
            a.insert(0,DO)
        if scan and x in ENDPOINT:a.append(SCAN)
        return a
    @lru_cache(None)
    def nextstate(t,w,s,a,c):
        b,i,r,paid=s
        e=es[w]
        p=b if a<0 or e.blocked(b,a,t) else a
        q=i if c<0 or e.blocked(i,c,t) else c
        rr=i if c==DO else r
        hit=paid or (a==DO and t!=e.drop and radio.get((r,b),False))
        obsB=(p,hit,e.blocked(b,ENDPOINT[b],t) if a==SCAN else None)
        obsI=(q,t+1>=e.receipt,e.blocked(i,ENDPOINT[i],t) if c==SCAN else None)
        if channel in ('share-I','common'):obsB+=obsI
        if channel in ('share-B','common'):obsI+=obsB
        return (p,q,rr,hit),obsB,obsI
    @lru_cache(None)
    def prunable(w,t,s):
        b,i,_,paid=s
        if t>H or (not paid and t>=D):return True
        return bound(w,t,b)+int(not paid)>H-t or bound(w,t,i)>H-t
    @lru_cache(None)
    def single(t,w,s):
        b,i,_,paid=s
        if paid and b==i==0:return True
        if t==H or prunable(w,t,s):return False
        return any(single(t+1,w,nextstate(t,w,s,a,c)[0])
                   for a,c in product(actions(t,w,s,0),actions(t,w,s,1)))
    @lru_cache(None)
    def ok(t,both,known):
        s,z=both
        if all(u[0]==u[1]==0 and u[3] for u in both):return True
        if t==H or prunable(0,t,s) or prunable(1,t,z):return False
        if not single(t,0,s) or not single(t,1,z):return False
        if all(known):return True
        def opts(j):
            a=actions(t,0,s,j);b=actions(t,1,z,j)
            if known[j]:return list(product(a,b))
            return [(x,x) for x in a if x in b]
        for (a,d),(c,f) in product(opts(0),opts(1)):
            q,v,w=nextstate(t,0,s,a,c)
            r,x,y=nextstate(t,1,z,d,f)
            ki=known[1] or w!=y
            kb=known[0] or v!=x
            # Receiver learns the installer's source-world bit only after
            # the declared forwarding delay (zero at the next decision cut,
            # or one full additional slot). An ideal observation arm.
            if channel=='onebit-now':kb |=ki
            if channel=='onebit-late':kb |=known[1]
            if ok(t+1,(q,r),(kb,ki)):return True
        return False
    init=(16,13,-1,False)
    return ok(0,(init,init),(False,False))

if __name__=='__main__':
    from coupled import solver
    fam=[
      [Env(short=0),Env(closure=0)],
      [Env(short=0),Env(closure=0,drop=1)],
      [Env(short=0,receipt=2),Env(closure=0,receipt=2,drop=1)],
      [Env(),Env(2,1,1)],
    ]
    loss=[0,0,0,0,0,0];specials=[]
    for n,es in enumerate(fam):
      for D,H in product(range(2,7),range(8,13)):
        mid=decentralized(es,D,H,{13,42},'share-I')
        routed=decentralized(es,D,H,{13,42},'onebit-now')
        delayed=decentralized(es,D,H,{13,42},'onebit-late')
        wrong=decentralized(es,D,H,{13,42},'share-B')
        local=decentralized(es,D,H,{13,42})
        common=decentralized(es,D,H,{13,42},'common')
        ref=solver(es,D,H,{13,42})
        assert common==ref and routed==mid
        assert not local or delayed
        assert not delayed or routed
        assert not wrong or common
        assert not local or mid
        assert not mid or common
        loss[0]+=1;loss[1]+=local;loss[2]+=mid;loss[3]+=common;loss[4]+=delayed;loss[5]+=wrong
        if common!=local:specials.append([n,D,H,int(local),int(mid),int(common)])
    print(loss)
    print(specials)
    for n,d,h in [(1,3,10),(2,4,11)]:
        e=fam[n]
        print(n,d,h,[int(decentralized(e,d,h,{13,42},m)) for m in
            ('private','onebit-now','onebit-late','share-B','common')])

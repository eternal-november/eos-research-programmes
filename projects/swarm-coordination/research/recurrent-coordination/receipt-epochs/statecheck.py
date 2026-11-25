"""Independent immutable-state enumeration, full modulo epoch cycles."""
from collections import deque

def successors(state,queues,L,n):
    M=L//2+1

    for i,(phase,p,t,seen,extent) in enumerate(state):
        # phase 0 idle, 1 physical old holder live, 2 actual clearance with
        # pending real message, 3 queued, 4 transfer settled both reads pending.
        def change(row,next_queues=queues):
            return state[:i]+(row,)+state[i+1:],next_queues
        if phase==0:
            yield change((1,p,t,0,extent))
        if phase==1:
            yield change((2,p,t,0,extent))
        if phase in (1,2):
            # Only the old issuer's authentic port bit and modulo color reach
            # gate. Compute all stale contents using their attested age, but
            # do not use that hidden age to decide actual acceptance.
            for age in range(int(phase==1),extent+1):
                g=2*t+p
                signer=(i+g-age)%2;tag=((g-age)//2)%M
                assert ((signer,tag)==((i+p)%2,t))==(age==0)

                if (signer,tag)==((i+p)%2,t):
                    target=i+1-((i+p)%2);new=list(queues)
                    new[target]=new[target]+(i,)
                    yield change((3,p,t,0,extent),tuple(new))
        if phase==4:
            # Recipients may read independently, in either order.
            for mask in (1,2):
                if seen&mask:continue
                s=seen|mask
                if s==3:
                    yield change((0,p^1,(t+p)%M,0,min(L,extent+1)))
                else:
                    yield change((4,p,t,s,extent))
    for s,Q in enumerate(queues):
        if not Q:continue
        i=Q[0];ph,p,t,v,e=state[i]
        assert ph==3 and s==i+1-((i+p)%2)
        next=queues[:s]+(Q[1:],)+queues[s+1:]
        yield state[:i]+((4,p,t,0,e),)+state[i+1:],next

def check(n,L):
    root=(tuple((0,0,0,0,0) for _ in range(n-1)),tuple(() for _ in range(n)))
    seen={root};queue=deque([root]);maxports=0;transitions=0
    while queue:
        st,Q=queue.popleft()
        assert all(len(k)<=2 and len(k)==len(set(k)) for k in Q)
        assert all(sum(i in row for row in Q)==int(s[0]==3) for i,s in enumerate(st))
        for i,(ph,p,tag,b,ext) in enumerate(st):
            assert 0<=tag<L//2+1 and 0<=ext<=L and ph in range(5)
        maxports=max(maxports,*map(len,Q))
        nxt=list(successors(st,Q,L,n));transitions+=len(nxt)
        assert nxt # no finite maximal deadlocked state in cooperative event envelope
        for x in nxt:
            if x not in seen:
                seen.add(x);queue.append(x)
    assert maxports==min(2,n-1)
    return len(seen),transitions

def main():
    s=t=0
    for n,L in [(n,L) for n in (2,3) for L in range(6)]+[(4,0),(4,1),(4,2)]:
        a,b=check(n,L);s+=a;t+=b
    print(s,t,'reachable immutable-state controls; no finite deadlock under the selected finish/observation transitions')
if __name__=='__main__':main()

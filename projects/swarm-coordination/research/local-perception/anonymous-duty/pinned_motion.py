"""Partial reports constrain pairwise actuator parity, not inferred names."""
from coupled_motion import cycle_columns, syndrome, low_defect
from random import Random
from itertools import combinations

def source_max(n,e,w,a,pins):
    def allowed(x):
        return all((x>>u)&1==p for u,p in pins.items())
    return max(sum(cost*(b^((x>>u)&1)^((x>>v)&1))
                   for (u,v),cost,b in zip(e,w,a)) 
               for x in range(1<<n) if allowed(x))

def pinned_constraints(n,edges,pins):
    cols,r=cycle_columns(n,edges)
    # A path per pinned pair is enough; using any simple paths may introduce
    # redundant support, but not additional independent constraints.
    adj=[[] for _ in range(n)]
    for i,(u,v) in enumerate(edges):
        adj[u].append((v,i));adj[v].append((u,i))
    root_parity=[]
    unseen=set(range(n))
    while unseen:
        j=min(unseen)
        st=[(j,())];unseen.remove(j); pp={}
        while st:
            u,path=st.pop()
            if u in pins:pp[u]=path
            for v,i in adj[u]:
                if v in unseen:
                    unseen.remove(v);st.append((v,path+(i,)))
        if pp:
            p=next(iter(pp))
            for q,path in pp.items():
                if q==p:continue
                b=r+len(root_parity)
                for i in set(path)^set(pp[p]):cols[i]|=1<<b
                root_parity.append(pins[q]^pins[p])
    return cols, [0]*r+root_parity

def exact(n,e,w,a,pins):
    cols, parity=pinned_constraints(n,e,pins)
    p=sum(b<<i for i,b in enumerate(parity))
    target=syndrome(cols,(1^v for v in a))^p
    return sum(w)-low_defect(cols,w,target),len(parity)

def main():
    e=[(0,1),(1,2)];w=[1,1];a=[0,0]
    for i in range(3):
        for value in (0,1):
            assert exact(3,e,w,a,{i:value})==(2,0)
    assert exact(3,e,w,a,{0:0,2:1})==(1,1)
    print('path: each single actuator report leaves demand at 2, two opposite endpoint readings lower it to 1')
    rng=Random(42);count=0
    for n in range(2,11):
        e=list(combinations(range(n),2))
        for _ in range(62):
            rng.shuffle(e)
            G=e[:rng.randrange(min(len(e),n+4)+1)]
            w=[rng.randint(1,10) for v in G];a=[rng.randint(0,1) for v in G]
            pins={v:rng.randint(0,1) for v in range(n) if rng.random()<.33}
            p,k=exact(n,G,w,a,pins)
            assert p==source_max(n,G,w,a,pins)
            count+=1
    print(count,'exact source worlds vs augmented parity constraints')
if __name__=='__main__':main()

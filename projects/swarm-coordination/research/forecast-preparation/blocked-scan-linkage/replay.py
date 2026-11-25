from collections import Counter
from itertools import permutations,product
from random import Random
import json

def roster(c):
    return tuple((a,b) for (a,b),n in zip(product(range(2),repeat=2),c) for _ in range(n))

def actual(r):
    n=len(r)
    costs={}
    for p in permutations(range(n)):
        x=sum(a==0 and r[p[i]][1]==0 for i,(a,b) in enumerate(r))
        k=sum(i!=v for i,v in enumerate(p))
        costs[x]=min(k,costs.get(x,n+1))
    return costs

def cells(n):
    for a in range(n+1):
        for b in range(n-a+1):
            for c in range(n-a-b+1):
                yield a,b,c,n-a-b-c

def local(r,d):
    a,b,c,k=r
    return dict((x,2*abs(x-a)) for x in range(a-min(a,k),a+min(b,c)+1) if 2*abs(x-a)<=d)

def actual_change(rs,targets):
    outputs=[]
    for r,x in zip(rs,targets):
        rr=roster(r)
        identity=list(range(len(rr))); delta=x-r[0]
        types=((0,1),(1,0)) if delta>0 else ((0,0),(1,1))
        groups=[[i for i,q in enumerate(rr) if q==t] for t in types]
        assert abs(delta)<=min(map(len,groups))
        for u,v in zip(*(g[:abs(delta)] for g in groups)):
            identity[u],identity[v]=identity[v],identity[u]
        counts=Counter((rr[i][0],rr[j][1]) for i,j in enumerate(identity))
        outputs.append((tuple(counts[z] for z in product(range(2),repeat=2)),
                        sum(i!=j for i,j in enumerate(identity))))
    return outputs

def ambiguity(rs,ss,K):
    q,r=([local(t,K) for t in group] for group in (rs,ss))
    def feasible(m):
        return {v for v in product(*m) if sum(c[x] for c,x in zip(m,v))<=K}
    return feasible(q)&feasible(r)

def balanced(n,x):
    assert n%2==0
    return x,n//2-x,n//2-x,x

def main():
    pc=0;tc=0
    from math import factorial
    for n in range(1,8):
        for t in cells(n):
            observed=actual(roster(t))
            for K in range(n+1):
                assert {x:k for x,k in observed.items() if k<=K}==local(t,K)
                tc+=1
            pc+=factorial(n)
    rng=Random(539110)
    for _ in range(2048):
        n,k=rng.randrange(2,9),rng.randrange(1,5)
        K=rng.randrange(n*k+1)
        left=[];right=[]
        for j in range(k):
            u,v=rng.randrange(n+1),rng.randrange(n+1)
            x,y=(rng.randint(max(0,u+v-n),min(u,v)) for _ in range(2))
            left.append((x,u-x,v-x,n-u-v+x))
            right.append((y,u-y,v-y,n-u-v+y))
        d=sum(abs(u[0]-v[0]) for u,v in zip(left,right))
        assert bool(ambiguity(left,right,K))==(d<=2*(K//2))
    zero=[balanced(80,40),balanced(80,16)]
    one=[balanced(80,0),balanced(80,24)]
    f=lambda r:tuple(map(sum,zip(*r)))
    pooled0=actual_change([f(zero)],[40])
    pooled1=actual_change([f(one)],[40])
    assert pooled0==pooled1==[((40,40,40,40),32)]
    assert not ambiguity(zero,one,47)
    target=(20,20)
    assert target in ambiguity(zero,one,48)
    assert sum(k for _,k in actual_change(zero,target))==48
    assert sum(k for _,k in actual_change(one,target))==48
    print(json.dumps(dict(permutations=pc,table_budget_checks=tc,block_instances=2048,
      pooled_first_overlap=32,tagged_first_overlap=48,original_common_table=pooled0),sort_keys=True))

if __name__=='__main__':
    main()

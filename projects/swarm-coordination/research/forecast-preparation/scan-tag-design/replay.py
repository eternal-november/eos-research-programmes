from itertools import combinations,product,accumulate
from random import Random
import json

def partitions(n):
    def put(i,s,k):
        if i==n:
            yield tuple(s)
        else:
            for g in range(k+1):
                yield from put(i+1,s+[g],max(k,g+1))
    return put(0,[],0)

def aggregate(x,p):
    out=[0]*(max(p)+1)
    for t,g in zip(x,p):
        out[g]+=t
    return tuple(out)

def mindist(z,o,p):
    return min(sum(abs(i-j) for i,j in zip(x,y))
               for x in map(lambda z:aggregate(z,p),z)
               for y in map(lambda o:aggregate(o,p),o))

def build(n,edges,K):
    amp=K//2+1
    # Identical positive balanced margins; the baseline separates different edges.
    z=[];o=[]
    for i,(a,b) in enumerate(edges):
        base=(i+1)*(2*amp+1)
        u=[base]*n;v=u[:]
        v[a]+=amp;v[b]-=amp
        z.append(tuple(u));o.append(tuple(v))
    M=len(edges)*(2*amp+1)+amp+1
    for mode in z+o:
        assert all(0<x<M for x in mode)
    return z,o,M

def interval_cuts(edges):
    chosen=[]
    for a,b in sorted(edges,key=lambda e:e[1]):
        if not chosen or chosen[-1]<a:
            chosen.append(b-1)
    return chosen

def contiguous(n,mask):
    ends=set(mask)
    return tuple(sum(i>j for j in ends) for i in range(n))

def brute_collision(z,o,cap,radius,p):
    q=[sum(cap for k in p if k==i) for i in range(max(p)+1)]
    lattice=list(product(*(range(v+1) for v in q)))
    def reachable(m):
        w=aggregate(m,p)
        return {x for x in lattice if sum(abs(a-b) for a,b in zip(x,w))<=radius}
    return bool(set().union(*(reachable(x) for x in z)) &
                set().union(*(reachable(y) for y in o)))

def clock_frontier(delta):
    s=[0]+list(accumulate(delta))
    n=len(delta)
    previous=[0]+[None]*n
    out=[]
    for k in range(1,n+1):
        current=[None]*(n+1)
        plus=minus=None
        for i in range(1,n+1):
            value=previous[i-1]
            if value is not None:
                p,m=value+s[i-1],value-s[i-1]
                plus=p if plus is None else max(plus,p)
                minus=m if minus is None else max(minus,m)
            if plus is not None:
                current[i]=max(plus-s[i],minus+s[i])
        out.append(current[n])
        previous=current
    return out

def main():
    graphs=pc=ic=bc=0
    for n in range(2,6):
        ground=list(combinations(range(n),2))
        for b in range(1,1<<len(ground)):
            E=[e for k,e in enumerate(ground) if b>>k&1]
            z,o,M=build(n,E,2)
            K=2
            graphs+=1
            for p in partitions(n):
                legal=all(p[a]!=p[d] for a,d in E)
                assert (mindist(z,o,p)>2*(K//2))==legal
                pc+=1
                if n<=3:
                    assert brute_collision(z,o,M,K//2,p)!=legal
                    bc+=1
            allcuts=range(n-1)
            c=interval_cuts(E)
            assert mindist(z,o,contiguous(n,c))>2
            brute=[]
            for m in range(n):
                for d in combinations(allcuts,m):
                    if mindist(z,o,contiguous(n,d))>2:
                        brute.append(m)
                    ic+=1
            assert len(c)==min(brute)
    E=[(0,1),(2,3),(4,5)]
    z,o,M=build(6,E,2)
    assert mindist(z,o,(0,1,0,1,0,1))==4
    assert len(interval_cuts(E))+1==4
    rng=Random(574018)
    for _ in range(1024):
        d=[rng.randrange(-6,7) for i in range(rng.randrange(1,10))]
        n=len(d)
        assert sum(abs(t) for t in d)==sum(abs(v) for v in aggregate(d,tuple(int(t<0) for t in d)))
        brute=[max(sum(abs(v) for v in aggregate(d,contiguous(n,P)))
               for P in combinations(range(n-1),k)) for k in range(n)]
        assert brute==clock_frontier(d)
    print(json.dumps(dict(two_mode_clock_cases=1024,graphs=graphs,partition_checks=pc,clock_partitions=ic,
         enumerated_observation_box_cases=bc,clock_example=4,reusable_example=2),sort_keys=True))

if __name__=='__main__':
    main()

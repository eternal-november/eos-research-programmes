from itertools import product,combinations
from random import Random
import json

def graph(n,edges):
    p=[0]*(n+1)
    for k in range(n+1):
        modified=False
        for a,b,c in edges:
            if p[b]>p[a]+c:
                p[b]=p[a]+c
                modified=True
        if not modified:return tuple(x-p[n] for x in p[:-1])
    return None

def plan(box,gaps,k,R,b,L,U,radio=True,sense=True):
    n=len(box);q=k+1
    e=[edge for i,(l,u) in enumerate(box) for edge in ((n,i,u),(i,n,-l))]
    e += [(i+1,i,-g) for i,g in enumerate(gaps)]
    if radio:e += [(i,i+q,R) for i in range(n-q)]
    if not sense:return graph(n,e)
    for i in range(n-q+1):
        for j in range(i,n-q+1):
            h=e+[(n,i+q-1,L+b),(i,n,b-L),(n,j+q-1,U+b),(j,n,b-U)]
            h += [(t,t+q,2*b) for t in range(i,j)]
            x=graph(n,h)
            if x is not None:return x
    return None

def direct(x,k,R,b,L,U,radio=True,sense=True):
    for lost in combinations(range(len(x)),k):
        y=[p for i,p in enumerate(x) if i not in lost]
        if radio and any(v-u>R for u,v in zip(y,y[1:])):
            return False
        if sense:
            end=L
            for p in y:
                if p+b<end:continue
                if p-b>end:break
                end=p+b
                if end>=U:break
            else:
                pass
            # At a singleton zone, an interval must actually cover the point.
            if L==U:
                if not any(abs(p-L)<=b for p in y):return False
            elif end<U:return False
    return True

def oracle(box,gaps,k,R,b,L,U,radio=True,sense=True):
    for x in product(*(range(l,u+1) for l,u in box)):
        if all(v-u>=g for u,v,g in zip(x,x[1:],gaps)) and direct(x,k,R,b,L,U,radio,sense):
            return x
    return None

def hidden_cut_tests():
    checked=0
    # Same common prefix; exact independent static terminal oracle on each branch.
    for g,b,d,T in product((1,2),(1,2),(1,2),range(4)):
        initial=(-g,0,g);n=3;R=2*g
        for tau in range(T+1):
            prefix=product(*(range(x-tau,x+tau+1) for x in initial))
            feasible=False
            for mid in prefix:
                if not all(v-u>=g for u,v in zip(mid,mid[1:])):continue
                slack=T-tau
                box=[(x-slack,x+slack) for x in mid]
                if all(oracle(box,[g]*2,1,R,b,center,center) is not None for center in (-(b+d),b+d)):
                    feasible=True;break
            assert feasible==(T-tau>=d),(g,b,d,T,tau)
            checked+=1
    return checked

def main():
    rng=Random(852883)
    counts={'yes':0,'no':0,'separately_but_not_jointly':0}
    for _ in range(1700):
        n=rng.randrange(2,7)
        box=[tuple(sorted([rng.randrange(-2,8),rng.randrange(-2,8)])) for j in range(n)]
        gaps=[rng.randrange(1,3) for j in range(n-1)]
        k=rng.randrange(n-1);R=rng.randrange(1,9);b=rng.randrange(5)
        L=rng.randrange(-2,8);U=L+rng.randrange(5)
        a=(box,gaps,k,R,b,L,U)
        x=plan(*a)
        y=oracle(*a)
        assert (x is None)==(y is None),(a,x,y)
        if x is not None:
            assert all(l<=p<=u for (l,u),p in zip(box,x))
            assert all(v-u>=g for u,v,g in zip(x,x[1:],gaps))
            assert direct(x,k,R,b,L,U)
        elif plan(*a,sense=False) is not None and plan(*a,radio=False) is not None:
            counts['separately_but_not_jointly']+=1
        counts['no' if x is None else 'yes']+=1
    a=([(0,0),(1,9),(1,9)],[1,1],1,4,2,7,8)
    assert plan(*a) is None and oracle(*a) is None
    assert direct(plan(*a,sense=False),1,4,2,7,8,sense=False)
    assert direct(plan(*a,radio=False),1,4,2,7,8,radio=False)
    counts["hidden_cut_cases"]=hidden_cut_tests()
    print(json.dumps(counts,sort_keys=True))
if __name__=='__main__':
    main()

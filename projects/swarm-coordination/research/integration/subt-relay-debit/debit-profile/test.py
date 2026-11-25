from itertools import product, combinations
from math import comb

def values(B,W):
    return [h for h in product(range(B+1),repeat=W) if sum(h)<=B]

def profile(histories):
    return tuple(max(sum(h[i:]) for h in histories) for i in range(len(histories[0])))

def exact(B,W,h,plan):
    ts = tuple(range(-W,0))+tuple(range(W+1))
    debits=h+plan
    # True constraint, recomputed from timestamps, inclusive window.
    return all(sum(d for s,d in zip(ts,debits) if t-W<=s<=t)<=B
               for t in range(W+1))

def summary(B,W,p,plan):
    return all((p[t] if t<W else 0)+sum(plan[max(0,t-W):t+1])<=B
               for t in range(W+1))

def probe(B,W,p,q):
    k=next(i for i in range(W) if p[i]!=q[i])
    n=B-min(p[k],q[k])
    return tuple(n if i==k else 0 for i in range(W+1))

def exhaustive(B,W):
    hs=values(B,W)
    assert len(hs)==comb(B+W,W)
    assert len(set(profile([h]) for h in hs))==len(hs)
    test=sep=0
    for h,k in combinations(hs,2):
        s,t=profile([h]),profile([k])
        plan=probe(B,W,s,t)
        assert exact(B,W,h,plan)!=exact(B,W,k,plan)
        sep+=1
    for i,h in enumerate(hs):
        for k in hs[i:]:
            p=profile([h,k])
            for plan in product(range(B+1),repeat=W+1):
                assert summary(B,W,p,plan)==(exact(B,W,h,plan) and exact(B,W,k,plan))
                test+=1
    return len(hs),sep,test

def witness():
    B,W=5,2
    # Hidden branch h fills A or B. Independent predecessor maxima do not
    # preserve the result of assigning sender after learning branch.
    anti=(((0,3),(0,0)),((0,0),(0,3)))
    corr=(((0,3),(0,3)),((0,0),(0,0)))
    fixed=(0,3,0)
    marg=lambda j:tuple(profile([x[k] for x in j]) for k in range(2))
    assert marg(anti)==marg(corr)
    possible=lambda j:all(any(exact(B,W,h,fixed) for h in w) for w in j)
    blind=lambda j:any(all(exact(B,W,w[k],fixed) for w in j) for k in range(2))
    assert possible(anti) and not possible(corr)
    assert not blind(anti) and not blind(corr)
    print("Blind schedules both fail; informed service possible only on anticorrelation:",marg(anti))
    # In the warehouse adapter, W is a guaranteed fixed residence time
    # in modeled bays. Token count is recomputed at entry, so prior exits
    # with the same count at the cut may give distinct new-entry times.
    early,late=(3,0),(0,3)
    assert sum(early)==sum(late)==3
    assert exact(B,W,early,fixed) and not exact(B,W,late,fixed)
    print("Same cut occupancy:",sum(early),"launch 3 at tick 1 accepted only after earlier admissions")

if __name__=='__main__':
    totals=[0,0,0]
    for B,W in ((1,1),(1,5),(2,4),(3,3),(5,2),(6,2)):
        row=exhaustive(B,W)
        totals=[a+b for a,b in zip(totals,row)]
        print(B,W,*row)
    print("Totals",*totals)
    witness()

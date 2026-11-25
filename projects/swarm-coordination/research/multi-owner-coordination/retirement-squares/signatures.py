"""Physical footprint quotients for an exact family of retirement commands."""
from collections import defaultdict
from dataclasses import dataclass, replace
from itertools import product, combinations_with_replacement
from random import Random

@dataclass(frozen=True)
class Hold:
    key: int
    bins: tuple[int,...]  # joint resource-by-tick coordinates at fixed consumer scope
    sig: int            # this set of certified commands may retire it
    voided: bool=False   # economic cancel, not a physical release

def add(a,b):
    return tuple(x+y for x,y in zip(a,b))

def observed(rows,d):
    x=(0,)*d
    for h in rows:x=add(x,h.bins)
    return x

def publish(rows,d):
    out=defaultdict(lambda:(0,)*d)
    for h in rows:out[h.sig]=add(out[h.sig],h.bins)
    return dict(out)

def retire(rows,command,certified):
    return tuple(h for h in rows if not (certified and h.sig&(1<<command)))

def cancel(rows,key):
    return tuple(replace(h,voided=True) if h.key==key else h for h in rows)

def after_profile(profile,commands,d):
    x=(0,)*d
    for group,v in profile.items():
        if not group&commands:x=add(x,v)
    return x

def zeta_recover(outcomes,m,d):
    # Outcomes indexed by allowed survivors: complement of retirement set.
    w={}
    for B in range(1<<m):
        carry=list(outcomes[B]);s=B
        while s:
            s=(s-1)&B
            for t,v in enumerate(w[s]):carry[t]-=v
        if any(carry): w[B]=tuple(carry)
        else: w[B]=(0,)*d
    return {s:v for s,v in w.items() if any(v)}

def raw_query(rows,d,setmask,m):
    for i in range(m):
        if setmask & (1<<i): rows=retire(rows,i,True)
    return observed(rows,d)

def behavioral(rows,d,m):
    return tuple(raw_query(rows,d,((1<<m)-1)^B,m) for B in range(1<<m))

def uniform_rename(rows,f):
    return tuple(replace(h,sig=f(h.sig)) for h in rows)

def commute(rows,f,src,tgt):
    # Must compare the two actual branches on the evolved boundary.
    a=uniform_rename(retire(rows,src,True),f)
    b=retire(uniform_rename(rows,f),tgt,True)
    return a==b

def main():
    # One each of either-retireable and unretireable vs two singletons.
    p=(Hold(0,(1,),3),Hold(1,(1,),0))
    q=(Hold(0,(1,),1),Hold(1,(1,),2))
    assert [raw_query(p,1,i,2) for i in range(4)]==[(2,),(1,),(1,),(1,)]
    assert [raw_query(q,1,i,2) for i in range(4)]==[(2,),(1,),(1,),(0,)]
    assert observed(cancel(p,0),1)==observed(p,1)
    assert observed(retire(cancel(p,0),0,True),1)==(1,)
    assert retire(cancel(p,0),0,False)==cancel(p,0)
    for m in range(1,11):
        p=tuple(Hold(i,(1,),i) for i in range(1<<m) if i.bit_count()%2==0)
        q=tuple(Hold(i,(1,),i) for i in range(1<<m) if i.bit_count()%2==1)
        pprof=publish(p,1);qprof=publish(q,1)
        full=(1<<m)-1
        assert all(after_profile(pprof,C,1)==after_profile(qprof,C,1)
                   for C in range(full))
        assert after_profile(pprof,full,1)==(1,) and after_profile(qprof,full,1)==(0,)
    print('parity families through ten scopes separate exactly at full retirement depth')
    n=0
    for m in (1,2,3):
        raw=list(product(range(1<<m),(1,2,3)))
        quotient={}
        for tuples in combinations_with_replacement(raw,3):
            rows=tuple(Hold(i,(v,),s) for i,(s,v) in enumerate(tuples))
            beh=behavioral(rows,1,m)
            prof=publish(rows,1)
            assert prof==zeta_recover(beh,m,1)
            if beh in quotient: assert quotient[beh]==prof
            quotient[beh]=prof
            n+=1
    print(n,'exhaustive exact retained-profile and raw retirement checks')
    rng=Random(331350)
    n=0
    for _ in range(1600):
        m=rng.randrange(1,6);p=rng.randrange(1,6);limit=1<<m
        rows=tuple(Hold(i,tuple(rng.randrange(1,6) for _ in range(p)),rng.randrange(limit))
                   for i in range(rng.randrange(1,10)))
        prof=publish(rows,p)
        assert zeta_recover(behavioral(rows,p,m),m,p)==prof
        table=[rng.randrange(limit) for _ in range(limit)]
        for s,t in product(range(m),repeat=2):
            expected=all(bool(h.sig&(1<<s))==bool(table[h.sig]&(1<<t)) for h in rows)
            assert commute(rows,table.__getitem__,s,t)==expected
            n+=1
    print(n,'named resource/receipt comparison squares with uniform per-signature amendments')
    # Bijective scope rename: an inverse produces the old source representative.
    swap=lambda a:2*(a&1)+((a&2)//2)
    assert all(swap(swap(a))==a for a in range(4))
    for state in ((Hold(0,(1,),1),Hold(1,(2,),2)),(Hold(0,(1,),0),Hold(1,(4,),3))):
        assert uniform_rename(uniform_rename(state,swap),swap)==state
        assert commute(state,swap,0,1) and commute(state,swap,1,0)
    # Amending by private owner instead of old signature can split a class.
    one=(Hold(0,(1,),0),);other=(Hold(1,(1,),0),)
    assert publish(one,1)==publish(other,1)
    amend=lambda xs:tuple(replace(h,sig=1) if h.key==0 else h for h in xs)
    assert raw_query(amend(one),1,1,1)!=raw_query(amend(other),1,1,1)
    print('owner-dependent amendments can demand a formerly unrepresented distinction')
if __name__=='__main__':main()

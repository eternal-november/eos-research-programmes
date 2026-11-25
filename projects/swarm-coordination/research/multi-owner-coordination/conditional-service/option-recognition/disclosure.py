"""Price, resource and evidence comparisons at a declared commitment cut."""
from fractions import Fraction as F
from itertools import product
from random import Random

from game import analyze, settle

def signal(v,k,a,q,e):
    # e of the original population are low states whose actual failure receipt
    # reaches the price setter by the offer cut. This routing rule binds before
    # the actual option outcome, and does not apply to mandatory safety evidence.
    assert 0<=e<=1-q
    m=1-e
    stage=analyze(v,k,a,q/m,False)
    return stage[0],m*stage[1],e*(v-k)+m*stage[2]

def direct(v,k,a,q,e):
    groups=(((0,e),),((0,1-q-e),(a,q)))
    vals=[]
    for group in groups:
        work=[]
        for p in (None,*range(v+1)):
            s=b=service=0
            for x,m in group:
                outcome,bv,sv=settle(x,v,k,p)
                s+=m*sv;b+=m*bv;service+=m*(outcome=='joint')
            work.append((s,service,b))
        vals.append(max(work))
    return sum(x[2] for x in vals),sum(x[0] for x in vals)

def design(groups,total,v,k,a,q,c,g):
    # One early authenticated source receipt can cover a whole mechanically
    # inseparable failure group. Costs are real reserve costs paid by seller.
    # DP retains cheapest exact early fraction; all partial designs share that
    # finite interface and have no strategic type-by-type discretionary reveal.
    states={0:(0,())}
    for i,(mass,cost) in enumerate(groups):
        for t,(price,keys) in tuple(states.items()):
            trial=price+cost,keys+(i,)
            if t+mass not in states or trial<states[t+mass]:
                states[t+mass]=trial
    feasible=[]
    for t,(price,keys) in states.items():
        m=1-F(t,total)
        if a*m<=q*(v-k) and a*m>c and v-k-a*m>g+price:
            feasible.append((price,keys,t))
    return min(feasible) if feasible else None

def brute_design(groups,total,v,k,a,q,c,g):
    feasible=[]
    for subset in product((False,True),repeat=len(groups)):
        fees=sum(x[1] for x,s in zip(groups,subset) if s)
        mass=sum(x[0] for x,s in zip(groups,subset) if s)
        _,b,s=signal(v,k,a,q,F(mass,total))
        if b>c and s>g+fees:
            feasible.append((fees,tuple(i for i,t in enumerate(subset) if t),mass))
    return min(feasible) if feasible else None

def main():
    # The band characterizes an extension when withholding everything and full
    # disclosure both fail, not every possible cost/authority profile.
    rng=Random(439442)
    n=0
    for _ in range(900):
        den=40; h=rng.randrange(1,12); q=F(h,den)
        v=rng.randrange(12,35); k=rng.randrange(5); V=v-k
        a=rng.randrange(1,V)
        if q*V>=a: continue # no-release comparator already pools
        c=F(rng.randrange(10,28),10)*a*q
        g=F(rng.randrange(0,10),5)
        if c<q*a:continue
        group_count=rng.randrange(1,7)
        cuts=[0]+sorted(rng.sample(range(1,den-h),group_count-1))+[den-h]
        groups=[(y-x,F(rng.randrange(1,8),3)) for x,y in zip(cuts,cuts[1:])]
        for t in range(0,den-h+1):
            _,b,s=signal(v,k,a,q,F(t,den))
            assert (b,s)==direct(v,k,a,q,F(t,den))
            n+=1
        assert design(groups,den,v,k,a,q,c,g)==brute_design(groups,den,v,k,a,q,c,g)
    print(n,'direct legal posted-price checks after reachable disclosures')
    v,k,a,q,c,g=18,4,6,F(1,4),F(5,2),2
    for shown in (0,F(1,4),F(1,2),F(3,4)):
        print('early truthful failure mass',shown,signal(v,k,a,q,shown))
    result=design(((2,1),(1,1)),4,v,k,a,q,c,g)
    assert result==(1,(0,),2)
    assert design(((3,1),),4,v,k,a,q,c,g) is None
    print('physical separation of the two failure-report channels changes whether either owner will prepare')

if __name__=='__main__':main()

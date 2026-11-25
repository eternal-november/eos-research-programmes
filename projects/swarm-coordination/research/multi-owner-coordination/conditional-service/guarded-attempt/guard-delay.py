"""Bargaining before an irrevocable service-guard read."""
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product,groupby
from random import Random

@dataclass(frozen=True)
class Type:
    mass: F
    success: F
    standalone: F
    after_failure: F
    attempt_cost: F=F(0)

def effective(t,v):
    return v-(t.standalone-(1-t.success)*t.after_failure)/t.success

def factored(types,v,k):
    terms=sorted([(effective(t,v),t.mass*t.success,t.mass*t.attempt_cost) for t in types],reverse=True)
    w=c=F(0)
    best=(F(0),F(0),None)
    for p, block in groupby(terms,key=lambda x:x[0]):
        for _,m,b in block:
            w+=m;c+=b
        revenue=w*(p-k)-c
        if revenue>0 and (revenue,w)>best[:2]:
            best=(revenue,w,p)
    return best

def direct(types,v,k,p):
    total_profit=total_joint=total_buyer=F(0)
    for t in types:
        upon_accept=t.success*(v-p)+(1-t.success)*t.after_failure if p is not None else -1
        if upon_accept>=t.standalone:
            total_profit+=t.mass*(t.success*(p-k)-t.attempt_cost)
            total_joint+=t.mass*t.success
            total_buyer+=t.mass*upon_accept
        else:
            total_buyer+=t.mass*t.standalone
    return total_profit,total_joint,total_buyer

def alternative_gate(reserved,finish,settle_valid,exercise,protected):
    # Prior load is actually holding the fallback port on [0,4).
    # A grant accepted at 4 is for the sole launch at 4, needing [4,6).
    # Tentative joint acceptance sequesters that lane [4,5) if co-funded.
    # No joint physical entry occurs until its guard is evaluated at 5.
    if not settle_valid or not exercise:
        return False
    competing_claims = ((0,finish),)
    if reserved and not protected:
        competing_claims += ((4,5),)
    return not any(a<6 and 4<b for a,b in competing_claims)

def execution(fallback_ready, accept, split_slot, old_end, joint_old_end,
              joint_receipt, source_signed=True):
    # setup happens at tick 4 without knowing whether shared permission will
    # clear; at tick 5 exercise one option or retire any unused staged kit.
    staged=fallback_ready and alternative_gate(
        accept,old_end,True,True,split_slot)
    receipt_ok=source_signed and joint_receipt == (5, True)
    # The truthful fixture emits positive clearance only if the old load is gone.
    assert not receipt_ok or joint_old_end<=5
    joint_start=accept and receipt_ok
    events=[]
    if staged: events.append((4,'stage-fallback'))
    if joint_start:
        events.append((5,'launch-shared'))
        if staged: events.append((5,'drain-fallback-staging'))
        events.append((6,'shared-service-settled'))
    elif staged:
        events.extend(((5,'launch-fallback'),(6,'fallback-settled')))
    return events

def lp_evidence(types,v,k,robust=True):
    # Generic incentive-compatibility LP in units of one success-contingent
    # payoff. When submission of the same p and x has different settlement
    # probabilities by type, IR is divided by the actor's true success chance,
    # not the price setter's posterior average.
    from scipy.optimize import linprog
    n=len(types)
    val=[effective(t,v) for t in types]
    coeff=[-float(t.mass*(t.success*(p-k)-t.attempt_cost)) for t,p in zip(types,val)]
    coeff += [float(t.mass*t.success) for t in types]
    inequalities=[]
    for i,j in product(range(n),repeat=2):
        if i==j:continue
        a=[0.]*(2*n)
        a[j]=float(val[i]-val[j]);a[n+j]=1.;a[n+i]=-1.
        inequalities.append(a)
    equal=[]
    if robust:
        for i,j in product(range(n),repeat=2):
            if i>=j or val[i]!=val[j]:continue
            a=[0.]*(2*n);a[i]=1.;a[j]=-1.
            equal.append(a)
    opt=linprog(coeff,A_ub=inequalities,b_ub=[0]*len(inequalities),
                A_eq=equal if equal else None,b_eq=[0]*len(equal) if equal else None,
                bounds=[(0,1)]*n+[(0,None)]*n,method='highs')
    expected=factored(types,v,k)[0]
    assert opt.success
    if robust: assert abs(-opt.fun-float(expected))<1e-8
    return -opt.fun

def exactly_one(xs,a,b):
    return (a in xs)!=(b in xs)

def main():
    rng=Random(39561)
    for j in range(2100):
        n=rng.randrange(2,7)
        groups=[Type(F(1,n),F(rng.randrange(1,9),8),F(a),
                     F(rng.randrange(a+1)),F(rng.randrange(3),2))
                for a in [rng.randrange(11) for i in range(n)]]
        v=rng.randrange(12,29);k=rng.randrange(6)
        ans=[]
        for p in [None,*{effective(t,v) for t in groups}]:
            if p is None or p>=0:
                ans.append((*direct(groups,v,k,p)[:2],p))
        # A negative price cannot improve payoff here because physical
        # transfer and attempted service are both nonnegative seller costs.
        ans.sort(key=lambda x:(x[0],x[1]))
        g=factored(groups,v,k)
        assert g[:2]==ans[-1][:2] or (g[0]==0==ans[-1][0])
        if j<120:lp_evidence(groups,v,k)
    print('2100 exact state/payoff schedules and 120 generic multi-type pricing LP controls')
    for protected in (False,True):
        assert alternative_gate(False,4,True,True,protected)
        assert not alternative_gate(False,5,True,True,protected)
        assert not alternative_gate(True,4,False,True,protected)
        assert alternative_gate(True,4,True,True,protected)==protected
        types=(Type(F(1,2),F(1,2),F(0),F(0)),
               Type(F(1,2),F(1,2),F(6),F(6 if protected else 0)))
        b,j,p=factored(types,18,4)
        bu=direct(types,18,4,p)[2]
        print('protected capacity',protected,'effective prices',[effective(t,18) for t in types],
              'quoted',p,'post-prep buyer',bu,'seller',b,'joint success',j)
        assert (bu>4)==protected
        if protected: assert b>2+1
    tie=(Type(F(1,2),F(1,2),F(6),F(6),F(6)),
         Type(F(1,2),F(1),F(6),F(0),F(0)))
    assert factored(tie,18,4)[0]==3
    assert lp_evidence(tie,18,4)==3 and lp_evidence(tie,18,4,False)==4
    print('a weakly truthful oracle separates identical menus and overstates attainable profit 4 vs 3')
    count=0
    for ready,accept,protect,old,joint,timely,sig in product(
            (False,True),(False,True),(False,True),(4,5),(5,6),(False,True),(False,True)):
        read=(5 if timely else 6,joint==5)
        e=execution(ready,accept,protect,old,joint,read,sig)
        names=[x[1] for x in e]
        assert ('launch-shared' in names)==(accept and joint==5 and timely and sig)
        assert not ('launch-shared' in names and 'launch-fallback' in names)
        if 'stage-fallback' in names:
            assert exactly_one(names,'drain-fallback-staging','fallback-settled')
        if not protect and accept: assert 'stage-fallback' not in names
        count+=1
    print(count,'tick traces; cleanup charged and no shared launch under a failed guard')
    # Two equally weighted paired histories can have the same marginals,
    # but different payoff conditional on failure. The best price consumes
    # the joint law of disposition and the actual fallback effect.
    independent_F=F(6,2)
    pair_as=[(False,F(6)),(True,F(0))]
    pair_bs=[(False,F(0)),(True,F(6))]
    for worlds,cap in ((pair_as,12),(pair_bs,6)):
        sv=F(sum(x[0] for x in worlds),len(worlds))
        after=sum((y for success,y in worlds if not success),F(0))/sum(1 for x in worlds if not x[0])
        assert effective(Type(F(1),sv,F(6),after),18)==cap
    assert effective(Type(F(1),F(1,2),F(6),independent_F),18)==9
    print('same safety and fallback marginals: paired valuation caps 12 vs 6, factorized substitute wrongly gives 9')

if __name__=='__main__':main()

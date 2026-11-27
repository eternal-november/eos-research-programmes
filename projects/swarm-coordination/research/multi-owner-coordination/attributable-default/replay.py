"""Exact civil coordination game: attributable default after a lawful role change."""
from collections import defaultdict
from fractions import Fraction as F
from itertools import product
import json
from pathlib import Path
import sys

# History predictions include both ordinary compliance (including lawful
# inability) and every feasible strategic deviation. Controller trace
# fields are records from distinct, modeled instruments, not ground truth.
OWNERS=("A","B")
PAY=("completed","missed")  # physical completion by deadline, not a consent flag

def record(h, action, arrives, view):
    owner, possible=h
    pay=PAY[0] if possible and action=="release" else PAY[1]
    if view=="outcome":
        return (pay,)
    if view=="named":
        return (pay,owner)
    # Case-keyed recognition from local governor plus no-fault eligibility
    # from distinct physical gate, captured before old duty can re-enter.
    # If not received by the financial cut we cannot use it.
    return (pay,owner,possible) if arrives else (pay,owner,None)

H=tuple(product(OWNERS,(False,True)))

def distribution(h,action,view,q,evade=False):
    out=defaultdict(F)
    for timely,mass in ((False,1-q),(True,q)):
        if not mass:
            continue
        # Diagnostic control: a non-verifying endpoint lets a deviator
        # suppress independent audit. Never assert protection then.
        if evade and action=="decline":
            timely=False
        out[record(h,action,timely,view)] += mass
    return out

def material(view,q,evade=False):
    good=set()
    for h in H:
        good.update(distribution(h,"release" if h[1] else "decline",view,q))
    bad={i:distribution((i,True),"decline",view,q,evade) for i in OWNERS}
    return good,bad

def minimum(d,alpha):
    # Strict continuation preference, no arbitrary positive tie break.
    if d<0:
        return 0
    if not alpha:
        return None
    return d//alpha+1

def formula(view,q,evade,d):
    good,bad=material(view,q,evade)
    return tuple(minimum(d[i],sum(p for o,p in bad[i].items() if o not in good))
                 for i in OWNERS)

def exhaustive(view,q,evade,d,cap):
    good,bad=material(view,q,evade)
    out=[]
    for i in OWNERS:
        noncompliant=tuple(o for o in bad[i] if o not in good)
        # Good records required to forfeit zero. Implicit default under a
        # protected observation is zero, including unknown/lawful refusal.
        possible=[]
        for amounts in product(range(cap+1),repeat=len(noncompliant)):
            expected=sum((bad[i][o]*v for o,v in zip(noncompliant,amounts)),F(0))
            if expected>d[i]:
                possible.append(max(amounts,default=0))
        out.append(min(possible,default=None))
    return tuple(out)

def participate(bonds, q_act, d, k, crew_after_tolls, prep, fee_cap):
    # Strict ex ante participation. Activation histories disjoint and sign
    # fees sunk at exercise. No crew revenue from forfeitures. q_act[i]
    # is measure of eligible actual holders, not conditional audit rate.
    targets={i:q_act[i]*d[i]+k[i]*bonds[j] for j,i in enumerate(OWNERS)}
    fees=tuple(max(0,targets[i]//1+1) for i in OWNERS)
    crew=q_act["A"]*crew_after_tolls["A"]+q_act["B"]*crew_after_tolls["B"]
    winners=[(a,b) for a,b in product(range(fee_cap+1),repeat=2)
             if a>targets["A"] and b>targets["B"] and crew-prep-a-b>0]
    good=all(x<=fee_cap for x in fees) and crew-prep-sum(fees)>0
    assert good==bool(winners)
    return fees,good

def main():
    count=0
    for v,q,e,a,b,c in product(("outcome","named","audit"),
        (F(0),F(1,4),F(1,2),F(3,4),F(1)),(False,True),range(-1,4),range(-1,4),range(7)):
        d=dict(A=a,B=b)
        expected=tuple(x if x is not None and x<=c else None for x in formula(v,q,e,d))
        actual=exhaustive(v,q,e,d,c)
        assert actual==expected
        count+=1

    d=dict(A=1,B=1)
    base={v:formula(v,F(1,2),False,d) for v in ("outcome","named","audit")}
    assert base==dict(outcome=(None,None),named=(None,None),audit=(3,3))
    assert formula("audit",F(1,2),True,d)==(None,None)
    assert formula("audit",F(1),False,d)==(2,2)
    feet=0
    for a,b,c,f,k,h in product(range(1,6),range(1,6),range(5),
                              range(5),range(3),range(3)):
        participate((a,b),dict(A=F(1,4),B=F(1,4)),dict(A=k,B=h),
                    dict(A=F(1,4),B=F(1,4)),dict(A=16,B=16),c,f)
        feet+=1
    fees,entered=participate((3,3),dict(A=F(1,4),B=F(1,4)),d,
                          dict(A=F(1,4),B=F(1,4)),dict(A=16,B=16),2,4)
    assert entered and fees==(2,2)

    # Old user physically clears at tick 4; one setup tick before each
    # gate's commit. Audit may arrive after completion/no show and may
    # still discipline if by the irrevocable financial cut. Cases below
    # declare exact audit law conditional on defection and same ability.
    timing=[]
    for new_installed,old_clear,visible,audit_time in product((False,True),
             (4,5,6),(False,True),(5,7,8,9)):
        holder="B" if new_installed else "A"
        control_cut=old_clear+1
        eligible=control_cut<=6
        # Only current recognized holder commits. Requested old command
        # cannot cause entry after the local amendment.
        current_grant=holder if eligible else None
        last_audit=8
        if audit_time<control_cut:
            # Do not treat a pre-cut status read as covering future ability.
            qualified=False
        else:
            qualified=visible and audit_time<=last_audit
        timing.append(dict(holder=holder,physical_clear=old_clear,control=control_cut,
                 eligible=eligible,grant=current_grant,qualified_audit=qualified,
                 audit_time=audit_time))
    assert any(x["eligible"] and x["qualified_audit"]
               and x["audit_time"]>7 for x in timing)
    src=json.loads(Path(sys.argv[1]).read_bytes())
    pair=[v for v in src["cases"] if v["clear"] and v["operative"] and v["delegation"]
          and v["disclosure"] and not v["sibling"]]
    assert len(pair)==2 and pair[0]["native_source"]==pair[1]["native_source"]
    assert {r["history"] for r in pair}=={"compatible","incompatible"}
    assert {r["rescue"] for r in pair}=={False,True}
    # Pinned simulation only exercises the entitlement witness, never
    # the authored payoff, refusal, probability, bond, or audit instrument.
    print(json.dumps(dict(native_entitlement_pair=len(pair), menu_checks=count,participation_checks=feet,
          example_bond=base,example_fees=fees,audit_timing=timing),sort_keys=True,indent=2))
if __name__=="__main__":
    main()

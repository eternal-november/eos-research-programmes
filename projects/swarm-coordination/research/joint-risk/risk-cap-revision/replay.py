"""Exact replay of risk-revision timing on the bounded two-dispatch plant."""
from fractions import Fraction as Q
from itertools import product
from hashlib import sha256
from pathlib import Path
import json
import reserve_source as src

LOW,HIGH,MID=Q(1,5),Q(25,64),Q(337,1024)
EXTRA=Q(1,20)
# Physical lock -> authority issue (if any) -> local admission -> receipt (if late)
# -> sealed-outcome interval. No fresh state read during these phases.
LOCK, ISSUE, EARLY, ADMIT, LATE, DISPATCH3, DISPATCH4 = range(7)
ORDERS={"tighten":(HIGH,LOW), "relax":(LOW,MID)}
POLICIES=("issuer_joint","receipt_joint","receipt_admission_only")
SOURCE_SHA="5e4925061efc774b495579621ba87204b27566ea751197a82f9bd10a78935f6d"

RISK={}
for word in src.WORDS:
    for law,eq in product(src.LAWS,(True,False)):
        _,_,loss=src.oracle(law,word,eq)
        for protect in (3,4):
            RISK[word,law,eq,protect]=loss[7-protect]
assert {v for (w,l,e,p),v in RISK.items()}=={Q(n,1024) for n in (175,400,337,112)}
for w,l in product(src.WORDS,src.LAWS):
    assert tuple(RISK[w,l,e,p] for e,p in product((True,False),(3,4)))==tuple(Q(n,1024) for n in (175,400,337,112))

def union(r,a):
    # Fast new load's failure is an independent Bernoulli coin.
    return r+(1-r)*(EXTRA if a=="fast" else 0)

def run(revision,changed,early,policy,w,l,eq,protect,a):
    old,new=ORDERS[revision]
    r=RISK[w,l,eq,protect]
    assert r<=old                           # only actually lawful initial cuts
    cand=union(r,a)
    tick=EARLY if early else LATE
    trace=[(LOCK,"lock_reserve",protect)]
    if changed:
        trace.extend(((ISSUE,"authority_revision",new),(tick,"verified_receipt",new)))
    trace.append((ADMIT,"admit_"+a,cand))
    trace.extend(((DISPATCH3,"owed_dispatch",3),(DISPATCH4,"owed_dispatch",4)))
    trace.append((DISPATCH3 if a=="fast" else DISPATCH4,"new_load_dispatch",a))
    trace.sort()
    observation=(w,eq,protect,new if changed and early else None)
    effective=new if changed and (early or policy=="issuer_joint") else old
    check_at_admit=cand<=effective
    # A joint revision names the same still-open physical horizon at receipt.
    # Admission-only is a distinct specification; no assertion of a joint
    # tightening when previously admitted work is grandfathered.
    inherited_at_receipt=(not changed or cand<=new) if policy!="receipt_admission_only" else None
    valid=check_at_admit and inherited_at_receipt is not False
    return dict(observation=observation,admissible=valid,admission_pass=check_at_admit,
                revision_audit=inherited_at_receipt,old_risk=r,new_risk=cand,
                service_dispatch=3 if a=="fast" else 4,trace=trace)

def summary():
    p=Path(__file__).with_name("reserve_source.py")
    assert sha256(p.read_bytes()).hexdigest()==SOURCE_SHA
    delivered={}
    checks=0
    for revision,early,policy in product(ORDERS,(False,True),POLICIES):
        groups={}
        n=0
        for w,l,eq,pr,changed in product(src.WORDS,src.LAWS,(True,False),(3,4),(False,True)):
            if RISK[w,l,eq,pr]>ORDERS[revision][0]:
                continue
            # The fixed law and policy coin are not inputs to the controller.
            armed={}
            for a in ("safe","fast"):
                z=run(revision,changed,early,policy,w,l,eq,pr,a)
                armed[a]=z["admissible"]
                obs=z["observation"]
                checks+=1
            row=groups.setdefault(obs,{"safe","fast"})
            row.intersection_update(a for a,v in armed.items() if v)
            n+=1
        delivered[revision,early,policy]=groups
    # Shortest witness, repeated on every report word under both hidden laws.
    w=src.WORDS[0]; l=src.LAWS[0]; k=(w,True,3,None)
    y=dict()
    for rev in ORDERS:
        for early,po in product((False,True),POLICIES):
            values=delivered[rev,early,po]
            for changed in (False,True):
                cap=ORDERS[rev][1] if early and changed else None
                y[rev,early,po,changed]=sorted(values[(w,True,3,cap)])
    assert delivered["tighten",False,"issuer_joint"][k]=={"safe"}
    assert delivered["tighten",False,"receipt_joint"][k]=={"safe"}
    assert delivered["tighten",False,"receipt_admission_only"][k]=={"safe","fast"}
    assert delivered["relax",False,"issuer_joint"][k]=={"safe"}
    assert delivered["relax",True,"issuer_joint"][(w,True,3,MID)]=={"safe","fast"}
    diverse={}
    for parity,priv in product((True,False),(3,4)):
        r=RISK[w,l,parity,priv]; fast=union(r,"fast")
        admissible_if_low=sorted(a for a in ("safe","fast") if union(r,a)<=LOW)
        diverse[parity,priv]=dict(old=r,fast=fast,low=admissible_if_low,
                                 middle_old_only=r<=MID,middle_plus_fast=fast<=MID)
    assert diverse[True,4]["low"]==diverse[False,3]["low"]==[]
    assert diverse[True,3]["low"]==["safe"] and diverse[False,4]["low"]==["fast","safe"]
    # Pre-lock tightening permits the parity policy with the safe new mode.
    assert max(RISK[w0,l0,eq,3 if eq else 4] for w0,l0,eq in product(src.WORDS,src.LAWS,(True,False)))==Q(175,1024)<LOW
    r=RISK[w,l,True,3]
    # Separate audit: a private old placement, independently wrong 10% of
    # the time, is unobjectionable only on the coarser pooled audit field.
    placement_pool={eq: (9*RISK[w,l,eq,3 if eq else 4]+RISK[w,l,eq,4 if eq else 3])/10
                    for eq in (True,False)}
    assert placement_pool=={True:Q(395,2048),False:Q(269,2048)}
    assert max(placement_pool.values())<=LOW<min(RISK[w,l,True,4],RISK[w,l,False,3])
    # Finite action classes support the policy feasibility theorem directly.
    dead_on_tightening=sum(not v for v in delivered["tighten",False,"issuer_joint"].values())
    assert dead_on_tightening==8
    joint_coin=(LOW-r)/((1-r)*EXTRA)
    assert joint_coin==Q(596,849)
    # Same new-loss marginal, different coupling; exact joint risks.
    coupling={"nested":r,"independent":union(r,"fast"),"disjoint":r+EXTRA}
    assert coupling["nested"]<=LOW<coupling["independent"]<coupling["disjoint"]
    sample={}
    for rev,early,po,changed,a in product(ORDERS,(False,True),POLICIES,(False,True),("safe","fast")):
        sample[str((rev,early,po,changed,a))]=run(rev,changed,early,po,w,l,True,3,a)
    return dict(checks=checks,observation_classes={str(k):len(v) for k,v in delivered.items()},
                common_actions={str(k):v for k,v in y.items()},
                exposures={str(k):v for k,v in diverse.items()},
                controls=dict(max_pooled_action_coin=joint_coin,same_marginal_couplings=coupling,
                              placement_pool=placement_pool,dead_on_late_tightening=dead_on_tightening),
                event_traces=sample)

if __name__=="__main__":
    print(json.dumps(summary(),default=str,indent=2,sort_keys=True))

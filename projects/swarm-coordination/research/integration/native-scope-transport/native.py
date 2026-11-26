"""Replay both frozen and unused authorized continuations at the exact native cut."""
from dataclasses import asdict
from importlib.util import spec_from_file_location,module_from_spec
from itertools import product
import json
import math
from pathlib import Path
import sys
from transfer import Row,audit,consumers,join_effect

src=Path(sys.argv[3])
sys.path.insert(0,str(src))
spec=spec_from_file_location("compound_replay",src/"replay.py")
up=module_from_spec(spec)
spec.loader.exec_module(up)


def options(works):
    return tuple((a,b) for a,b in product('-R','-LR')
                 if not (a=='R' and (works or b=='R')))


def source(plant,t,works,action):
    obj=plant()
    try:
        obj.pre(works)
        evidence=obj.evidence(t,False)
        assert (evidence.old.name=='SETTLED')==works
        paid,details=obj.commit(*action,t)
        paid=tuple(bool(x) for x in paid)
        a,b=action
        # Independent effects reference, supplied the same finite arm/cut.
        expected_old=works or a=='R'
        expected_rescue= b=='R' or (b=='L' and (not works if plant is up.Warehouse else t>1))
        assert paid==(expected_old,expected_rescue,True),(plant.name,t,works,action,paid)
        if plant is up.Warehouse and paid[0]:assert details['return_owed']
        if plant is up.Radio:assert details['retained_pending_copy']==(not paid[0])
        return Row(f"{plant.name}:{t!r}",(plant.name,t,works,action),evidence.old.name,action,paid)
    finally:
        obj.close()


def full_profile(rows):
    return frozenset((r.status,r.action,r.paid) for r in rows)


def run():
    contexts={}
    cuts=(.75,1.,math.nextafter(1.,math.inf),1.25)
    cases={(p.name,t):[source(p,t,s,a) for s in (False,True) for a in options(s)]
           for p,t in product((up.Warehouse,up.Radio),cuts)}
    base=cases["warehouse",.75]
    prof=consumers(base)
    n=0
    for key,rows in cases.items():
        name,t=key
        # Exhaustive same-information policies: enumerate each branch independently.
        def policies_shape():
            # Old status is the only controller input; hidden native states
            # are evaluated conditionally, not read by policy execution.
            modes=['LIVE','SETTLED']
            parts=[[r for r in rows if r.status==s] for s in modes]
            return [[row.action for row in choices if all(row.paid)] for choices in parts]
        options_by_branch=policies_shape()
        adequate=bool(all(options_by_branch))
        # If settlement read is erased, one action must work for both statuses.
        # Ineligible retries cannot be supplied by hidden actuator authority.
        erased_actions=set(options_by_branch[0])&set(options_by_branch[1])
        assert not erased_actions
        certified=audit(rows)
        assert adequate==certified
        assert certified==(name=='warehouse' or t>1)
        assert (consumers(rows)==prof)==certified
        assert (full_profile(rows)==full_profile(base))==(name=='warehouse')
        wrong=[r for r in rows if r.action==('-','L')]
        joint=join_effect(wrong,[0,1,2])
        marginal=[join_effect(wrong,[i]) for i in range(3)]
        false_join=bool(all(marginal) and not joint)
        assert false_join==(name=='warehouse')
        # Typed histories agree with evaluator and protocol boundary:
        # never substitute an issued command for eventual native callback.
        contexts[f"{name}:{t!r}"]=dict(
            consumer_carries=certified, direct_feasible=adequate, feasible_without_status=bool(erased_actions), feasible_contingent_policies=math.prod(map(len,options_by_branch)),
            unrestricted_profile_matches=full_profile(rows)==full_profile(base),
            pos_in_each_marginal=int(bool(all(marginal))),joint_witnesses=joint,
            false_join=false_join,source_rows=[asdict(r) for r in rows])
        n+=len(rows)
    assert n==64
    print(json.dumps(dict(contexts=contexts,cases=n),indent=2,sort_keys=True))


if __name__=='__main__':
    run()

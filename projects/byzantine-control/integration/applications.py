"""Instantiate the common-core adapter on actual enactment and shared-device kernels."""
from __future__ import annotations
from collections import Counter
from dataclasses import replace
from pathlib import Path
import argparse, hashlib, json
import core_bridge as b
import enactment_model as e
import structure_model as st

class MemoObservations:
    """Exact memoization of these immutable-state, pure source callbacks."""
    def __init__(self,kernel):
        self.original=kernel
        self.cache={}
    def __getattr__(self,name):
        return getattr(self.original,name)
    def observations(self,fault,state):
        key=(fault,state)
        if key not in self.cache:
            self.cache[key]=tuple(self.original.observations(fault,state))
        return self.cache[key]
    def check_cache(self):
        for (fault,state),observations in self.cache.items():
            assert observations==tuple(self.original.observations(fault,state))

def source_node(node):
    """Decode into the ORIGINAL source Node class, not the bridge module class."""
    return st.Node(node.fault,node.state,node.memory,node.ages)

def record_key(boundary):
    return (boundary.node,boundary.observation.local,b.freeze_event(boundary.observation.physical_sample),
            boundary.violations,boundary.terminal,boundary.previous_effect)

def compare_round(kernel,tables,fault,state):
    kernel=MemoObservations(kernel)
    memory=tuple(t.start("boot") for t in tables)
    ages=tuple(0 for _ in kernel.service(fault))
    node=b.source.Node(fault,state,memory,ages)
    decoded=source_node(node)
    assert type(decoded) is st.Node and (decoded.fault,decoded.state,decoded.memory,decoded.ages)==(fault,state,memory,ages)
    observations=effects=expanded=absent=faulty=0
    digest=hashlib.sha256()
    for obs in kernel.observations(fault,state):
        observations+=1
        sample=state.x if isinstance(kernel.original,e.Enactment) else tuple(z.physical.x for z in state)
        assert obs.physical_sample==sample
        boundary=b.CoreBoundary(node,obs)
        # The source callback, separately reconstructed using its actual rule.
        issued=[]; next_memory=[]
        for i,t in enumerate(tables):
            if kernel.compliant(fault,i):
                c,m=t.react(memory[i],obs.local[i])
            else:
                c,m=None,memory[i]
            issued.append(c); next_memory.append(m)
            absent+=int(obs.local[i] is None)
            faulty+=int(not kernel.compliant(fault,i))
            assert b.local_view(boundary,i)==(memory[i],obs.local[i])
        issued=tuple(issued); next_memory=tuple(next_memory)
        expected=Counter()
        for out in kernel.outcomes(fault,state,obs,issued):
            effects+=1
            a=[]; bad=list(out.violations)
            for age,(name,deadline) in zip(ages,kernel.service(fault)):
                new=0 if name in out.delivered else age+1
                a.append(new)
                if new>=deadline: bad.append("actual_service_deadline:"+name)
            target=b.source.Node(fault,out.state,next_memory,tuple(a))
            rec=b.EffectRecord(issued,out.delivered,b.freeze_event(out.event),out.violations)
            next_obs=tuple(kernel.observations(fault,out.state))
            assert next_obs
            for no in next_obs:
                expected[(target,no.local,b.freeze_event(no.physical_sample),tuple(sorted(set(bad))),None,rec)]+=1
        actual=Counter(record_key(nb) for nb,_ in b.core_successors(kernel,boundary,b.profile(kernel,tables,boundary)))
        assert expected==actual, ("Source/core mismatch",fault,state,obs)
        expanded+=sum(actual.values())
        digest.update(repr(sorted(actual.items(),key=lambda p:repr(p[0]))).encode("utf-8"))
    kernel.check_cache()
    return {"joint_observations":observations,"source_effects":effects,"prepared_successors":expanded,
            "absent_slots":absent,"faulty_slots":faulty,"digest":digest.hexdigest()}

def aggregate(records):
    totals={k:sum(r[k] for r in records) for k in records[0] if k!="digest"}
    totals["factored_rounds"]=len(records)
    totals["digest"]=hashlib.sha256("".join(r["digest"] for r in records).encode()).hexdigest()
    return totals

def enactment():
    kernel=e.Enactment(); tables=e.policies(); records=[]; keys=0
    for index,f in enumerate(kernel.faults()):
        if index % 100 == 0: print("Enactment correspondence fault "+str(index),flush=True)
        init=next(iter(kernel.initials(f)))
        assert tuple(t.start(j) for t,j in zip(tables,init.local_inputs))==(0,)*7
        states=(init.state,replace(init.state,x=4,pending=(1,1,1,1),last_sample=4,
                spare_stage=2,ready=True,votes=3,retired=True,ready_issued=True,issued_votes=3))
        for state in states:
            assert e.metadata_invariant(f,state)
            records.append(compare_round(kernel,tables,f,state))
        if f.ready_key_bad and not f.planner_bad:
            assert all(kernel.compliant(f,i) for i in range(4))
            keys+=1
    result=aggregate(records)
    assert result["absent_slots"]>0 and result["faulty_slots"]>0 and keys>0
    return dict(result,joint_faults=len(tuple(kernel.faults())),ready_key_fault_with_intact_brake_planners=keys,
                state_selection="one actual initializer plus one inductive warm/retired state per fault; not full reachable graph")

def fleet():
    kernel=st.SharedPlannerFleet()
    shared=st.Table(("pair_low","pair_high"),("boot",),(0,),((0,1),),((0,0),))
    target=st.Table(("low","high"),("boot",),(0,),((0,1),),((0,0),))
    tables=(shared,target,target,target,target)
    records=[]
    for index,f in enumerate(kernel.faults()):
        if index % 12 == 0: print("Fleet correspondence fault "+str(index),flush=True)
        first=next(iter(kernel.initials(f)))
        assert tuple(t.start(j) for t,j in zip(tables,first.local_inputs))==(0,)*5
        states=(first.state,tuple(st.SwitchingState(st.BrakeState(x,6,((0,0,0),),()),j)
                                 for j,x in enumerate((4,4))),
                tuple(st.SwitchingState(st.BrakeState(x,6,((0,0,0),),()),j)
                      for j,x in enumerate((2,3))))
        for state in states:
            records.append(compare_round(kernel,tables,f,state))
    return dict(aggregate(records),joint_faults=len(tuple(kernel.faults())),
                state_selection="actual first initializer, two-high boundary and unequal ambiguous-source boundary per fault; not full graph")

def reproduce():
    return {"enactment":enactment(),"shared_fleet":fleet(),
            "scope":"Exhaustive local outcomes/next observations at declared source scenarios; generic step/run proof supplies transport for all faithful instances",
            "source_hashes":{p.name:hashlib.sha256(p.read_bytes().replace(b"\r\n",b"\n")).hexdigest()
                for p in [Path(__file__),Path(b.__file__),Path(e.__file__),Path(st.__file__),
                          Path(__file__).with_name("APPLICATIONS.md"),Path(b.source.__file__)]}}
def main():
    ap=argparse.ArgumentParser()
    g=ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--write",action="store_true");g.add_argument("--check",action="store_true")
    a=ap.parse_args();r=reproduce();t=json.dumps(r,indent=2,sort_keys=True)+"\n"
    p=Path(__file__).with_name("applications_results.json")
    if a.write:p.write_text(t,encoding="utf-8",newline="\n")
    elif p.read_text(encoding="utf-8")!=t:raise SystemExit("Application correspondence changed")
    print(json.dumps(r,indent=2,sort_keys=True))
if __name__=="__main__":main()

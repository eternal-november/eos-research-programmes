"""Pinned MRWS append-order composition in a selected civil simulator."""
from collections import Counter
from itertools import product, permutations
import json
from pathlib import Path
import sys

sys.path.insert(0,sys.argv[1])
import warehouse as w
from core import Event, Row, Use, admitted
from mrws.exceptions import SimulationError

# Candidate launch is old order bounded by five station appends after
# initial class 8: 7 at 5, 6 at 6, 5 at 10, 4 at 11, 3 at 12.
# Static authority: B prior to fault, D/C thereafter, named buffer S;
# the controller can select backup only from its own cut-local read.
def native(arm, moved, read, cap, deadline):
    wire=[]
    w.transport.send_message=lambda msg:wire.append(json.loads(msg))
    x=w.Fixture()
    station=x._goals["station"]
    A=x._robots
    now=0
    station._get_total_steps=lambda:now
    x._order_robots_assignment={1:["B","C","D"]}
    buffer=w.Carrier("named-buffer",())
    pickups=0
    steps=[]
    def content(obj):
        return [i.get_dependency() for i in obj.report_inventory()]
    def step(t,event):
        nonlocal now
        assert t>=now
        now=t
        steps.append([t,event])
    def pick(t,item,append):
        nonlocal pickups
        step(t,"pick "+str(item))
        assert pickups<cap
        pickups+=1
        d=A["D"]
        assert not content(d) and not d.battery_faulted_critical
        d.receive_inventory([w.items[item]])
        if append:
            station.interact(d)
    pick(5,7,True)
    pick(6,6,True)
    handling=0
    if moved:
        step(7,"salvage 4 to "+("buffer" if arm=="buffer" else "station"))
        A["B"].set_amount_of_items_to_transfer_next_time(1)
        assert content(A["B"])==[5,4]
        if arm=="buffer":
            buffer.receive_inventory(A["B"].transfer_inventory())
            assert content(buffer)==[4]
        else:
            station.interact(A["B"])
            assert content(station)==[8,7,6,4]
        assert content(A["B"])==[5]
        handling+=1
    step(8,"critical B loss")
    A["B"].battery_faulted_critical=True
    w.transport.transmit_robot_fault("B","battery-critical")
    assert wire[-1]["command"]=="ROBOTFAULT"
    observed=None
    if arm=="buffer" and read:
        step(9,"read named buffer")
        observed=content(buffer)
    # The side operation is physically separate and has its own port.
    def side():
        other=w.Carrier("side",[3])
        h=w.RobotHome("side-home","side",0,0)
        other.gone_home_to_clear_inv=True
        step(12,"side unload")
        h.interact(other)
        assert not content(other)
    if arm=="eager":
        pick(10,5,False)
        assert content(A["D"])==[5]
        try:
            station.interact(A["D"])
        except SimulationError as e:
            assert "dependency rule" in str(e)
        else:
            raise AssertionError("expected native order rejection")
        assert not content(A["D"]) and content(station)==[8,7,6,4]
        assert not x.completions
    elif arm=="compensate":
        # Counterfactual authorization, not an exposed stock station mission
        # operation: invoke inherited station pop and preserve the popped 4.
        step(9,"authorized station withdrawal")
        buffer.receive_inventory([station.pop_item_from_inventory()])
        assert content(station)==[8,7,6] and content(buffer)==[4]
        handling+=1
        pick(10,5,True)
        step(11,"retrieve withdrawn 4")
        A["D"].receive_inventory(buffer.transfer_inventory())
        station.interact(A["D"])
        handling+=1
        step(12,"C settles class 3")
        station.interact(A["C"])
    else:
        # A read of [] is distinct from a missing read. Only a positive
        # verified 4 can meet the three-pick cap across the indistinguishable
        # alternatives. Already-paid 7 and 6 are not discarded.
        enough=cap>=4-(observed==[4]) and deadline>=12
        if enough:
            pick(10,5,True)
            if observed==[4]:
                step(11,"retrieve buffered 4")
                A["D"].receive_inventory(buffer.transfer_inventory())
                station.interact(A["D"])
                handling+=1
            else:
                pick(11,4,True)
            step(12,"C settles class 3")
            station.interact(A["C"])
        assert bool(x.completions)==enough
    side()
    done=bool(x.completions)
    assert x.completions==([(1,12)] if done else [])
    assert [e["objName"] for e in wire if e["command"]=="ORDERCOMPLETE"]==(["order1"] if done else [])
    return dict(arm=arm,moved=moved,read=read,cap=cap,deadline=deadline,picks=pickups,
                observations=observed,handling=handling,settled=done,side=True,
                pending_station=content(station),inaccessible_B=content(A["B"]),
                residual_buffer=content(buffer),steps=steps)

def law(target, accepted, rank):
    remain=Counter(target)
    remain.subtract(accepted)
    return (all(n>=0 for n in remain.values()) and
            (not accepted or all(rank[k]<=rank[accepted[-1]] for k,n in remain.items() if n>0)))

def check_law():
    count=0
    rank={"a":2,"b":2,"c":1}
    def dec(s):
        return all(rank[x]>=rank[y] for x,y in zip(s,s[1:]))
    for a,b in product(range(5),repeat=2):
        for target in product(rank,repeat=a):
            rem=[t for t in set(permutations(target)) if dec(t)]
            for accepted in product(rank,repeat=b):
                if dec(accepted):
                    assert law(target,accepted,rank)==any(t[:b]==accepted for t in rem)
                    count+=1
    return count

def prove_family():
    # Compile the envelope before checking native outcomes. Observation
    # only partitions rows: the effect is the actual named custody.
    result={}
    for cap, deadline in product((3,4),(11,12)):
        rows=[]
        key=("pick-budget",)
        for moved,delivered in product((False,True),repeat=2):
            rec=((9,"dispatcher",moved),) if delivered else ()
            actual=frozenset({("buffer",4)}) if moved else frozenset()
            prior=tuple(Event(t,0,uses=(Use(key,1,cap,12),)) for t in (5,6))
            common=(Event(10,0,uses=(Use(key,1,cap,12),)),
                    Event(12,0,paid=("old",)),Event(12,1,paid=("side",)))
            rows.append(Row(rec,actual,prior,{
                "reuse":common+(Event(11,0,need=frozenset({("buffer",4)})),),
                "repick":common+(Event(11,0,uses=(Use(key,1,cap,12),)),),
            }))
        got=admitted(rows,"dispatcher",9,{"old":deadline,"side":12},("reuse","repick"))
        for view, actions in got.items():
            physical=[m for m,d in product((False,True),repeat=2)
                      if view==(((9,m),) if d else ())]
            direct=tuple(a for a,b in (("reuse",all(physical)),("repick",cap>=4))
                         if b and deadline>=12)
            assert actions==direct
        result[(cap,deadline)]=got
    return result

def main():
    out=[native("buffer",m,r,c,d) for m,r,c,d in
         product((False,True),(False,True),(3,4),(11,12))]
    verdicts=prove_family()
    for h in out:
        o=h["observations"]
        view=((9,o==[4]),) if o is not None else ()
        got=verdicts[(h["cap"],h["deadline"])][view]
        assert bool(got)==h["settled"] and h["side"]
        if got:
            assert h["picks"]==(3 if got[0]=="reuse" else 4)
    out.extend(native(a,True,True,3,12) for a in ("eager","compensate"))
    assert [v["settled"] for v in out[-2:]]==[False,True]
    assert [v["handling"] for v in out[-2:]]==[1,3]
    print(json.dumps(dict(cases=out,language_checks=check_law(), matched_views=sum(map(len,verdicts.values()))),indent=2,sort_keys=True))

if __name__=="__main__":
    main()

"""Reuse exact admission in MRWS ordered class service, not radio delivery."""
from pathlib import Path
from itertools import product
from collections import defaultdict
import importlib.util
import json
import sys

from core import Event, Row, Use, admitted

losses=(None,"B","C")
actions=tuple((b,c,opt) for b,c,opt in product((0,1),repeat=3))
parts=(("A",(7,6)),("B",(5,4)),("C",(3,)))
dues={"old":9,"unrelated":9}

def row(loss, report, cap, require_optional):
    receipt=((report,"dispatcher",loss or "none"),) if report else ()
    ready={("retained",name) for name in ("B","C") if name!=loss}
    facts=frozenset(ready | {("permit","D"),("permit","side")})
    key=("physical-pick-audit",)
    def pick(t,order,cost):
        return Event(t,order,need=frozenset((("permit","D"),)),
                     uses=(Use(key,cost,cap,9),))
    options={}
    for b,c,opt in actions:
        needed={("retained",name) for name,flag in (("B",b),("C",c)) if not flag}
        opts=[pick(6,0,2)]
        if b:opts.append(pick(7,0,2))
        if c:opts.append(pick(7,1,1))
        if opt:
            opts.append(pick(8,0,1))
            if require_optional:
                opts.append(Event(8,1,paid=("optional",)))
        opts.append(Event(9,0,need=frozenset(needed),paid=("old",)))
        opts.append(Event(9,1,need=frozenset((("permit","side"),)),paid=("unrelated",)))
        options[b,c,opt]=tuple(opts)
    return Row(receipt,facts,(),options)


def direct(worlds,cap,mut):
    return tuple(a for a in actions if (not mut or a[2]) and
            2+2*a[0]+a[1]+a[2]<=cap and
            all(w!="B" or a[0] for w in worlds) and all(w!="C" or a[1] for w in worlds))


def run_plan(test,report,cap,optional):
    targets=losses if test==2 else (("B","C") if test==1 else (None,))
    goals=dues|({"optional":8} if optional else {})
    results=admitted([row(s,report,cap,optional) for s in targets],"dispatcher",6,goals,actions)
    for name, got in results.items():
        worlds=tuple(x for x in targets if not name or (x or "none")==name[0][1])
        assert got==direct(worlds,cap,optional)
    return results


def fixture(up):
    p=up/"warehouse.py"
    m=importlib.util.spec_from_file_location("prior_mrws",p)
    w=importlib.util.module_from_spec(m)
    m.loader.exec_module(w)
    return w


def execute(w,loss,report,cap,optional,cases):
    x=w.Fixture()
    wire=[]
    w.transport.send_message=lambda raw:wire.append(json.loads(raw))
    robots=x._robots
    if loss:
        robots[loss].battery_faulted_critical=True
        w.transport.transmit_robot_fault(loss,"battery-critical")
        assert wire[-1]["command"]=="ROBOTFAULT" and wire[-1]["objName"]==loss
    # The selected native robot state is sampled by the fixture's authorized
    # local supervisor. Delivery/erasure of the sampling result is authored.
    observed=tuple(name for name in ("B","C") if robots[name].battery_faulted_critical)
    assert observed==((loss,) if loss else ())
    key=((report,"dispatcher",(observed[0] if observed else "none")),) if report and report<=6 else ()
    # admitted() exports the consumer tuple (sample_tick, contents), not actor.
    visible=tuple((t,z) for t,_,z in key)
    options=cases[visible]
    chosen=max(options,key=lambda a:(a[2],-2*a[0]-a[1])) if options else None
    station=x._goals["station"]
    picked=0
    done=[]
    optional_native=False
    if chosen is not None:
        b,c,opt=chosen
        x._order_robots_assignment={1:['D']+(['B'] if not b else [])+(['C'] if not c else [])}
        if opt:
            aux=w.Carrier("extra-check",())
            aux.receive_inventory([w.items[8]])
            picked+=1
            optional_native=aux.report_inventory_item_names()==["item8"]
        for name, classes in parts:
            # A is lost initially; B and C are used only with native retained
            # class evidence or reconstructed using D. Operative port is serial.
            replacement=name=="A" or name=="B" and b or name=="C" and c
            src=robots["D"] if replacement else robots[name]
            assert not src.battery_faulted_critical
            if replacement:
                src.receive_inventory([w.items[i] for i in classes])
                picked+=len(classes)
            else:
                assert tuple(i.get_dependency() for i in src.report_inventory())==classes
            done+=src.report_inventory_item_names()
            station.interact(src)
        assert picked==2+2*b+c+opt and picked<=cap
        assert done==["item"+str(i) for i in range(7,2,-1)]
        assert x.completions==[(1,9)]
        assert [s["objName"] for s in wire if s["command"]=="ORDERCOMPLETE"]==["order1"]
    else:
        assert not x.completions
    # An unrelated operator commits separate physical inventory custody even
    # when the shared reference refuses. This fixture uses no shared pick slot.
    independent=w.Carrier("local-inspection",[3])
    own=w.RobotHome("side","side",0,0)
    independent.gone_home_to_clear_inv=True
    assert independent.get_inventory_usage()==1
    own.interact(independent)
    assert independent.get_inventory_usage()==0
    return dict(lost=loss,notice=report,cap=cap,optional_required=optional,
                chosen=chosen,paid_old=x.completions,picked=picked,
                optional_staged=optional_native,side_return=True,accepted=done)


def main():
    up=Path(sys.argv[1])
    w=fixture(up)
    allrows=[]
    for r,c,opt in product((None,6,7),range(2,7),(False,True)):
        p=run_plan(2,r,c,opt)
        allrows.extend(execute(w,x,r,c,opt,p) for x in losses)
    positive=[x for x in allrows if x["notice"]==6 and x["cap"]==4 and not x["optional_required"]]
    assert all(x["paid_old"] for x in positive)
    assert [x["optional_staged"] for x in positive]==[True,False,True]
    no_receipt=[x for x in allrows if x["notice"] in (None,7) and x["cap"]==4]
    assert all(not x["paid_old"] and x["side_return"] for x in no_receipt)
    audited=sum(len(run_plan(n,d,c,m)) for n,d,c,m in
                product(range(3),(None,6,7),range(2,20),(False,True)))
    print(json.dumps(dict(native_cases=allrows,matched_observation_cells=audited),
                     sort_keys=True,indent=2))

if __name__=="__main__":
    main()

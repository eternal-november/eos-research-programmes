"""Single consuming cut. Physical return and rival debit execute in native fixtures."""
from itertools import product
from pathlib import Path
from collections import Counter
import importlib.util
import json
import subprocess
import sys
from live import pick_core

up=Path(sys.argv[1])
spec=importlib.util.spec_from_file_location("fixture",up/"isolated.py")
iso=importlib.util.module_from_spec(spec)
spec.loader.exec_module(iso)
n=iso.load_native(up/"native_source.py")

p=subprocess.Popen([sys.argv[2]],stdin=subprocess.PIPE,stdout=subprocess.PIPE,text=True)

def ask(*args):
    p.stdin.write(" ".join(map(str,args))+"\n")
    p.stdin.flush()
    return p.stdout.readline().strip()

def run(case,arm):
    cap,need,rival,kind,ret,lag,backup,cut=case
    assert ask("reset",cap)=="ok"
    g=iso.make(n,True)
    carrier,side=g.agents
    carrier.dir=n.Direction.RIGHT
    side.x,side.y,side.dir=1,3,n.Direction.RIGHT
    g._recalc_grid()
    a=n.Action
    def step(x,y):
        n.step(g,[x.value,y.value])
    def send(s,d,b,link=1):
        return int(ask("send",7,s,d,b,link))
    def clear():
        return (carrier.x,carrier.y)==(3,0) and carrier.carrying_shelf is None
    def read():
        return clear(),tuple(map(int,ask("sample",7).split()))
    for move in [a.NOOP,a.NOOP,a.TOGGLE_LOAD,a.FORWARD,a.RIGHT,a.RIGHT]:
        step(move,a.NOOP)
    assert clear()
    permit=4+lag<=7
    def install():
        # Exactly one warehouse action slot: the independent carrier always moves.
        step(a.FORWARD if ret else a.NOOP,a.FORWARD)
        if kind!="none":
            sender,target,link={"P-drop":("P","probe",0),"Q-drop":("Q","probe",0),
                "side-RX":("Side","probe",1),"P-RX":("P","probe",1)}[kind]
            rival_delivery=send(sender,target,rival,link)
            if cut!="after":
                assert rival_delivery==link
        assert send("Side","unrelated",1)==1
    def choose(state):
        c,radio=state
        return pick_core(7,cap,need,permit,c,backup,radio)
    initial=read()
    draft=choose(initial)
    if cut=="before":
        install()
    middle=read() if arm in {"check-twice","global"} else None
    if arm=="snapshot":
        chosen=draft
    elif arm=="check-twice":
        chosen=choose(middle)
    elif arm=="global":
        # Compute below at the consuming cut; this version invalidates on
        # any interposed update, including the independent carrier/send.
        chosen=None if cut!="after" else draft
    if cut=="between":
        install()
    actual=read()
    if arm=="scoped":
        # This inspection and the subsequent send occupy the same fenced
        # cut in the wrapper. No claim that stock simulators provide it.
        c,(xp,xq,rx)=actual
        chosen=None
        if permit and c and rx+need<=cap:
            if draft=="P" and xp+need<=cap:
                chosen="P"
            elif draft=="Q" and xq+need<=cap and backup:
                chosen="Q"
            else:
                chosen=choose(actual)
    if arm=="direct":
        c,(xp,xq,rx)=actual
        chosen=next((s for s,x,enabled in (("P",xp,True),("Q",xq,backup))
            if enabled and c and permit and x+need<=cap and rx+need<=cap),None)
    # Separate closed-form oracle: native rival charge and physical return
    # are computed from the event chart without consulting either checker.
    interposed=cut!="after"
    px=rival if interposed and kind in {"P-drop","P-RX"} else 0
    qx=rival if interposed and kind=="Q-drop" else 0
    rx=rival if interposed and kind in {"P-RX","side-RX"} else 0
    assert actual==(not (interposed and ret),(px,qx,rx))
    oracle=None
    if permit and actual[0] and need+rx<=cap:
        if need+px<=cap:
            oracle="P"
        elif backup and need+qx<=cap:
            oracle="Q"
    if arm in {"scoped","direct"}:
        assert chosen==oracle
    if arm=="global":
        assert middle is not None
    delivered=False
    paid=False
    debt=0
    if chosen:
        got=send(chosen,"owed",need)
        i=0 if chosen=="P" else 1
        debt=read()[1][i]-actual[1][i]
        assert got==int(actual[1][i]+need<=cap and actual[1][2]+need<=cap)
        assert debt==(need if actual[1][i]+need<=cap else 0)
        delivered=bool(got)
        paid=delivered and actual[0] and permit
    if cut=="after":
        install()
    assert (side.x,side.y)==(2,3)
    return dict(chosen=chosen,delivered=delivered,paid=paid,unlawful=bool(chosen and not actual[0]),
                rejected=bool(chosen and not delivered),failed_tx=debt if chosen and not delivered else 0,
                oracle=oracle)

stats={k:Counter() for k in ["snapshot","check-twice","global","scoped","direct"]}
witness={}
for case in product((4,5,6),(2,3,4),(1,2,3),("none","P-drop","Q-drop","side-RX","P-RX"),
                    (0,1),(0,3,4),(0,1),("before","between","after")):
    results={}
    for arm,st in stats.items():
        r=results[arm]=run(case,arm)
        st.update(cases=1,paid=int(r["paid"]),unlawful=int(r["unlawful"]),rejected=int(r["rejected"]),
                  failed_tx=r["failed_tx"],missed_feasible=int(bool(r["oracle"]) and not r["paid"]))
    assert results["scoped"]==results["direct"]
    cap,need,rival,kind,ret,lag,backup,cut=case
    if (cap,need,rival,lag,backup,cut)==(5,3,3,0,1,"between") and (
        not ret or kind=="none"):
        witness[kind+("/return" if ret else "")]=results
assert witness["none/return"]["check-twice"]["unlawful"]
assert witness["P-drop"]["scoped"]["chosen"]=="Q"
assert witness["side-RX"]["check-twice"]["failed_tx"]==3
assert witness["none"]["scoped"]["paid"] and not witness["none"]["global"]["paid"]
p.stdin.close()
assert p.wait()==0
print(json.dumps(dict(stats=stats,witness=witness),sort_keys=True))

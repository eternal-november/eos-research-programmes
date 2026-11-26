from collections import Counter
from itertools import permutations, product
from pathlib import Path
from types import SimpleNamespace as NS
import importlib.util
import json
import subprocess
import sys
from live import pick_core

up=Path(sys.argv[1])
spec=importlib.util.spec_from_file_location("fixture",up/"isolated.py")
iso=importlib.util.module_from_spec(spec);spec.loader.exec_module(iso)
n=iso.load_native(up/"native_source.py")
p=subprocess.Popen([sys.argv[2]],stdin=subprocess.PIPE,stdout=subprocess.PIPE,text=True,bufsize=1)
def ask(*args):
    p.stdin.write(" ".join(map(str,args))+"\n")
    p.stdin.flush()
    return p.stdout.readline().strip()

A=n.Action
bay=(2,0)

def replay(order,linked,kill,arm):
    assert ask("reset",5)=="ok"
    g=iso.make(n,True)
    c,s=g.agents
    c.dir=n.Direction.RIGHT
    s.x,s.y,s.dir=1,3,n.Direction.RIGHT
    g._recalc_grid()
    for command in (A.TOGGLE_LOAD,A.FORWARD,A.RIGHT,A.RIGHT):
        n.step(g,[command.value,A.NOOP.value])
    assert (c.x,c.y,c.dir,c.carrying_shelf)==(3,0,n.Direction.LEFT,None)

    hold=True
    terminal=None
    offered=False
    landed=[]
    allowed=[]
    refused=0
    side_tick=None
    trace=[]
    for tick,event in enumerate(order,1):
        if event=="offer":
            offered=True
        elif event in {"use1","use2"} and offered and terminal is None:
            radio=tuple(map(int,ask("sample",tick).split()))
            if arm=="direct":
                x,y,z=radio
                route=next((r for r,value in (("P",x),("Q",y)) if value+3<=5 and z+3<=5),None)
            else:
                route=pick_core(tick,5,3,True,True,True,radio)
            if route:
                sent=ask("send",tick,route,"owed",3,int(event=="use2" or linked))=="1"
                if sent:
                    terminal="applied"
                    landed.append(tick)
                    allowed.append((c.x,c.y)!=bay)
        elif event=="ask_cancel":
            if arm=="on-request":
                hold=False
        elif event=="fence":
            if terminal is None:terminal="canceled"
        elif event=="receipt":
            if terminal is not None:hold=False
        elif event=="reboot":
            # Volatile app restarts; native motion state and radio ledger both survive.
            if arm=="source-volatile" and kill in {"src","both"}:hold=False
            if arm=="broker-volatile" and kill in {"dst","both"}:terminal=None

        # An old owner can ask to enter every source tick. The guard replaces
        # only definite entry into this bay, not all movements at the source.
        cmd=A.FORWARD if (c.x,c.y)!=bay else A.NOOP
        dest=n.Agent.req_location(NS(x=c.x,y=c.y,dir=c.dir,req_action=cmd),g.grid_size)
        if hold and dest==bay and cmd==A.FORWARD:
            refused+=1
            cmd=A.NOOP
        n.step(g,[cmd.value,A.NOOP.value])
        if side_tick is None and (arm!="blanket" or not hold):
            n.step(g,[A.NOOP.value,A.FORWARD.value])
            assert (s.x,s.y)==(2,3)
            assert ask("send",tick,"Side","unrelated",1,1)=="1"
            side_tick=tick
        trace.append((event,hold,terminal,(c.x,c.y),tuple(landed)))
    return dict(sent=len(landed),unlawful=allowed.count(False),duplicate=max(0,len(landed)-1),
                return_denials=refused,side_at_one=int(side_tick==1),back=int((c.x,c.y)==bay),
                trace=trace)

arms=("pledge","direct","on-request","source-volatile","broker-volatile","blanket")
counts={k:Counter() for k in arms}
examples={}
actions=("offer","use1","use2","ask_cancel","fence","receipt","reboot")
for order in permutations(actions):
    if order.index("ask_cancel")>order.index("fence") or order.index("use1")>order.index("use2"):
        continue
    for link,kill in product((False,True),("src","dst","both")):
        out={arm:replay(order,link,kill,arm) for arm in arms}
        assert out["pledge"]==out["direct"]
        assert not out["pledge"]["unlawful"] and not out["pledge"]["duplicate"] and out["pledge"]["side_at_one"]
        for k,r in out.items():
            counts[k].update(cases=1,**{key:value for key,value in r.items() if key!="trace"})
        for name in ("on-request","source-volatile","broker-volatile"):
            if name not in examples and out[name]["unlawful"]:
                examples[name]={"order":order,"first_link":link,"restart":kill,"bad":out[name],"good":out["pledge"]}
        if "receipt-before-fence" not in examples and order.index("receipt")<order.index("fence") and (
            out["pledge"]["sent"]==0 and out["pledge"]["back"]==0):
            examples["receipt-before-fence"]={"order":order,"good":out["pledge"]}
assert set(examples)=={"on-request","source-volatile","broker-volatile","receipt-before-fence"}
assert counts["blanket"]["side_at_one"]==0
p.stdin.close()
assert p.wait()==0
print(json.dumps(dict(verdicts=counts,witness=examples),sort_keys=True))

from pathlib import Path
from types import SimpleNamespace as NS
from itertools import product
from collections import Counter
import json
import subprocess
import sys
import tempfile

import journal
from live import pick_core

n=journal.n
iso=journal.iso
A=n.Action
p=subprocess.Popen([sys.argv[2]],stdin=subprocess.PIPE,stdout=subprocess.PIPE,text=True,bufsize=1)
def ask(*args):
    p.stdin.write(" ".join(map(str,args))+"\n")
    p.stdin.flush()
    return p.stdout.readline().strip()

def plant():
    g=iso.make(n,True)
    c,s=g.agents
    c.dir=n.Direction.RIGHT
    s.x,s.y,s.dir=1,3,n.Direction.RIGHT
    g._recalc_grid()
    for command in (A.TOGGLE_LOAD,A.FORWARD,A.RIGHT,A.RIGHT):
        n.step(g,[command.value,A.NOOP.value])
    assert (c.x,c.y,c.dir,c.carrying_shelf)==(3,0,n.Direction.LEFT,None)
    return g

plan,tags=journal.plan()
i=tags["acceptA"]
key="run:7"
assert i==7
stock_due=tuple(plan[i])

class CrashPlant:
    def __init__(self,path,phase):
        self.path,self.phase=path,phase
        d=journal.open_db(path)
        for j,action in enumerate(plan[:i]):
            journal.apply(d,f"pref:{j}",action,"none","bundled")
        d.close()
        self.effect=None

    def query(self):
        d=journal.open_db(self.path)
        record=d.execute("select tick,result from receipt where intent=?",(key,)).fetchone()
        if record is not None:
            assert record[0]==8 and json.loads(record[1])==[1,0]
            assert journal.state(journal.reconstruct(d))["tick"]==8
        d.close()
        return record

    def advance(self,t):
        if t==5:
            journal.child(self.path,key,stock_due,self.phase,"bundled")
            if self.query():self.effect=t
        elif t==6:
            resumed=journal.child(self.path,key,stock_due,"none","bundled")
            assert resumed["cached"]==(self.effect==5)
            if self.effect is None:self.effect=t
            return "a7!" if self.query() else "-"
        return "-"

phases=("before-native","after-native","after-stage","after-commit")
native={}

def run(case,arm,core=None):
    ph,old,link1,link2,backup=case
    effect,terminal=(None,"-") if core else native[ph]
    assert ask("reset",5)=="ok"
    g=plant()
    c,s=g.agents
    hold=True
    return_tick=None
    clear_at_effect=None
    receipts=[]
    seen_terminal=False
    side=False
    def permitted(route):
        return route=="P" or backup
    for t in range(1,9):
        # Observer consumes native broker events only; the distinct plant
        # commit time is for auditing, except legitimate publication at 6.
        payload="-"
        if t==1 and old:
            payload=ask("notify",1,"P","a6!",1)
            assert payload=="a6!"
        if t in (2,6):
            assert ask("side",2)=="1"
            n.step(g,[A.NOOP.value,A.FORWARD.value])
            assert (s.x,s.y)==(2 if t==2 else 3,3)
            if t==6:side=True
        if core and t in (5,6):
            newly_published=core.advance(t)
            if newly_published!="-":terminal=newly_published
            effect=core.effect
        if t==effect:
            clear_at_effect=(c.x,c.y)!=(2,0)
        if t in (6,7) and terminal!="-" and not seen_terminal:
            radio=tuple(map(int,ask("sample",t).split()))
            if arm=="direct":
                x,y,rx=radio
                route=next((s for s,v in (("P",x),("Q",y))
                            if permitted(s) and v+3<=5 and rx+3<=5),None)
            else:
                route=pick_core(t,5,3,True,True,backup and arm!="primary-only",radio)
            if route:
                payload=ask("notify",t,route,terminal,int(link1 if t==6 else link2))
                assert payload in ("-",terminal)
                if t==6 and not link1:
                    assert tuple(map(int,ask("sample",t).split()))==(3,0,0)
        if payload!="-":
            receipts.append(payload)
            seen_terminal=seen_terminal or payload==terminal
            if payload==terminal or arm=="untyped":
                hold=False
        if t==5 and arm=="assume-committed":
            hold=False
        command=A.FORWARD if return_tick is None else A.NOOP
        dest=n.Agent.req_location(NS(x=c.x,y=c.y,dir=c.dir,req_action=command),g.grid_size)
        if hold and command==A.FORWARD and dest==(2,0):
            command=A.NOOP
        n.step(g,[command.value,A.NOOP.value])
        if return_tick is None and (c.x,c.y)==(2,0):
            return_tick=t
    assert clear_at_effect is not None and side
    assert return_tick is None or (c.x,c.y)==(2,0)
    if core:
        assert (effect,terminal)==native.setdefault(ph,(effect,terminal))
    return dict(terminal_cut=effect,side=side,unsafe=not clear_at_effect,
                returned=return_tick,wire_receipts=receipts)

witness={}
counts={k:Counter() for k in ("durable","direct","primary-only","untyped","assume-committed")}
for case in product(phases,(0,1),(0,1),(0,1),(0,1)):
    with tempfile.TemporaryDirectory() as loc:
        live=CrashPlant(str(Path(loc)/"plant.sqlite"),case[0])
        results={"durable":run(case,"durable",live)}
    results.update({arm:run(case,arm) for arm in counts if arm!="durable"})
    assert results["durable"]==results["direct"]
    ph,old,link1,link2,backup=case
    good=results["durable"]
    expected=6 if link1 else (7 if link2 and backup else None)
    assert good["returned"]==expected and not good["unsafe"]
    for k,r in results.items():
        counts[k].update(cases=1,unsafe=int(r["unsafe"]),returned=int(r["returned"] is not None))
    if case in [("after-commit",1,0,1,1),("after-native",0,0,0,1)]:
        witness["/".join(map(str,case))]=results
p.stdin.close()
assert p.wait()==0
print(json.dumps(dict(native_commits=native,verdicts=counts,witness=witness),sort_keys=True))

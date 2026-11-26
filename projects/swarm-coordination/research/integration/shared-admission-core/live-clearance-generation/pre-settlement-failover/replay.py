from pathlib import Path
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
assert i==7

def execute(path,ph,breakP,qSetup,qPath,ack,variant):
    assert ask("reset")=="ok"
    g=plant()
    c,s=g.agents
    d=journal.open_db(path)
    for j,action in enumerate(plan[:i]):
        journal.apply(d,f"pref:{j}",action,"none","bundled")
    d.close()
    key="run:7"
    payload=tuple(plan[i])
    def fact():
        d=journal.open_db(path)
        r=d.execute("select tick,result from receipt where intent=?",(key,)).fetchone()
        d.close()
        return r
    attempts=[]
    def send(t,sender,dst,bytes,link):
        r=ask("send",t,sender,dst,bytes,int(link))
        assert r in ("-",bytes)
        attempts.append([t,sender,dst,len(bytes),r!="-"])
        return r
    def invoke(t,r,phase):
        nonlocal effect
        if r!="r7?":return False
        result=journal.child(path,key,payload,phase,"bundled")
        record=fact()
        if record:
            assert record[0]==8 and json.loads(record[1])==[1,0]
            if effect is None:
                assert (c.x,c.y)!=(2,0)
                effect=t
        if result is not None:
            assert result["result"]==[1,0]
        return result is not None
    def source(t):
        nonlocal returned
        cmd=A.FORWARD if released and returned is None else A.NOOP
        n.step(g,[cmd.value,A.NOOP.value])
        if returned is None and (c.x,c.y)==(2,0):
            returned=t
    effect=returned=armed=None
    released=False
    initial=send(2,"P","owed","r7?",True)
    assert initial=="r7?"
    assert not invoke(2,initial,ph)
    assert (effect is not None)==(ph=="after-commit")
    for t in (3,4,5,6):
        source(t)
        if t in (3,6):
            assert ask("side",t)=="1"
            n.step(g,[A.NOOP.value,A.FORWARD.value])
        if t==4 and variant!="reactive":
            prep=send(t,"Side","setup","p7",qSetup)
            if prep=="p7":armed=t+2
    assert (s.x,s.y)==(3,3)
    # The decision sees physical receipt outcomes, not the evaluator's
    # path bit or database state. breakP is passed only to native RF.
    pHit=send(7,"P","owed","r7?",not breakP)
    settled=invoke(7,pHit,"none")
    if not settled and variant=="reactive":
        prep=send(7,"Side","setup","p7",qSetup)
        if prep=="p7":armed=9
    if not settled and armed is not None and armed<=7:
        radio=tuple(map(int,ask("sample",7).split()))
        x,y,z=radio
        if variant=="direct":
            route="Q" if y+3<=5 and z+3<=5 else None
        else:
            route=pick_core(7,5,3,True,True,True,radio)
        assert x>=3
        if route:
            assert route=="Q"
            settled=invoke(7,send(7,"Q","owed","r7?",qPath),"none")
    if settled:
        released=send(7,"Base","proof","a7!",ack)=="a7!"
    source(7)
    paid_by7=effect is not None
    # Route P can recover later. Same app key must return original effect
    # even after the source has used the qualified callback and reentered.
    end=send(12,"P","owed","r7?",True)
    assert end=="r7?"
    assert invoke(12,end,"none")
    d=journal.open_db(path)
    assert journal.state(journal.reconstruct(d))["tick"]==8
    assert d.execute("select count(*) from log where result='[1,0]'").fetchone()[0]==1
    d.close()
    if not released:
        # This recovery is intentionally outside the declared deadline.
        released=send(12,"Base","proof","a7!",True)=="a7!"
        assert released
        source(12)
    assert returned in (7,12) and returned>=effect
    return dict(effect=effect,return_tick=returned,paid_by7=paid_by7,
                service=returned==7,attempts=attempts)

phases=("before-native","after-native","after-stage","after-commit")
stats={k:Counter() for k in ("staged","direct","reactive")}
witness={}
for case in product(phases,(0,1),(0,1),(0,1),(0,1)):
    ph,breakP,qSetup,qPath,ack=case
    out={}
    for arm,ct in stats.items():
        with tempfile.TemporaryDirectory() as loc:
            v=out[arm]=execute(str(Path(loc)/"plant.db"),*case,arm)
        past=ph=="after-commit"
        action=(not breakP) or (arm!="reactive" and qSetup and qPath)
        assert v["paid_by7"]==bool(past or action)
        assert v["service"]==bool(action and ack)
        ct.update(cases=1,service=int(v["service"]),station_exact=1,
                  sent_bytes=sum(x[3] for x in v["attempts"]))
    assert out["staged"]==out["direct"]
    if case in (("after-stage",1,1,1,1),("after-commit",1,1,1,1),
                ("after-stage",1,1,0,1)):
        witness["/".join(map(str,case))]=out
p.stdin.close()
assert p.wait()==0
print(json.dumps(dict(verdicts=stats,witness=witness),sort_keys=True))

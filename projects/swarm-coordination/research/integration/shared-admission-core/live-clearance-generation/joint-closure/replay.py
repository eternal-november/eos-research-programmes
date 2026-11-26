"""Common native source, station and radio timeline with explicit receipt use."""
from collections import Counter
from itertools import product
from pathlib import Path
import json
import subprocess
import sys
import tempfile
import journal
from core import Event, Row, Use, check
from live import pick_core

n=journal.n
A=n.Action
p=subprocess.Popen([sys.argv[2]],stdin=subprocess.PIPE,stdout=subprocess.PIPE,text=True,bufsize=1)
plan,tags=journal.plan()
i=tags["acceptA"]
assert i==7
key="run:7"
bypass="Q"

def ask(*args):
    p.stdin.write(" ".join(map(str,args))+"\n")
    p.stdin.flush()
    return p.stdout.readline().strip()

def gate(proof,now_q):
    # Positive proof eliminates the still-unresolved row. No ack, or an ack
    # about another operation, is compatible with a Q retry due next tick.
    def charge(n):
        return Use(("radio","tx","Q"),n,5,4)
    worlds=(True,) if proof=="a7!" else (True,False)
    for paid in worlds:
        old=Event(7,0,uses=() if paid else (charge(3),),paid=("old",))
        earlier=() if not now_q else (Event(6,0,uses=(charge(now_q),)),)
        new=Event(6,1,uses=(charge(3),),paid=("extra",))
        r=Row((),frozenset(),earlier+(old,),{"extra":(new,)})
        if not check(r,"extra",6,{"old":7,"extra":6}):return False
    return True

def execute(db,phase,common,p_loss,q_setup,q_route,arm):
    assert ask("reset")=="ok"
    source=journal.iso.make(n,True)
    c,s=source.agents
    c.dir=n.Direction.RIGHT
    s.x,s.y,s.dir=1,3,n.Direction.RIGHT
    source._recalc_grid()
    for a in (A.TOGGLE_LOAD,A.FORWARD,A.RIGHT,A.RIGHT):
        n.step(source,[a.value,A.NOOP.value])
    assert (c.x,c.y)==(3,0)
    visitor=n.Agent(2,1,n.Direction.UP,0)
    source.agents.append(visitor)
    source.n_agents=3
    source._recalc_grid()
    d=journal.open_db(db)
    for j, action in enumerate(plan[:i]):
        journal.apply(d,f"pref:{j}",action,"none","bundled")
    assert d.execute("select tick from receipt where intent='pref:6'").fetchone()==(7,)
    d.close()

    def read_settlement():
        d=journal.open_db(db)
        a=d.execute("select tick,result from receipt where intent=?",(key,)).fetchone()
        d.close()
        if a: assert a[0]==8 and json.loads(a[1])==[1,0]
        return a is not None

    trans=[]
    def send(t,frm,to,body,link=True):
        result,meter=ask("send",t,frm,to,body,int(link)).split()
        debit=int(meter)
        assert debit in (0,len(body)) and (result=="-" or debit==len(body))
        assert result in ("-",body)
        trans.append((t,frm,to,body,result,debit))
        return result

    def invoke(body,phase):
        if body!="r7?":return False
        z=journal.child(db,key,tuple(plan[i]),phase,"bundled")
        if z is not None:
            assert z["result"]==[1,0]
            return True
        return False

    def return_source():
        n.step(source,[A.FORWARD.value,A.NOOP.value,A.NOOP.value])
        assert (c.x,c.y)==(2,0)

    assert not invoke(send(2,"P","owed","r7?"),phase)
    before=read_settlement() # evidence supplier and evaluator, not coordinator
    assert before==(phase=="after-commit")
    assert ask("side",3)=="1"
    n.step(source,[A.NOOP.value,A.FORWARD.value,A.NOOP.value])
    if common:
        # One event affects the probe stage and later the primary station
        # route; failed dispatch is still TX debit. Independent arm p_loss
        # can erase just the latter route.
        assert send(3,"Base","sink","p???",False)=="-"
        assert trans[-1][-1]==4
    q_ready=send(4,"Side","setup","p7",q_setup)=="p7"
    assert ask("side",6)=="1"
    n.step(source,[A.NOOP.value,A.FORWARD.value,A.NOOP.value])
    assert (s.x,s.y)==(3,3)
    # Genuine old late a6 exists, but is not a completion for r7.
    proof=send(6,"Base","proof","a7!" if read_settlement() else "a6")
    early_view=(q_ready,proof)
    if common:
        assert proof=="-" and trans[-1][-1]==0
    qualified=proof=="a7!"
    stay_valid=(c.x,c.y)!=(2,0)
    if qualified:
        return_source()
        entry=6
    else:
        entry=None
    now_q=int(ask("sample",6).split()[1])
    exact=gate(proof,now_q)
    assert exact==(qualified and now_q+3<=5)
    optional=exact if arm=="core" else (qualified and now_q+3<=5)
    if arm=="untyped":
        optional=proof!="-"
    chosen=None
    if optional:
        if arm=="latched":
            # A cached pre-release read is not valid after the known return.
            assert stay_valid
            chosen="bay"
            n.step(source,[A.NOOP.value,A.NOOP.value,A.FORWARD.value])
            assert (visitor.x,visitor.y)==(2,1)
        else:
            chosen="bypass"
        optional=send(6,bypass,"extra","x7!")=="x7!"
    unlawful=bool(optional and (not qualified or
                  (chosen=="bay" and (c.x,c.y)==(2,0))))

    q_used=False
    if not qualified:
        settled=invoke(send(7,"P","owed","r7?",not (common or p_loss)),"none")
        if not settled and q_ready:
            radio=tuple(map(int,ask("sample",7).split()))
            good=pick_core(7,5,3,True,True,True,radio)=="Q"
            assert good==(radio[1]+3<=5 and radio[2]+3<=5)
            if (good if arm!="direct" else radio[1]+3<=5 and radio[2]+3<=5):
                q_used=True
                settled=invoke(send(7,"Q","owed","r7?",q_route),"none")
    by7=read_settlement()
    if not qualified and by7 and send(8,"Base","proof","a7!")=="a7!":
        return_source()
        entry=8
    if not by7:
        assert invoke(send(13,"P","owed","r7?"),"none")
    # A reappearing primary safely retries even if the source already returned.
    assert invoke(send(18,"P","owed","r7?"),"none")
    if entry is None:
        assert send(18,"Base","proof","a7!")=="a7!"
        return_source()
    d=journal.open_db(db)
    assert d.execute("select count(*) from log where result='[1,0]'").fetchone()[0]==1
    assert journal.state(journal.reconstruct(d))["tick"]==8
    d.close()
    return dict(view=early_view, old_by7=by7,entry_before_deadline=entry,
                q=q_used,optional_paid=optional,unlawful=unlawful,
                transmissions=trans,actual_side=2,
                tx_requested_bytes=sum(len(s[3]) for s in trans)+2,
                native_tx_bytes=sum(s[-1] for s in trans)+2)

stats={}
witness={}
phases=("before-native","after-native","after-stage","after-commit")
for case in product(phases,(0,1),(0,1),(0,1),(0,1)):
    phase,common,p_loss,setup,path=case
    outputs={}
    for arm in ("core","direct","untyped","latched"):
        with tempfile.TemporaryDirectory() as temp:
            x=outputs[arm]=execute(str(Path(temp)/"a.db"),*case,arm)
        ct=stats.setdefault(arm,Counter())
        in_scope=bool(setup and path)
        ct.update(total=1,positive_envelope=int(in_scope),
                  positive_old_paid=int(in_scope and x["entry_before_deadline"] in (6,8)),
                  old_paid=int(x["old_by7"]), entered_by8=int(x["entry_before_deadline"] is not None),
                  unsafe=int(x["unlawful"]),optional=int(x["optional_paid"]),
                  q=int(x["q"]),requested=x["tx_requested_bytes"],charged=x["native_tx_bytes"])
        if arm in ("core","direct"):
            assert not x["unlawful"]
            assert bool(x["entry_before_deadline"])==bool(x["old_by7"])
            if in_scope:assert x["old_by7"]
            assert x["optional_paid"]==(phase=="after-commit" and not common)
    assert outputs["core"]==outputs["direct"]
    if case in (("after-stage",0,1,1,1),("after-commit",1,0,1,1),
                ("after-stage",1,0,1,1),("after-commit",0,1,1,1)):
        witness["/".join(map(str,case))]=outputs
m=witness["after-stage/1/0/1/1"]["core"]
k=witness["after-commit/1/0/1/1"]["core"]
assert m["view"]==k["view"]==(True,"-") and m["q"]==k["q"]==True
assert m["entry_before_deadline"]==k["entry_before_deadline"]==8
p.stdin.close()
assert p.wait()==0
print(json.dumps({"verdicts":stats,"witness":witness},sort_keys=True))

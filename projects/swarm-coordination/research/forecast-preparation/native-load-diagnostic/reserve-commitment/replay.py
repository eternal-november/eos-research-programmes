"""A pre-mission action changes actual reserve pose and native delivery time."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json
import sys
import numpy as np
import isolated as iso

up=Path(sys.argv[1])
old=(up/"prior.py").read_text()
m={}
mark="\nexperiments={}\n"
assert old.count(mark)==1
exec(compile(old.split(mark)[0],str(up/"prior.py"),"exec"),m)
A=m["A"];n=m["n"];ask=m["ask"];wire=m["w"]
archive=json.loads((up/"archive.json").read_text())
MODES=(0,1,"wait")

def execute(x,truth,choice):
    assert ask("reset")=="ok"
    g=m["plant"](x,False,True)
    c,h=g.agents
    h.x,h.y,h.dir=4,1,n.Direction.RIGHT
    observer=n.Agent(0,4,n.Direction.RIGHT,0)
    g.agents.append(observer)
    g.n_agents=3
    g._recalc_grid()
    actions=[]
    def act(a=A.NOOP,b=A.NOOP,e=A.NOOP):
        n.step(g,[a.value,b.value,e.value])
        actions.append([a.name,b.name,e.name])
        assert len({(i.x,i.y) for i in g.agents})==3
    def move_to(y):
        # One-dimensional bay lock, no transit into the cargo workspace.
        if h.y==y:return 0
        d=n.Direction.UP if y<h.y else n.Direction.DOWN
        turns=0
        while h.dir!=d:
            v=h.dir
            b=A.LEFT if (h.dir==n.Direction.RIGHT and d==n.Direction.UP) else A.RIGHT
            act(b=b)
            assert h.dir!=v
            turns+=1
            assert turns<=2
        dy=abs(y-h.y)
        for _ in range(dy):act(b=A.FORWARD)
        assert (h.x,h.y)==(4,y)
        return turns+dy
    def send(t,frm,to,body,link=True):
        r,d=ask("send",t,frm,to,body,int(link)).split()
        assert r in (body,"-") and int(d) in (0,len(body))
        return r,int(d)

    # Only the known initial lane X exists at selection. The independent
    # future obstacle realization is materialized below, after preparation.
    prep=0 if choice=="wait" else move_to(2*(x^choice))
    assert prep==(0 if choice=="wait" else 2)
    assert c.carrying_shelf is not None
    opt,d0=send(0,"P","extra","job!",h.y==1)
    # Even failure of the optional scheduled attempt has a recorded debit.
    assert d0==4 and (opt=="job!")==bool(choice=="wait")

    if truth:
        g.shelfs[0].x,g.shelfs[0].y=2,2*x
        g._recalc_grid()
    act(a=A.FORWARD)
    blocked=c.x==1
    assert blocked==truth
    y=x^blocked
    path=iso.route(n,g,0,(3,2*y),set())
    assert path is not None
    for a in path:act(a=a)
    assert c.carrying_shelf is not None and (c.x,c.y)==(3,2*y)
    act(e=A.FORWARD)
    assert (observer.x,observer.y)==(1,4)
    assert ask("side",15)=="1"

    # Landing is a named physical fact, no helper change was authorized
    # before this cut. Room for actual local transport uses current poses.
    delay=move_to(2*y)
    expected=(2 if choice=="wait" else (0 if choice==truth else 4))
    assert delay==expected
    close=abs(h.x-c.x)+abs(h.y-c.y)==1
    result,d1=send(20+delay,"Q","owed","pay",close)
    assert result=="pay" and d1==3
    return {"prepare_actions":prep,"correction_delay":delay,"old_on_fast_cut":delay==0,
            "optional":opt=="job!","side":True,"charge":d0+d1+1,
            "terminal":[list((c.x,c.y)),list((h.x,h.y))],
            "actual_command_tape":actions}

records={}
L={}
for x,M,a in product((0,1),(0,1),MODES):
    z=execute(x,M,a)
    entry=(z["correction_delay"],int(not z["optional"]))
    if (M,a) in L:assert L[M,a]==entry
    L[M,a]=entry
    records[f"{x}/{M}/{a}"]=z
wire.stdin.close()
assert wire.wait()==0

def choose(e,price):
    h=[archive["cases"][f"{i}/switch/source/{e}"][0] for i in (0,1)]
    symbols=sorted(set(h[0])|set(h[1]))
    P=[F(1,4),F(3,4)]
    def risk(rule,law):
        p=P[law]
        return sum(F(h[law].get(o,0),16)*sum(prob*(L[t,a][0]+L[t,a][1]*price)
                   for t,prob in enumerate((1-p,p))) for o,a in zip(symbols,rule))
    vals=[]
    for r in product(MODES,repeat=len(symbols)):
        rr=[risk(r,l) for l in (0,1)]
        vals.append((max(rr),sum(rr)/2))
    optimum=min(a for a,b in vals)
    lower=min(b for a,b in vals)
    # Same observation posterior, no action based on future pallet.
    derived=[(int(o[-1]) if o in ("b0","b1") and price<F(1,2) else "wait") for o in symbols]
    assert optimum==lower==max(risk(derived,i) for i in (0,1))
    return dict(worst_cost=str(optimum),policy=list(zip(symbols,derived)))

dec={}
for e,c in product((0,1),(F(0),F(1,4),F(1,2),F(3,4))):
    dec[f"{e}/{c}"]=choose(e,c)
print(json.dumps(dict(native=records,minimax=dec),sort_keys=True))

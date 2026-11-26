"""Source-backed first-return cut, with an authored asynchronous time envelope."""
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

A=n.Action
noop,fw,left,right=A.NOOP,A.FORWARD,A.LEFT,A.RIGHT
dirs=(n.Direction.LEFT,n.Direction.UP,n.Direction.RIGHT,n.Direction.DOWN)
turns=((),(left,), (right,right),(right,))
bay=(2,0)

def plant(distance,heading):
    g=iso.make(n,True)
    c,s=g.agents
    c.dir=n.Direction.RIGHT
    s.x,s.y,s.dir=1,3,n.Direction.RIGHT
    g._recalc_grid()
    n.step(g,[A.TOGGLE_LOAD.value,noop.value])
    for _ in range(distance):
        n.step(g,[fw.value,noop.value])
    # Find the installed orientation by native steps before stamping.
    if heading==0: rotated=(right,right)
    elif heading==1: rotated=(left,)
    elif heading==2: rotated=()
    else: rotated=(right,)
    for t in rotated:n.step(g,[t.value,noop.value])
    assert (c.x,c.y,c.dir,c.carrying_shelf)==(2+distance,0,dirs[heading],None)
    return g

# East-to-west is two turns; North-to-west is left; South-to-west right.
def shortest(distance,heading):
    return turns[heading]+(fw,)*distance

def go(g,seq):
    for a in seq:n.step(g,[a.value,noop.value])

def away(g):
    c=g.agents[0]
    return (c.x,c.y)!=bay

native_words=0
for d,h in product((1,2),range(4)):
    word=shortest(d,h)
    for k in range(len(word)):
        for prefix in product(tuple(A),repeat=k):
            g=plant(d,h)
            go(g,prefix)
            assert away(g),(d,h,prefix)
            native_words+=1
    g=plant(d,h)
    go(g,word)
    assert not away(g)
    native_words+=1

def support(H,shape):
    if shape=="shared":
        return [(i,H-i) for i in range(H+1)]
    return list(product(range(H+1),repeat=2))

def verify(case,a,b,head,trace,policy):
    d,visible,H,shape,cap,need,rival,backup=case
    note_seen=(head,) if visible else (0,2)
    joint=support(H,shape)
    min_return=min(len(shortest(d,h)) for h in note_seen)
    stage_bound=(max(x for x,_ in joint)+max(y for _,y in joint))
    exact=max(x+y for x,y in joint)<min_return
    if policy=="snapshot":valid=True
    elif policy=="inclusive":valid=max(x+y for x,y in joint)<=min_return
    elif policy=="separate":valid=stage_bound<min_return
    elif policy=="composed":valid=exact
    else:
        # Direct universal test on the cube of histories, no max-summary.
        valid=all(x+y<len(shortest(d,h)) for h in note_seen for x,y in joint)
    assert ask("reset",cap)=="ok"
    g=plant(d,head)
    word=shortest(d,head)
    steps=((word+(noop,)*(a+b))[:a+b] if trace=="earliest" else (noop,)*(a+b))
    if rival:
        assert ask("send",5,"P","probe",rival,0)=="0"
    go(g,steps[:a])  # receipt delivery cut, no read of g
    go(g,steps[a:])  # separate broker effect cut, no read of motion
    radio=tuple(map(int,ask("sample",5).split()))
    if policy=="direct":
        x,y,z=radio
        route=next((r for r,l,e in (("P",x,True),("Q",y,backup))
                    if valid and e and l+need<=cap and z+need<=cap),None)
    else:
        route=pick_core(5,cap,need,True,valid,backup,radio)
    oracle=None
    if exact:
        if need+rival<=cap:oracle="P"
        elif backup and need<=cap:oracle="Q"
    if policy in {"composed","direct"}:assert route==oracle
    # Separate verifier checks actual order and actual use; excluded from policy.
    clear_truth=away(g)
    assert clear_truth==(trace=="stay" or a+b<len(word))
    delivered=False
    if route:delivered=ask("send",5,route,"owed",need,1)=="1"
    assert delivered==bool(route)
    assert ask("send",5,"Side","unrelated",1,1)=="1"
    n.step(g,[noop.value,fw.value])
    s=g.agents[1]
    assert (s.x,s.y)==(2,3)
    return dict(delivered=delivered,unauthorized=delivered and not clear_truth,
                false_refusal=not delivered and oracle is not None,choice=route)

stats={k:Counter() for k in ("snapshot","inclusive","separate","composed","direct")}
witness={}
for c in product((1,2),(False,True),range(1,5),("shared","rect"),(5,),(2,3),(0,3),(False,True)):
    d,vis,H,kind,cap,need,rival,back=c
    for a,b in support(H,kind):
        for h,trace in product(range(4) if vis else (0,2),("earliest","stay")):
            rs={}
            for arm,st in stats.items():
                r=rs[arm]=verify(c,a,b,h,trace,arm)
                st.update(cases=1,**{label:int(r[label]) for label in
                                    ("delivered","unauthorized","false_refusal")})
            assert rs["composed"]==rs["direct"]
            if vis and a==1 and need==3 and rival==3 and back and h==2 and trace=="earliest":
                if (d,H,kind,b) in [(1,2,"shared",1),(1,3,"shared",2),(2,3,"shared",2),(1,2,"rect",2)]:
                    witness[f"{d}/{H}/{kind}/{b}"]=rs
assert witness["1/2/shared/1"]["composed"]["choice"]=="Q"
assert witness["1/2/shared/1"]["separate"]["false_refusal"]
assert witness["1/3/shared/2"]["inclusive"]["unauthorized"]
assert witness["2/3/shared/2"]["composed"]["choice"]=="Q"
assert witness["1/2/rect/2"]["snapshot"]["unauthorized"]
p.stdin.close()
assert p.wait()==0
print(json.dumps(dict(first_return_native_words=native_words,verdicts=stats,witness=witness),sort_keys=True))

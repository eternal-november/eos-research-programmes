"""Finite civil logistics recovery; protect a fixed old move and radio transfer."""
from collections import Counter, defaultdict
from functools import cache
from itertools import product
from pathlib import Path
from types import SimpleNamespace
from core import Row, Use, Event, check
import json
import sys

# Import the published native fixture definitions without running its main sweep.
path=Path(sys.argv[1])/"prior/replay.py"
ns={}
marker="\nrows={}\n"
source=path.read_text()
assert source.count(marker)==1
exec(compile(source.split(marker)[0],str(path),"exec"),ns)
fixture=SimpleNamespace(**ns)

Q=fixture.Q
ROUTES=("Direct","Bypass")
CLEAR=("bay","clear")
DIRECT="Direct"
BYPASS="Bypass"
COST=4
FIRST=4
NEW_DUE=6

def older_sender(b):
    return BYPASS if b else DIRECT

def budget(sender,n):
    return Use(("tx",sender),n,COST,4)

def core_law(b,t,old,route):
    # Old task owns full TX capacity at its appointed cut. A motion at that
    # tick happens first. A dispatch needs actual clearance, not a cache.
    changes={"drop":frozenset({CLEAR})} if b else {"add":frozenset({CLEAR})}
    release=Event(old,0,**changes)
    old_tx=Event(old,1,uses=(budget(older_sender(b),4),),paid=("old",))
    send=Event(t,2,need=frozenset({CLEAR}) if route==DIRECT else frozenset(),
               uses=(budget(route,1),),paid=("new",))
    row=Row((),frozenset({CLEAR}) if b else frozenset(),(release,old_tx),{route:(send,)})
    return check(row,route,t,{"new":NEW_DUE,"old":old})

def direct_law(b,t,old,route):
    # Here |t-old| is at most the native one-second horizon throughout.
    actual_clear=bool(b) if t<old else not bool(b)
    return t<=NEW_DUE and route!=older_sender(b) and (route!=DIRECT or actual_clear)

def classify(W,old,t,checking):
    return tuple(r for r in ROUTES if all(checking(b,t,old,r) for b in W))

def solver(worlds,old,tags,kind):
    """Total service exact game, and opportunistic safe acquisition tree."""
    law=core_law if kind=="core" else direct_law
    def read(row,j):
        return (row[1][j],row[2][j]) if tags else row[1][j]
    @cache
    def synth(ix,qs,t):
        bits={worlds[i][0] for i in ix}
        for route in classify(bits,old,t,law):
            return route,len(ix)
        best=("-",0)
        if t>=NEW_DUE:return best
        for j in qs:
            groups=defaultdict(list)
            for i in ix:groups[read(worlds[i],j)].append(i)
            if len(groups)==1:continue
            opts={v:synth(tuple(hold),tuple(q for q in qs if q!=j),t+1)
                  for v,hold in sorted(groups.items())}
            count=sum(c for _,c in opts.values())
            if count>best[1]:best=((j,{v:s for v,(s,_) in opts.items()}),count)
        return best
    return synth(tuple(range(len(worlds))),Q,FIRST)

def select(tree,rec,tags):
    elapsed=0
    while not isinstance(tree,str):
        j,branch=tree
        obs=(rec[1][j],rec[2][j]) if tags else rec[1][j]
        tree=branch[obs]
        elapsed+=1
    return tree,FIRST+elapsed

def native_execute(g,b,t,old,route,assert_safe=True):
    hit=legit=old_hit=False
    for epoch in range(FIRST, max(old,t)+1):
        if epoch==old:
            g.step(fixture.A.FORWARD)
            assert g.clear()!=bool(b)
            old_hit=fixture.ask("send",old,older_sender(b),"Old","old!",1)[0]=="old!"
        if epoch==t and route!="-":
            legit=route!=DIRECT or g.clear()
            hit=fixture.ask("send",t,route,"Job","n",1)[0]=="n"
    if assert_safe:
        assert old_hit and ((legit and hit)==(route!="-"))
        assert (g.side.x,g.side.y)==(2,3)
    return hit,legit,old_hit

for b,t,old,r in product((0,1),range(4,9),(6,7,8),ROUTES):
    assert core_law(b,t,old,r)==direct_law(b,t,old,r)

samples={}
for limit in (1,2):
    allrows=[]
    for mode,word,b in product([m for m in fixture.MODES if len(m)<=limit],fixture.WORDS,(0,1)):
        _,rec,_=fixture.native_fixture(word,b,mode,FIRST)
        allrows.append(rec)
    samples[limit]=tuple(sorted(set(allrows)))

out={}
for limit,old,tags in product((1,2),(6,7,8),(False,True)):
    W=samples[limit]
    key=f"{limit}/{old}/{'qualified' if tags else 'bare'}"
    tree,leaves=solver(W,old,tags,"core")
    assert (tree,leaves)==solver(W,old,tags,"direct")
    assert (leaves==len(W))==(limit==1 and old>6 and tags)
    ct=Counter()
    for b,word,mode in product((0,1),fixture.WORDS,[m for m in fixture.MODES if len(m)<=limit]):
        g,rec,_=fixture.native_fixture(word,b,mode,FIRST)
        route,t=select(tree,rec,tags)
        assert t<=NEW_DUE
        expected=direct_law(b,t,old,route) if route!="-" else False
        assert expected==(route!="-")
        hit,lawful,preserved=native_execute(g,b,t,old,route)
        if hit:ct[f"paid_at_{t}"]+=1
        else:ct["withheld"]+=1
        ct["old_preserved"]+=int(preserved)
    out[key]={"worlds":len(W),"distinct_rows_served":leaves,"native_executions":ct}

# Two controls: a pending early send can block the old job; at the shared
# cut the old sender gets its legitimate priority but the physical change
# makes a formerly clear reading insufficient.
g,_,_=fixture.native_fixture((1,)*6,1,(),FIRST)
assert native_execute(g,1,5,7,BYPASS,False)==(True,True,False)
g,_,_=fixture.native_fixture((1,)*6,1,(),FIRST)
assert native_execute(g,1,6,6,DIRECT,False)==(True,False,True)
fixture.p.stdin.close()
assert fixture.p.wait()==0
print(json.dumps({"results":out,"control_wrong_sender_blocks_old":True,
                  "control_expired_clearance_still_has_radio_callback":True},sort_keys=True))

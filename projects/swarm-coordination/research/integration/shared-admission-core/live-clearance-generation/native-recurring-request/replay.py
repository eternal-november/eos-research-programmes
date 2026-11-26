from pathlib import Path
from collections import Counter
from itertools import product
import importlib.util
import ast
import json
import sys

up=Path(sys.argv[1])
spec=importlib.util.spec_from_file_location("fixture",up/"isolated.py")
iso=importlib.util.module_from_spec(spec);spec.loader.exec_module(iso)
n=iso.load_native(up/"native_source.py")
source=iso.read(up/"native_source.py")
defs=iso.funcs(source,["_get_default_obs","_get_info"])
ns=vars(iso).copy()
ns.update(_LAYER_AGENTS=0,_LAYER_SHELFS=1)
exec(compile(ast.Module(body=defs,type_ignores=[]),str(up/"native_source.py"),"exec"),ns)
A=n.Action
goal=(4,1)
start=(2,0)

def json_default(obj):
    if hasattr(obj,"tolist"):return obj.tolist()
    raise TypeError(type(obj))

def make(radius):
    g=iso.make(n,False)
    g.fast_obs=False
    g.normalised_coordinates=False
    g.sensor_range=radius
    g._obs_sensor_locations=(2*radius+1)**2
    g._make_obs=lambda a:ns["_get_default_obs"](g,a)
    g._get_info=lambda:ns["_get_info"](g)
    g.max_steps=1000
    return g

def step(g,cmd):
    o,r,done,truncated,info=n.step(g,[cmd.value,A.NOOP.value])
    assert not done and not truncated and len(r)==2 and info=={}
    return int(round(r[0]*2))

def walk(g,where):
    seq=iso.route(n,g,0,where,set())
    assert seq is not None
    credit=0
    for cmd in seq:credit+=step(g,cmd)
    assert (g.agents[0].x,g.agents[0].y)==where
    return credit

def deliver(g,which):
    c=g.agents[0]
    shelf=g.shelfs[which-1]
    home=(shelf.x,shelf.y)
    assert shelf in g.request_queue and c.carrying_shelf is None
    assert walk(g,home)==0
    assert step(g,A.TOGGLE_LOAD)==0 and c.carrying_shelf is shelf
    assert walk(g,goal)==1 and c.has_delivered and shelf not in g.request_queue
    arrival=g._cur_steps
    assert walk(g,home)==0
    assert step(g,A.TOGGLE_LOAD)==1 and not c.has_delivered and c.carrying_shelf is None
    depart=g._cur_steps
    assert walk(g,start)==0
    while c.dir != n.Direction.DOWN:
        assert step(g,A.RIGHT)==0
    assert step(g,A.NOOP)==0
    return arrival,depart

def view(g):
    a=[(c.x,c.y,c.dir.value,c.carrying_shelf.id if c.carrying_shelf else None,
        c.has_delivered,c.prev_x,c.prev_y,c.req_action.value) for c in g.agents]
    return dict(exact_stock=[g._make_obs(c) for c in g.agents],poses=a,
                shelves=[(s.id,s.x,s.y) for s in g.shelfs],
                request_ids=[s.id for s in g.request_queue],grid=g.grid.copy(),
                current_tick=g._cur_steps,last_reward=[0,0],old_ack=None)

def freeze(v):
    return json.dumps(v,default=json_default,sort_keys=True)

def pref(radius,returned,extra):
    g=make(radius)
    ev=[]
    if returned:
        ev=[deliver(g,1),deliver(g,2)]
    while g._cur_steps < 80+extra: assert step(g,A.NOOP)==0
    assert g._cur_steps==80+extra
    return g,ev

def continuation(g,issued,receipt,arm):
    old_credit=issued
    accepted=0
    if arm=="replay-all" or (arm=="effect-key" and not receipt):
        deliver(g,1)
        old_credit+=1
        accepted=1
    # New order with the same A shelf is legitimate only once B has run and
    # the native queue advances back to A. In the suppress-all arm the old
    # activation was never even attempted as a retry. That does not make A's
    # old historical obligation paid.
    active=[s.id for s in g.request_queue]
    if active==[2]:deliver(g,2)
    assert [s.id for s in g.request_queue]==[1]
    new_credit=0 if arm=="tombstone-shelf" else 1
    if new_credit:deliver(g,1)
    return old_credit, new_credit, accepted

stats={k:Counter() for k in ("replay-all","tombstone-shelf","effect-key")}
w={}
for radius,extra in product((0,1,2,4),range(5)):
    unpaid,_=pref(radius,False,extra)
    paid,ev=pref(radius,True,extra)
    assert freeze(view(unpaid))==freeze(view(paid))
    assert unpaid._cur_inactive_steps!=paid._cur_inactive_steps
    if radius==4 and extra==0:
        w.update(cut=paid._cur_steps,paid_native_cuts=ev,
                 inactive_count_hidden=[unpaid._cur_inactive_steps,paid._cur_inactive_steps],
                 native_view_bytes=len(freeze(view(paid))),ending_request=view(paid)["request_ids"])
    for arm,st in stats.items():
        for issued in (0,1):
            g,_=pref(radius,issued,extra)
            old,new,retry=continuation(g,issued,bool(issued),arm)
            st.update(cases=1,old_exact=int(old==1),new=int(new),duplicate=max(0,old-1),
                      old_missing=int(old==0),attempts=retry)
assert stats["replay-all"]["duplicate"]==20
assert stats["tombstone-shelf"]["new"]==0
assert stats["effect-key"]["old_exact"]==stats["effect-key"]["new"]==40
# The lifts differ only in which valid application request authorized the
# first A acceptance. Stock RWARE never gets that application key.
g1,ev1=pref(4,True,0)
g2,ev2=pref(4,True,0)
assert ev1==ev2 and g1._cur_inactive_steps==g2._cur_inactive_steps
assert freeze(view(g1))==freeze(view(g2))
assigned1=[(7,ev1[0][0]),(9,ev1[1][0])]
assigned2=[(6,ev2[0][0]),(9,ev2[1][0])]
w["keyed_lifts"]={
    "history_a":assigned1,"history_b":assigned2,
    "decisive_recovered_key":7,
    "recover_old_needs_retry":[not any(k==7 for k,_ in hist) for hist in (assigned1,assigned2)]
}
print(json.dumps(dict(view_pairs=20,verdicts=stats,witness=w),sort_keys=True))

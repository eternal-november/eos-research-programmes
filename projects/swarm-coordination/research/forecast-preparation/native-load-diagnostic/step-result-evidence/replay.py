"""The privileged information is the earlier native API cut, not a hidden parity oracle."""
from collections import Counter
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import ast
import json
import sys
import isolated as iso

up=Path(sys.argv[1])
old=(up/"prior.py").read_text()
marker="\nexperiments={}\n"
assert old.count(marker)==1
prior={}
exec(compile(old.split(marker)[0],str(up/"prior.py"),"exec"),prior)
ask=prior["ask"];wire=prior["w"];n=prior["n"];A=prior["A"]
g=dict(iso.__dict__,_LAYER_AGENTS=0,_LAYER_SHELFS=1)
code=iso.funcs(ast.parse((up/"native_source.py").read_text()),
               ("_get_default_obs","_make_obs","_get_info"))
exec(compile(ast.Module(body=code,type_ignores=[]),str(up/"native_source.py"),"exec"),g)

def selected_observer(p,radius=1):
    p.sensor_range=radius
    p.image_obs=p.image_dict_obs=p.fast_obs=p.normalised_coordinates=False
    p._obs_sensor_locations=(2*radius+1)**2
    p._get_default_obs=lambda a:g["_get_default_obs"](p,a)
    p._make_obs=lambda a:g["_make_obs"](p,a)
    p._get_info=lambda:g["_get_info"](p)
    return p

def capture(x,M,rule,mode,erase):
    assert ask("reset")=="ok"
    p=selected_observer(prior["plant"](x,M,True))
    at,sd=p.agents
    def send(t,s,d,p,link=True):
        y,b=ask("send",t,s,d,p,int(link)).split()
        assert y in ("-",p) and int(b) in (0,len(p))
        return y,int(b)
    old,b0=send(0,"Q","owed","old")
    assert old=="old"
    observing=n.step(p,[A.FORWARD.value,A.NOOP.value])
    ob=observing[0][0]
    assert observing[1:]==([0.,0.],False,False,{})
    native_post=tuple(map(int,ob["self"]["location"]))
    assert native_post==(1 if M else 2,2*x)
    # An adapter reads the documented default unnormalized self location
    # immediately after its fixed named action; it never reads req_action.
    code=("b"+("1" if native_post[0]==1 else "0")) if mode=="source" else "ok"
    main,b1=send(1,"P","owed",code,not erase)
    ext,b2=send(2,"Side","proof","job!")
    assert ext=="job!" and ask("side",2)=="1"
    # Continue old routes even when the evidence did not arrive. Changed
    # receiver policy preserves the old lane after the same blocked step.
    y=(1-x if (native_post[0]==1 and rule=="switch") else x)
    p_target=(3,2*y)
    plan=iso.route(n,p,0,p_target,set())
    assert plan is not None and len(plan)<=14
    for a in list(plan)+[A.NOOP]*(14-len(plan)):
        n.step(p,[a.value,A.NOOP.value])
    n.step(p,[A.NOOP.value,A.FORWARD.value])
    assert (at.x,at.y)==p_target and at.carrying_shelf and (sd.x,sd.y)==(1,4)
    return main,b0+b1+b2+1,y,ext,len(plan)

def canonical(o):
    if isinstance(o,dict):return {k:canonical(v) for k,v in o.items()}
    if isinstance(o,(list,tuple)):return [canonical(v) for v in o]
    if hasattr(o,"tolist"):return o.tolist()
    return o

def alias_control():
    both=[]
    delta=[]
    for start in (3,4):
        p=selected_observer(prior["plant"](0,False,True))
        at=p.agents[0]
        at.x=start
        at.carrying_shelf.x=start
        p.shelfs[0].x,p.shelfs[0].y=0,3
        p._recalc_grid()
        st=n.step(p,[A.FORWARD.value,A.NOOP.value])
        both.append(canonical(st))
        delta.append(at.x-start)
        assert at.req_action==A.FORWARD and at.x==4
    assert both[0]==both[1] and delta==[1,0]
    return dict(stock_next_results_equal=True,forward_command_retained_both=True,
                actual_x_displacements=delta)

def deterministic_minimax(c):
    points=sorted(set(c[0])|set(c[1]))
    # The posterior is tied after erasure. 50/50 in a tie equalizes
    # symmetric laws. Enumerate rational choice probabilities explicitly.
    return min(max(F(sum(c[i][o]*(x if i==0 else 1-x)
                         for o,x in zip(points,w)),16) for i in (0,1))
               for w in product((F(0),F(1,2),F(1)),repeat=len(points)))

entries={}
for law,rule,engine,interference in product((0,1),("switch","keep"),("source","status"),(0,1)):
    h=Counter();stats=Counter()
    for x,u,b in product((0,1),range(4),(0,1)):
        M=u<(1 if law==0 else 3)
        msg,charged,y,opt,c=capture(x,M,rule,engine,bool(interference and b))
        h[msg]+=1
        stats.update(optional_preserved=int(opt=="job!"),side_physical=1,charged=charged,
                     actual_lane_changes=int(y!=x),motions=c)
    entries[law,rule,engine,interference]=(h,stats)

out={}
for interference in (0,1):
    source=[entries[law,"switch","source",interference][0] for law in (0,1)]
    status=[entries[law,"switch","status",interference][0] for law in (0,1)]
    error=deterministic_minimax(source)
    # Direct same-information likelihood under the two fixed laws.
    lower=F(sum(min(source[0][o],source[1][o]) for o in set(source[0])|set(source[1])),32)
    assert error==lower==(F(3,8) if interference else F(1,4))
    assert status[0]==status[1] and deterministic_minimax(status)==F(1,2)
    assert all(entries[law,"keep","source",interference][0]==source[law] for law in (0,1))
    out[str(interference)]=dict(error=str(error),wrong_reserve_cost="1/2",
                                regret=str(error/2),same_exact_as_paid_pair=True)

record={f"{l}/{r}/{e}/{i}":[h,s] for (l,r,e,i),(h,s) in entries.items()}
clipping=alias_control()
wire.stdin.close()
assert wire.wait()==0
print(json.dumps(dict(cases=record,minimax=out,clipping_control=clipping),sort_keys=True))

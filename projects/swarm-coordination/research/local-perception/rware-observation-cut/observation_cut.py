"""Selected native RWARE local perception and one-mover action semantics."""
from collections import defaultdict
from functools import lru_cache
from itertools import product
from pathlib import Path
from types import SimpleNamespace as NS
import ast
import json
import numpy as np
import isolated as iso

ROOT=Path(__file__).resolve().parent
native=iso.load_native(ROOT/"native_source.py")
tree=iso.read(ROOT/"native_source.py")
writer=[x for x in tree.body if isinstance(x,ast.ClassDef) and x.name=="_VectorWriter"]
d=iso.funcs(tree,["_get_default_obs","_make_obs"])
# Gym is used only to ask the already-fixed flat vector size. Destination
# planning and coordinate encoding never use this shim.
ctx=dict(np=np,gym=NS(spaces=NS(flatdim=lambda a:a)),_LAYER_AGENTS=0,_LAYER_SHELFS=1)
exec(compile(ast.Module(body=writer+d,type_ignores=[]),str(ROOT/"native_source.py"),"exec"),ctx)
A,D=native.Action,native.Direction
MODES=("dict-normalized","flat-normalized","dict-absolute","flat-absolute")
def make(n,r,p,d,mode,marker=False):
    # Open local patch, with one stationary remote entity and a remote requested shelf.
    native.Agent.counter=native.Shelf.counter=0
    ag=native.Agent(*p,d,0)
    side=native.Agent(0,0,D.UP,0)
    if marker in ("marked-pair","right-marked","unmarked-pair"):
        shelfs=[native.Shelf(2,1),native.Shelf(4,1),native.Shelf(n-1,n-1)]
        request=shelfs[0] if marker=="marked-pair" else shelfs[1] if marker=="right-marked" else shelfs[-1]
    else:
        shelfs=[native.Shelf(2,1) if marker else native.Shelf(n-1,n-1)]
        request=shelfs[0]
    world=NS(grid_size=(n,n),grid=np.zeros((2,n,n),dtype=int),msg_bits=0,n_agents=2,
       agents=[ag,side],shelfs=shelfs,request_queue=[request],
       goals=[(0,n-1)],highways=np.zeros((n,n),dtype=bool),reward_type=native.RewardType.TWO_STAGE,
       np_random=iso.OneChoice(),_cur_steps=0,_cur_inactive_steps=0,max_steps=20,max_inactivity_steps=None,
       _get_info=lambda:{},normalised_coordinates=mode.endswith("-normalized"),
       fast_obs=mode.startswith("flat"),image_obs=False,image_dict_obs=False,
       sensor_range=r,_obs_sensor_locations=(2*r+1)**2,observation_space=[8+7*(2*r+1)**2]*2)
    world._recalc_grid=lambda:native._recalc_grid(world)
    world._is_highway=lambda x,y:native._is_highway(world,x,y)
    world._get_default_obs=lambda a:ctx["_get_default_obs"](world,a)
    world._make_obs=lambda a:ctx["_make_obs"](world,a)
    world._recalc_grid()
    return world

def freeze(x):
    if isinstance(x,dict):return {k:freeze(v) for k,v in x.items()}
    if isinstance(x,np.ndarray):return {"dtype":str(x.dtype),"values":x.tolist()}
    if isinstance(x,(tuple,list)):return [freeze(v) for v in x]
    return x

def first_output(w):
    return freeze(w._make_obs(w.agents[0]))

def loc(obs,mode):
    return obs["values"][:2] if mode.startswith("flat") else obs["self"]["location"]["values"]

def case(n,r,axis,heading):
    c=n//2
    center=(c,c)
    left=list(center);left[axis]-=1;right=list(center);right[axis]+=1
    poses=(tuple(left),tuple(right))
    out={}
    for mode in MODES:
        obs=[first_output(make(n,r,p,heading,mode)) for p in poses]
        assert (obs[0]==obs[1])==(mode=="dict-normalized")
        expected=[[0,0],[0,0]] if mode=="dict-normalized" else poses
        if mode=="flat-normalized":
            expected=[[float(np.float32(z/(n-1))) for z in p] for p in poses]
        assert [list(loc(a,mode)) for a in obs]==[list(a) for a in expected]
        out[mode]=[loc(a,mode) for a in obs]
    starts=[]
    trials=0
    for start in poses:
        found=set()
        for one,two in product(A,repeat=2):
            w=make(n,r,start,heading,"dict-normalized")
            native.step(w,(one,A.NOOP))
            native.step(w,(two,A.NOOP))
            ag=w.agents[0]
            if (ag.x,ag.y)==center:found.add((one.name,two.name))
            assert (w.agents[1].x,w.agents[1].y)==(0,0)
            trials+=1
        assert len(found)==1,found
        starts.append(next(iter(found)))
    assert starts[0][0]!=starts[1][0]
    # Flat normalization retains enough actual input to select, rather than
    # asking the observation oracle for the latent pose.
    steps=0
    mapping={tuple(o):u for o,u in zip(out["flat-normalized"],starts)}
    for start in poses:
        w=make(n,r,start,heading,"flat-normalized")
        for action in mapping[tuple(loc(first_output(w),"flat-normalized"))]:
            native.step(w,(A[action],A.NOOP));steps+=1
        assert (w.agents[0].x,w.agents[0].y)==center
    return out,starts,trials,steps

def policy_probe(mode,marker):
    n,r=7,1
    kinds=marker if isinstance(marker,tuple) else (marker,)
    root=tuple((x,3,D.UP.value,k) for x,k in product((2,4),kinds))
    target=(3,3)
    choices=(A.NOOP,A.FORWARD,A.LEFT,A.RIGHT)
    @lru_cache(None)
    def initial_obs(s):
        x,y,d,k=s
        return json.dumps(first_output(make(n,r,(x,y),D(d),mode,k)),sort_keys=True)
    @lru_cache(None)
    def transition(s,a):
        x,y,d,k=s
        w=make(n,r,(x,y),D(d),mode,k)
        obs,reward,term,trunc,info=native.step(w,(a,A.NOOP))
        ag=w.agents[0]
        assert reward==[0.0,0.0] and not term and not trunc and not info
        next_state=ag.x,ag.y,ag.dir.value,k
        o=json.dumps(freeze(obs[0]),sort_keys=True)
        assert o==initial_obs(next_state)
        return next_state,o
    def split(actions):
        table=defaultdict(set)
        for s,o in actions:table[o].add(s)
        return tuple(tuple(sorted(v)) for _,v in sorted(table.items()))
    @lru_cache(None)
    def plan(budget,worlds):
        if all(s[:2]==target for s in worlds):return ()
        if not budget:return None
        for a in choices:
            p=[plan(budget-1,v) for v in split(transition(s,a) for s in worlds)]
            if all(q is not None for q in p):return a.name,p
        return None
    common=split((s,initial_obs(s)) for s in root)
    for horizon in range(13):
        ans=[plan(horizon,w) for w in common]
        if all(p is not None for p in ans):break
    else:raise AssertionError("unreached in bound")
    probes=transition.cache_info().currsize
    if marker in (True,"marked-pair") and mode=="dict-normalized":
        whole=common[0]
        assert len(whole)==2
        assert len(split(transition(s,A.LEFT) for s in whole))==1
        # Moving forward from the ambiguous start makes the fixed common
        # requested shelf visible only in the left history.
        a,b=[transition(s,A.FORWARD) for s in whole]
        assert a[1]!=b[1]
        assert [sum(x["shelf_requested"][0] for x in json.loads(out)["sensors"])
                for _,out in (a,b)]==[1,0]
        if marker=="marked-pair":
            def without_request(o):
                z=json.loads(o)
                for row in z["sensors"]:row.pop("shelf_requested")
                return z
            assert without_request(a[1])==without_request(b[1])
    return {"minimum":horizon,"native_transition_queries":probes,"policy":ans}

def live_request():
    # The unrelated old service occurs before the probe. The unmodified
    # stock queue replacement runs exactly when the old shelf crosses
    # its destination. No controller gets the chosen shelf ID.
    poses=((2,3),(4,3))
    actual=[]
    by={}
    for seed,pay,(x,y) in product((0,1),(False,True),poses):
        w=make(7,1,(x,y),D.UP,"dict-normalized","unmarked-pair")
        old=w.shelfs[-1];side=w.agents[1]
        side.x,side.y,side.dir=1,6,D.UP
        side.carrying_shelf=old;old.x,old.y=side.x,side.y
        w.goals=[(1,5)]
        w.np_random=np.random.default_rng(seed)
        w._recalc_grid()
        pre=first_output(w)
        obs,reward,_,_,_=native.step(w,(A.NOOP,A.FORWARD if pay else A.NOOP))
        assert freeze(obs[0])==pre # requested shelf still lies outside the receiver's crop
        assert reward==([0.0,0.5] if pay else [0.0,0.0])
        assert (side.x,side.y)==((1,5) if pay else (1,6))
        chosen=w.request_queue[0]
        assert chosen is (w.shelfs[1-seed] if pay else old)
        obs,reward,_,_,_=native.step(w,(A.FORWARD,A.NOOP))
        assert reward==[0.0,0.0]
        o=freeze(obs[0])
        requests=sum(s["shelf_requested"][0] for s in o["sensors"])
        assert requests==int(pay and x==(4 if seed==0 else 2))
        # The exact native fresh-snapshot input to the planning stage.
        equivalent="right-marked" if pay and seed==0 else "marked-pair" if pay else "unmarked-pair"
        assert o==first_output(make(7,1,(x,2),D.UP,"dict-normalized",equivalent))
        by[seed,pay,x]=o
        elapsed=None
        if pay:
            # Only the known calibration (which cell has the unique mark)
            # and the acquired request flag select this next maneuver.
            marks_left=(seed==1)  # declared producer-to-place mapping, not learnt from the flag
            start_left=bool(requests)==marks_left
            for a in (A.RIGHT if start_left else A.LEFT,A.FORWARD,
                      A.RIGHT if start_left else A.LEFT,A.FORWARD):
                native.step(w,(a,A.NOOP))
            assert (w.agents[0].x,w.agents[0].y)==(3,3)
            assert (side.x,side.y)==(1,5)
            elapsed=w._cur_steps
            assert elapsed==6  # one prior-source tick plus five observation/action ticks
        actual.append([seed,pay,x,chosen.id,requests,elapsed])
    assert by[0,True,4]==by[1,True,2]  # marked locally in both histories, opposite positions
    assert by[0,True,2]==by[1,True,4]  # neutral locally in both histories, opposite positions
    return actual

def main():
    rows=trials=steps=0;witness=None
    for n in (7,9,11):
      for r in (0,1,2):
       for axis,heads in ((0,(D.UP,D.DOWN)),(1,(D.LEFT,D.RIGHT))):
        for head in heads:
            out,starts,k,w=case(n,r,axis,head)
            trials+=k;steps+=w;rows+=1
            if (n,r,axis,head)==(7,1,0,D.UP):witness={"location":out,"needed_sequences":starts}
    assert witness is not None
    plans={m:policy_probe(config,has) for m,config,has in (("normalized-dict-marker","dict-normalized",True),("normalized-dict-no-marker","dict-normalized",False),("normalized-flat-marker","flat-normalized",True),("normalized-dict-paired-request","dict-normalized","marked-pair"),("normalized-dict-paired-neutral","dict-normalized","unmarked-pair"),("normalized-dict-unknown-request","dict-normalized",("marked-pair","right-marked")))}
    assert [plans[m]["minimum"] for m in plans]==[5,8,2,5,8,8]
    print(json.dumps({"actual_dispatch_and_probe":live_request(),"exact_native_policies":plans,"pairs":rows,"native_observation_pairs":4*rows,
          "native_action_trials":trials,"observation_selected_steps":steps,"witness":witness},sort_keys=True,separators=(",",":")))
if __name__=="__main__":
    main()

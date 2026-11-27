"""Native stale-reference counterexample with an equal final ordered queue."""
from itertools import product
from observation_cut import make,native,A,D,np,freeze,first_output
import json

def start(pose,seed):
    w=make(7,1,(pose,3),D.UP,"dict-normalized","unmarked-pair")
    old=w.agents[1];old.x,old.y=1,6;old.dir=D.UP
    courier=native.Agent(3,0,D.DOWN,0)
    w.agents.append(courier);w.n_agents+=1
    load=w.shelfs[-1];load.x,load.y=1,6
    z=native.Shelf(6,6);w.shelfs.append(z)
    old.carrying_shelf=load
    w.request_queue=[load]
    w.goals=[(1,5),(3,0)]
    w.np_random=np.random.default_rng(seed);w._recalc_grid()
    return w

def move(w,a=A.NOOP,b=A.NOOP,c=A.NOOP):
    o,r,term,trunc,info=native.step(w,(a,b,c))
    assert not term and not trunc and not info
    return freeze(o[0]),r

def phase(seed,pose):
    w=start(pose,seed);view=[first_output(w)]
    q=lambda:tuple(o.id for o in w.request_queue)
    o,r=move(w,b=A.FORWARD);view.append(o)
    assert r==[0.,.5,0.]
    if q()[0] not in (1,2):return None
    original=q()[0]
    receipt=("prior-delivery",1,3,original)
    o,r=move(w,a=A.FORWARD);view.append(o)
    old_probe=any(x["shelf_requested"][0] for x in o["sensors"])
    assert old_probe==(pose==2*original)
    for a in (A.LEFT,A.LEFT,A.FORWARD):
        o,r=move(w,a=a);view.append(o);assert r==[0.,0.,0.]
    assert (w.agents[0].x,w.agents[0].y,w.agents[0].dir)==(pose,3,D.DOWN)
    if original==1:left,right=A.LEFT,A.RIGHT
    else:left,right=A.RIGHT,A.LEFT
    courier=w.agents[2]
    actions=(right,A.FORWARD,left,A.FORWARD,A.TOGGLE_LOAD,A.LEFT,A.LEFT,A.FORWARD,right,A.FORWARD)
    for t,a in enumerate(actions,1):
        o,r=move(w,c=a);view.append(o)
        if t<10:assert r==[0.,0.,0.]
        if t==5:
            assert courier.carrying_shelf.id==original
            assert (courier.x,courier.y)==(2*original,1)
    assert r==[0.,0.,.5] and (courier.x,courier.y)==(3,0)
    if q()!=(4,):return None
    assert w._cur_steps==15
    # Current ordered queue, publication count and current detector are
    # all visible to the comparator, but the as-of assignment is not.
    latest=(w._cur_steps,q(),tuple(view))
    # Explicitly compute the recovered decision from the observed old flag
    # and the actual source record chosen by the prior delivery.
    left_pose=bool(old_probe)==(receipt[3]==1)
    turn=A.LEFT if left_pose else A.RIGHT
    needed=[]
    for a,b in product(A,repeat=2):
        # Only inspector moves in these final two slots. Accepted native
        # headings and unit motions are exact through the original body.
        g=w.agents[0]
        v=native.Agent(g.x,g.y,g.dir,0)
        for x in (a,b):
            v.req_action=x
            if x in (A.LEFT,A.RIGHT):v.dir=v.req_direction()
            if x==A.FORWARD:v.x,v.y=v.req_location(w.grid_size)
        if (v.x,v.y)==(3,3):needed.append((a,b))
    assert needed==[(turn,A.FORWARD)]
    move(w,a=turn);move(w,a=A.FORWARD)
    assert (w.agents[0].x,w.agents[0].y)==(3,3) and w._cur_steps==17
    assert (w.agents[1].x,w.agents[1].y)==(1,5)
    return {"receipt":receipt,"latest":latest,"needed":turn.name,"flag":old_probe}

def main():
    rows={}
    for seed in range(32):
      for pose in (2,4):
        o=phase(seed,pose)
        if o is not None:rows[seed,pose]=o
    left=next(seed for (seed,pose),v in rows.items() if v["receipt"][3]==1)
    right=next(seed for (seed,pose),v in rows.items() if v["receipt"][3]==2)
    checks=[]
    for flag,p0,p1 in ((True,2,4),(False,4,2)):
        a,b=rows[left,p0],rows[right,p1]
        assert a["latest"]==b["latest"] and a["needed"]!=b["needed"]
        assert a["flag"]==b["flag"]==flag
        checks.append([flag,p0,p1,a["needed"],b["needed"]])
    print(json.dumps({"admitted_seed_pose_pairs":len(rows),"witness_seeds":[left,right],
        "same_ordered_current_queue":[4],"equal_full_histories":checks,"initial_source_tick":1,"cut":15,"deadline":17},
        sort_keys=True,separators=(",",":")))
if __name__=="__main__":main()

"""Exact native motion when a queue reference arrives after the first read."""
from collections import defaultdict
from functools import lru_cache
from itertools import product
import json
from observation_cut import make,first_output,freeze,native,A,D

MARKS=("marked-pair","right-marked")
ACTION=(A.NOOP,A.FORWARD,A.LEFT,A.RIGHT)
worlds=tuple((x,3,D.UP.value,k) for x,k in product((2,4),MARKS))
TARGET=(3,3)
@lru_cache(None)
def perceive(s):
    x,y,d,k=s
    return json.dumps(first_output(make(7,1,(x,y),D(d),"dict-normalized",k)),sort_keys=True)
@lru_cache(None)
def update(s,a):
    x,y,d,k=s
    w=make(7,1,(x,y),D(d),"dict-normalized",k)
    out,reward,term,trunc,info=native.step(w,(a,A.NOOP))
    assert reward==[0.0,0.0] and not trunc and not term and not info
    g=w.agents[0]
    s1=(g.x,g.y,g.dir.value,k)
    assert perceive(s1)==json.dumps(freeze(out[0]),sort_keys=True)
    return s1

def all_obs(t,s,arrival,quality):
    # State introduced only when it is causally known; a completion
    # acknowledgement is common and never treated as queue identity.
    if t<arrival:return perceive(s),None
    if quality=="bound":return perceive(s),s[3]
    if quality=="generic":return perceive(s),"published"
    if quality=="unbound-old":return perceive(s),"earlier-left"
    raise ValueError(quality)

def split(B,t,arrival,quality):
    d=defaultdict(set)
    for s in B:d[all_obs(t,s,arrival,quality)].add(s)
    # Positional ordering uses only stable observed strings.
    return tuple((o,tuple(sorted(v))) for o,v in sorted(d.items()))

def solve(arrival,quality,forgot=False):
    @lru_cache(None)
    def plan(t,left,B):
        if all(xy[:2]==TARGET for xy in B):return ()
        if left==0:return None
        for a in ACTION:
            pieces=split((update(s,a) for s in B),t+1,arrival,quality)
            paths=[]
            for o,V in pieces:
                if forgot and t+1==arrival:
                    # Forced amnesia ablation (non-narrowing): all native grid
                    # states in the no-past model compatible with this output.
                    V=tuple(sorted(s for s in universe if all_obs(t+1,s,arrival,quality)==o))
                    assert V
                result=plan(t+1,left-1,V)
                if result is None:break
                paths.append((o,result))
            else:return (a.name,tuple(paths))
        return None
    # The admitted initial pose family remains the same. A deliberately
    # amnesic restarted worker may not know which first action ran.
    def reach_in(depth):
        S=set(worlds)
        for _ in range(depth):S={update(s,a) for s in S for a in ACTION}
        return S
    universe=reach_in(arrival) if forgot else ()
    for horizon in range(13):
        roots=tuple((o,plan(0,horizon,B)) for o,B in split(worlds,0,arrival,quality))
        if all(p is not None for _,p in roots):break
    else:return None,0
    for s in worlds:
        step=0;cpu=dict(roots)[all_obs(0,s,arrival,quality)]
        while cpu:
            a,paths=cpu
            s=update(s,A[a]);step+=1
            cpu=dict(paths)[all_obs(step,s,arrival,quality)]
        assert s[:2]==TARGET and step<=horizon
    return horizon,plan.cache_info().currsize

def frozen_memory():
    # Validate the full common prefix on one evolving native environment.
    # The sole logical payload from the earlier probe is who had local mark.
    witnesses={}
    for x,k in product((2,4),MARKS):
        w=make(7,1,(x,3),D.UP,"dict-normalized",k)
        flag=None
        for tick,u in enumerate((A.FORWARD,A.LEFT,A.LEFT,A.FORWARD),1):
            obs,_,_,_,_=native.step(w,(u,A.NOOP))
            if tick==1:
                flag=any(s["shelf_requested"][0] for s in obs[0]["sensors"])
        current=freeze(obs[0])
        assert not any(s["shelf_requested"][0] for s in current["sensors"])
        if k in witnesses:
            assert witnesses[k]["same_input"]==current
            assert witnesses[k]["flag"]!=flag
        witnesses[k]={"same_input":current,"flag":flag}
        turn=A.LEFT if flag==(k=="marked-pair") else A.RIGHT
        for a in (turn,A.FORWARD):native.step(w,(a,A.NOOP))
        assert (w.agents[0].x,w.agents[0].y)==TARGET
        assert w._cur_steps==6
    return {"native_trajectories":4,"past_payload_bits_for_frozen_prefix":1,
        "pose_lost_if_only_current_observation_plus_bound_reference":True}

def main():
    rows=[solve(t,"bound") for t in range(9)]
    generic=[solve(t,"generic")[0] for t in (0,1,4,8)]
    wrong=[solve(t,"unbound-old")[0] for t in (0,1,4,8)]
    assert all(x==8 for x in [*generic,*wrong])
    restart=[solve(t,"bound",True)[0] for t in (1,2,3,4)]
    assert [x[0] for x in rows]==[5,5,6,6,6,7,8,8,8]
    assert restart==[5,6,6,7]
    print(json.dumps({"frozen_prefix_memory":frozen_memory(),"bound_min":[x[0] for x in rows],"semantic_cuts_evaluated":sum(x[1] for x in rows),
          "generic_completion_only":generic,"unbound_old_bit":wrong,"restarted_no_past":restart,
          "unique_native_transitions":update.cache_info().currsize},sort_keys=True,separators=(",",":")))
if __name__=="__main__":main()

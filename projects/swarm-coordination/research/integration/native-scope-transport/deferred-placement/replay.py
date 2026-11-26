"""Controlled 7x7 RWARE native dispatch, one placement under a later designation."""
from collections import deque
from itertools import product
from hashlib import sha1
from pathlib import Path
import json
import sys
import numpy as np
from control import BAYS,E,S,W,N,choose,best_delay,safe_pending
from fallback import upon

up=Path(sys.argv[1]).resolve()
for n,sha in [('native_source.py','9797bf36970d5eb14fef7a150fab7562c450dff6'),
              ('rware_rotation.py','9803d1607cccf88a4a58e58f18528232790056be'),
              ('isolated.py','610a81b316a9b3538106387467c4e2f4437b28f4')]:
    b=(up/n).read_bytes()
    assert sha1(f"blob {len(b)}\0".encode()+b).hexdigest()==sha
sys.path.insert(0,str(up))
import rware_rotation as rw
api=rw.engine(up/'native_source.py')
A,D=api.Action,api.Direction
HEAD={E:D.RIGHT,S:D.DOWN,W:D.LEFT,N:D.UP}
CENTER=(3,3)
BAY={E:(5,3),S:(3,5),N:(3,1)}
OUT={E:(6,3),S:(3,6),N:(3,0)}
STAGING={E:(5,1),S:(1,5),N:(1,1)}
ENTRY={E:(5,2),S:(2,5),N:(2,1)}
GOAL={E:(5,4),S:(4,5),N:(4,1)}
NAMES={E:'east',S:'south',N:'north',W:'west'}
DUE=5
OLD_TICKS=2
F,T,Z=A.FORWARD,A.TOGGLE_LOAD,A.NOOP
L,R=A.LEFT,A.RIGHT

def shortest_turn(start,goal):
    seen={start}; q=deque([(start,())])
    while q:
        h,p=q.popleft()
        if h==goal:return p
        for delta,code in ((1,R),(-1,L)):
            x=(h+delta)%4
            if x not in seen:
                seen.add(x);q.append((x,p+(code,)))
    raise AssertionError('orientation space closed incorrectly')


def exhaustive(deadline,steps,cut,b):
    # Independent reference: selected direction remains unknown until cut.
    # Before it, only rotate or wait; after, straight arm once aligned.
    # Enumerate reachable headings, then calculate both contingent choices.
    current={E}
    for _ in range(cut):
        current={(h+d)%4 for h,d in product(current,(-1,0,1))}
    states={}
    for h in current:
        states[h]=tuple(
            needed for needed in BAYS if b!=needed and
            any(c!=needed and c!=b and cut+len(shortest_turn(h,c))+steps+1<=deadline
                for c in BAYS))
    return states


def local_designation(env):
    # Fixed read cells, each at Manhattan distance <=3 from old center.
    # Use actual executed arrival, not the command to the selected loader.
    present=[]
    for arm,(x,y) in ENTRY.items():
        assert sum(abs(a-b) for a,b in zip(CENTER,(x,y)))<=3
        if env.grid[0,y,x]:
            present.append(arm)
    return present[0] if len(present)==1 else None


def run(blocked,need,mode,cut=0,heading=E,fixed=None,erase=False,marker_tick=1,earlier_need=None):
    ix={e:i+1 for i,e in enumerate(BAYS)}
    pos=((2,3),*(STAGING[x] for x in BAYS),(0,6),OUT[blocked])
    dirs=(D.RIGHT,*(D.DOWN if x==E else D.RIGHT for x in BAYS),D.RIGHT,HEAD[(blocked+2)%4])
    extras=tuple((None,c) for c in ((0,0),(6,0),(6,6),(0,5),(6,5)))
    api.Agent.counter=api.Shelf.counter=0
    agents=[api.Agent(*p,d,0) for p,d in zip(pos,dirs,strict=True)]
    shelves=[api.Shelf(*p) for p in (*pos,*(c for _,c in extras))]
    for a,s in zip(agents,shelves):a.carrying_shelf=s
    env=rw.iso.NS(grid_size=(7,7),msg_bits=0,n_agents=len(agents),agents=agents,
                  grid=np.zeros((2,7,7),dtype=int),highways=np.zeros((7,7),dtype=bool),
                  shelf_count=len(shelves),shelfs=shelves,request_queue=shelves[:6],
                  reward_type=api.RewardType.TWO_STAGE,_cur_steps=0,
                  _cur_inactive_steps=0,max_steps=50,max_inactivity_steps=None,
                  _make_obs=lambda a:None,_get_info=lambda:{})
    env._recalc_grid=lambda:api._recalc_grid(env)
    env._is_highway=lambda x,y:api._is_highway(env,x,y)
    env.goals=[CENTER,*GOAL.values(),(1,6),OUT[blocked]]
    for x,y in env.goals:env.highways[y,x]=True
    env.np_random=rw.iso.NS(choice=lambda options:min((s for s in options if s.id>=7),key=lambda s:s.id))
    env._recalc_grid()

    def step(actions):
        a=[Z]*6
        for j,c in actions.items():a[j]=c
        _,r,*_=api.step(env,[x.value for x in a])
        assert len({(w.x,w.y) for w in env.agents})==6
        return tuple(float(x) for x in r)

    blocker=env.shelfs[5]
    assert step({})==(0,0,0,0,0,.5)
    assert step({5:F})==(0,)*6
    assert (blocker.x,blocker.y)==BAY[blocked]
    assert step({5:T})==(0,0,0,0,0,.5)
    for a in (L,L,F):assert step({5:a})==(0,)*6
    assert env.agents[5].carrying_shelf is None
    for s,(x,y) in BAY.items():
        assert int(env.grid[1,y,x])==(blocker.id if s==blocked else 0)
    assert step({0:F})==(.5,0,0,0,0,0)
    assert local_designation(env) is None

    def old_plan(h,c):
        return (*shortest_turn(h,c),F,F,T,F)
    waiting=list(shortest_turn(E,heading))
    if mode=='wait':
        assert cut>=1 and len(waiting)<=cut
        queue=[Z]*(cut-len(waiting))+waiting
    elif mode=='fixed':
        assert fixed in BAYS and fixed!=blocked
        queue=list(old_plan(E,fixed))
    else:
        assert mode=='fallback' and cut in (1,2)
        queue=[]
        h0=E

    selected=fixed
    stamp=None
    qualified=None
    new_paid=False
    disjoint=None
    assert earlier_need is None or (earlier_need!=need and earlier_need!=blocked and marker_tick==2)
    assert marker_tick in (1,2)
    samples=[]
    for tick in range(1,DUE+3):
        act={}
        if queue:act[0]=queue.pop(0)
        if tick==marker_tick:
            act[ix[need]]=F # Genuine arrival, before any read that claims it.
        if tick==1:
            act[4]=F
            if earlier_need is not None:act[ix[earlier_need]]=F
        if tick in (DUE+1,DUE+2):act[ix[need]]=F
        r=step(act)
        if tick==1:
            if marker_tick==1:assert local_designation(env)==need
            elif earlier_need is not None:assert local_designation(env)==earlier_need
            else:assert local_designation(env) is None
            assert r[4]==.5
            disjoint=tick
        if tick in (1,2):
            samples.append(NAMES.get(local_designation(env)))
            if tick==2 and earlier_need is not None:
                assert local_designation(env) is None # two seen, neither alone establishes final designation
                for named in (need,earlier_need):
                    x,y=ENTRY[named]
                    assert env.grid[0,y,x]==env.agents[ix[named]].id
        if r[0]==.5:
            assert stamp is None
            stamp=tick
        if r[ix[need]]==.5:
            assert tick==DUE+2
            new_paid=True
        if mode=='wait' and tick==cut:
            observed=None if erase else local_designation(env)
            qualified=observed
            proposal=choose(blocked,observed)
            if proposal is not None and safe_pending(cut,heading,proposal,OLD_TICKS,DUE):
                selected=proposal
                queue=list(old_plan(heading,proposal))
        if mode=='fallback' and tick in (1,2) and selected is None:
            observed=None if erase or tick!=cut else local_designation(env)
            if observed is not None:qualified=observed
            if tick==2:
                assert env.agents[0].dir==HEAD[h0]
            task,value=upon(blocked,observed,tick,h0,OLD_TICKS,DUE)
            if task=='orient':
                p=shortest_turn(h0,value)
                assert len(p)<=1
                queue=list(p)
                h0=value
            elif task=='place':
                selected=value
                queue=list(old_plan(h0,value))
            else:
                raise AssertionError('fallback leaves old unserved')
    if stamp is not None:
        assert stamp<=DUE and selected!=blocked
        assert env.agents[0].carrying_shelf is None
        assert (env.shelfs[0].x,env.shelfs[0].y)==BAY[selected]
        assert (env.agents[0].x,env.agents[0].y)==OUT[selected]
    else:
        assert mode=='wait' and env.agents[0].carrying_shelf is env.shelfs[0]
        assert (env.agents[0].x,env.agents[0].y)==CENTER
    assert (blocker.x,blocker.y)==BAY[blocked]
    assert new_paid==(selected!=need)
    if mode=='wait':
        holds=not erase and cut+len(shortest_turn(heading,choose(blocked,need)))+3<=DUE
        assert (stamp is not None)==holds
        if holds:assert selected==choose(blocked,need)
    if mode=='fixed':assert stamp==len(shortest_turn(E,fixed))+3
    if mode=='fallback':assert stamp is not None
    assert disjoint==1
    signature=(stamp,new_paid,disjoint,NAMES.get(qualified),NAMES.get(selected))
    return signature if marker_tick==1 else (signature,samples)


def optimal_tree(b):
    """Exact contingent comparison when early/late/erased schedules are admitted."""
    valid=set(BAYS)-{b}
    command=lambda h,t: tuple(c for c in valid if t+len(shortest_turn(h,c))+3<=DUE)
    vectors=[]
    for h1 in (E,N,S):
        earliest=command(h1,1)
        for h2 in {h1,(h1+1)%4,(h1-1)%4}:
            latest=command(h2,2)
            if not earliest or not latest:continue
            early=sum(any(c!=needed for c in earliest) for needed in valid)
            late=sum(any(c!=needed for c in latest) for needed in valid)
            erased=max(sum(c!=needed for needed in valid) for c in latest)
            vectors.append((early,late,erased,h1,h2))
    best=max(x[:3] for x in vectors)
    assert best==(2,1,1)
    # With east physically closed, an early turn to stage fallback at north
    # or south forfeits one early designation. Waiting to choose heading does not.
    if b==E:
        assert all(h1==E for *val,h1,h2 in vectors if tuple(val)==best)
    return best


def campaign():
    fixed=[]; waited=[]; missed=[]
    boundaries={}
    fallback_rows=[]
    compared_trees={}
    physical_delay=[]
    real_reassign=[]
    direct_checks=0
    for b in BAYS:
        valid=tuple(s for s in BAYS if s!=b)
        assert best_delay(b,E,2,DUE)==1
        for need,site in product(valid,repeat=2):
            fixed.append((NAMES[b],NAMES[need],NAMES[site],run(b,need,'fixed',fixed=site)))
        for cut in range(1,4):
            ref=exhaustive(DUE,OLD_TICKS,cut,b)
            max_count=max(map(len,ref.values()))
            assert max_count=={1:2,2:1,3:0}[cut]
            boundaries[f'{NAMES[b]}:{cut}']=max_count
            for h,need in product(sorted(ref),valid):
                out=run(b,need,'wait',cut,h)
                assert bool(out[0] and out[1])==(need in ref[h])
                waited.append((NAMES[b],NAMES[need],cut,NAMES[h],out))
        for need in valid:
            missed.append((NAMES[b],NAMES[need],run(b,need,'wait',1,erase=True)))
        local=[]
        for status in ('early','late','erased'):
            raw=[run(b,need,'fallback',1 if status=='early' else 2,
                     erase=(status=='erased')) for need in valid]
            local.append(sum(bool(r[0] and r[1]) for r in raw))
            assert all(r[0] is not None and r[2]==1 for r in raw)
            fallback_rows.extend((NAMES[b],status,NAMES[need],r)
                                 for need,r in zip(valid,raw,strict=True))
        assert tuple(local)==optimal_tree(b)
        compared_trees[NAMES[b]]=local
        for need in valid:
            physical=run(b,need,'fallback',2,marker_tick=2)
            merely_report=run(b,need,'fallback',2)
            assert physical==(merely_report,[None,NAMES[need]])
            physical_delay.append((NAMES[b],NAMES[need],physical))
            p=choose(b,need)
            switched=run(b,need,'fallback',1,marker_tick=2,earlier_need=p)
            assert switched[0][0] is not None and switched[0][2]==1
            assert not switched[0][1] and switched[0][3]==NAMES[p]
            assert switched[0][4]==NAMES[need] and switched[1]==[NAMES[p],None]
            real_reassign.append((NAMES[b],NAMES[p],NAMES[need],switched))

    # Extra analytic checks across partial prefixes and actuator windows.
    for deadline,steps,cut,b in product(range(1,14),range(1,7),range(7),BAYS):
        ref=exhaustive(deadline,steps,cut,b)
        for h,viable in ref.items():
            assert (len(viable)==2)==(cut<=best_delay(b,h,steps,deadline))
            direct_checks+=1
    assert len(fixed)==12 and len(waited)==66 and len(missed)==6 and len(fallback_rows)==18
    print(json.dumps(dict(native_fixed=fixed,native_waited=waited,native_erased=missed,
                          best_on_time_branches_of_two=boundaries,bounded_direct_checks=direct_checks,
                          native_deadline_fallback=fallback_rows,matched_optimal_tree=compared_trees,
                          source_delayed_motion=physical_delay, source_reassigned=real_reassign),
                     sort_keys=True,indent=2))

if __name__=='__main__':
    campaign()

"""Replay #753 source-bound probe with actual canceled versus effective reserve motion."""
from copy import deepcopy
from itertools import product
from collections import deque
import json
from observation_cut import loc
from same_queue import start,native,A,D,freeze

def xyz(a):
    return int(a.x),int(a.y),a.dir.name

def can_finish(start,goal,blockers,horizon):
    """Independent static, empty-handed, single-mover reachability frontier."""
    x,y,h=start
    offsets={'UP':(0,-1),'DOWN':(0,1),'LEFT':(-1,0),'RIGHT':(1,0)}
    cycle=('UP','RIGHT','DOWN','LEFT')
    q=deque([(x,y,h,())]);seen={(x,y,h)}
    while q:
        x,y,h,p=q.popleft()
        if (x,y)==goal:return p
        if len(p)>=horizon:continue
        dx,dy=offsets[h]
        col,row=(min(max(x+dx,0),6),min(max(y+dy,0),6))
        nxt=[('LEFT',x,y,cycle[(cycle.index(h)-1)%4]),
             ('RIGHT',x,y,cycle[(cycle.index(h)+1)%4])]
        if (col,row) not in blockers:nxt.append(('FORWARD',col,row,h))
        for a,x1,y1,h1 in nxt:
            if (x1,y1,h1) not in seen:q.append((x1,y1,h1,p+(a,)));seen.add((x1,y1,h1))

def frozen_receiver(source,flag,scope,observed_heading,horizon,goal):
    """Consumes an admitted source record and a separately qualified body cut."""
    if source[:3]!=('dispatch',1,3) or source[3] not in (1,2):return None
    probe,actor,expected_epoch,cut,dx,dy,heading,blockers=scope
    if (probe,actor,expected_epoch,cut)!=(1,4,1,21) or heading!=observed_heading:return None
    origin_x=2 if flag==(source[3]==1) else 4
    x,y=6-origin_x+dx,3+dy
    return can_finish((x,y,observed_heading),goal,blockers,horizon)

def replay(seed,origin,blocked):
    w=start(origin,seed)
    w.max_steps=50
    reserve=native.Agent(6-origin,3,D.DOWN,0)
    obstacle=native.Agent(6-origin,4 if blocked else 5,D.DOWN,0)
    w.agents.extend((reserve,obstacle)); w.n_agents+=2;w._recalc_grid()
    records=[]
    def step(a=A.NOOP,b=A.NOOP,c=A.NOOP,d=A.NOOP,e=A.NOOP):
        pre=tuple(xyz(z) for z in w.agents)
        requested=(a,b,c,d,e)
        obs,r,term,trunc,info=native.step(w,requested)
        assert not term and not trunc and not info
        post=tuple(xyz(z) for z in w.agents)
        records.append((w._cur_steps,tuple(i.name for i in requested),
                         tuple(z.req_action.name for z in w.agents),pre,post))
        return [freeze(o) for o in obs],r
    _,r=step(b=A.FORWARD)
    assert r==[0,.5,0,0,0]
    assigned=w.request_queue[0].id
    receipt=('dispatch',1,3,assigned)
    assert assigned==(1 if seed==14 else 2)
    obs,_=step(a=A.FORWARD)
    flag=any(o['shelf_requested'][0] for o in obs[0]['sensors'])
    for a in (A.LEFT,A.LEFT,A.FORWARD):step(a=a)
    l,r=(A.LEFT,A.RIGHT) if assigned==1 else (A.RIGHT,A.LEFT)
    for a in (r,A.FORWARD,l,A.FORWARD,A.TOGGLE_LOAD,A.LEFT,A.LEFT,A.FORWARD,r,A.FORWARD):
        obs,reward=step(c=a)
    assert reward==[0,0,.5,0,0] and tuple(o.id for o in w.request_queue)==(4,)
    # The old freight body actually leaves the local area, same across arms.
    for b in (A.LEFT,A.LEFT,A.FORWARD):step(b=b)
    # Read of reserve stopped across all three actions. Same requests in
    # both fault worlds; the simulator settles the first motion differently.
    assert w._cur_steps==18
    before=records[-1][0]
    step(d=A.FORWARD)
    _,rr=step(e=A.FORWARD); obs,_=step(e=A.FORWARD)
    assert not any(rr)
    old=w.agents[0]
    hd=D(obs[3]['self']['direction']).name
    assert hd=='DOWN' and loc(obs[3],'dict-normalized')==[0,0]
    # Authored authority, distinct from native effects. Only agent 4 may act in
    # final horizon and all others are frozen, leaving the center unoccupied.
    q=records[before:]
    assert tuple(z[0] for z in q)==(19,20,21)
    assert all(z[1][3]=='NOOP' for z in q[1:])
    assert q[0][2][3]==('NOOP' if blocked else 'FORWARD')
    assert (q[0][3][3]==q[0][4][3]) if blocked else (q[0][4][3][1]==4)
    # Replay of a settled effect from a commissioned mirror placement.
    # Accepted native action != requested action; no current absolute
    # position of reserve is exported to the frozen receiver.
    # The certificate uses the realized source delta, not a rule that
    # every accepted FORWARD in every possible layout moves one cell.
    dh=tuple(v-u for u,v in zip(q[0][3][3][:2],q[-1][4][3][:2]))
    assert dh==(0,0 if blocked else 1)
    blockers=frozenset((z.x,z.y) for z in w.agents if z.id!=4)
    full_state=xyz(reserve)
    assert full_state==(6-origin,3+dh[1],hd)
    # Native absolute-output control: no changed physical state or history,
    # and enough information to bypass the historical body-pose transport.
    w.normalised_coordinates=False
    absolute_native=freeze(w._make_obs(reserve))
    w.normalised_coordinates=True
    abs_pose=(*loc(absolute_native,'dict-absolute'),D(absolute_native['self']['direction']).name)
    assert abs_pose==full_state
    # Native exhaustive control: each candidate starts with exact same
    # frozen real plant state. None of these trials is a receiver input.
    def native_end(suffix):
        w2=deepcopy(w)
        w2._recalc_grid=lambda:native._recalc_grid(w2)
        w2._is_highway=lambda x,y:native._is_highway(w2,x,y)
        w2._get_default_obs=lambda a:w._get_default_obs(a)
        w2._make_obs=lambda a:None
        for x in suffix:native.step(w2,(A.NOOP,A.NOOP,A.NOOP,A[x],A.NOOP))
        return xyz(w2.agents[3])[:2]
    layers={}
    for n in range(1,5):
        layers[n]={}
        for suffix in product(('NOOP','LEFT','RIGHT','FORWARD'),repeat=n):
            end=native_end(suffix)
            layers[n].setdefault(end,[]).append(suffix)
    modes=[('settled',old.id,reserve.id,1,21,*dh),
           ('pretend_fresh',old.id,reserve.id,1,21,0,0),
           ('actual_old_cut',old.id,reserve.id,1,18,0,0),
           ('wrong_actor',old.id,old.id,1,21,*dh),
           ('wrong_appointment',old.id,reserve.id,2,21,*dh),
           ('requested',old.id,reserve.id,1,21,0,1)]
    results={}
    for goal in ((3,3),(3,4)):
        ys=goal[1]
        possible=(ys==3)==blocked
        direct=can_finish(abs_pose,goal,blockers,2)
        exact=layers[2].get(goal,[])
        assert bool(exact)==possible and len(exact)==int(possible)
        assert direct==(exact[0] if exact else None)
        earliest=min(n for n,l in layers.items() if goal in l)
        assert earliest==(2 if possible else 4 if ys==3 else 3)
        ans={}
        for name,*entry in modes:
            scope=(*entry,hd,blockers)
            plan=frozen_receiver(receipt,flag,scope,hd,2,goal)
            ans[name]=[plan,None if plan is None else native_end(plan)==goal]
        assert ans['settled']==[direct,(True if possible else None)]
        for k in ('actual_old_cut','wrong_actor','wrong_appointment'):
            assert ans[k]==[None,None]
        assert ans['pretend_fresh'][1]==(blocked if ys==3 else None)
        assert ans['requested'][1]==(not blocked if ys==4 else None)
        results[str(ys)]={'decisions':ans,'earliest':earliest,'direct':direct}
    return {'receipt':receipt,'flag':flag,'at_cut':obs[3],
            'requested':tuple(z[1] for z in q),'reservation':4,
            'settled_delta':dh,'first_post':q[0][4][3],
            'nonactor_cells':sorted(blockers),'heading':hd,
            'actuated_or_cancelled':q[0][2][3],'results':results,
            'unrelated_native_reward':reward}


def main():
    rows=[]
    for seed,origin in product((14,9),(2,4)):
        a,b=[replay(seed,origin,k) for k in (False,True)]
        for key in ('receipt','flag','at_cut','requested','reservation','unrelated_native_reward'):
            assert a[key]==b[key],key
        a.pop('at_cut');b.pop('at_cut')
        rows.append({'seed':seed,'origin_x':origin,'blocked':b,'free':a})
    print(json.dumps({'paired_worlds':len(rows),'exact_suffix_replays':2*len(rows)*sum(4**n for n in range(1,5)),'rows':rows},sort_keys=True,separators=(',',':')))
if __name__=='__main__':main()

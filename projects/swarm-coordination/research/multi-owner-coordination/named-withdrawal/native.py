"""Exact selected native fixture: typed local conditional warehouse withdrawal."""
from hashlib import sha1
from itertools import product
from pathlib import Path
import json
import sys
import numpy as np
from release import lawful

up=Path(sys.argv[1]).resolve()
for f,sha in [('native_source.py','9797bf36970d5eb14fef7a150fab7562c450dff6'),
              ('rware_rotation.py','9803d1607cccf88a4a58e58f18528232790056be'),
              ('isolated.py','610a81b316a9b3538106387467c4e2f4437b28f4')]:
    b=(up/f).read_bytes()
    assert sha1(f"blob {len(b)}\0".encode()+b).hexdigest()==sha
sys.path.insert(0,str(up))
import rware_rotation as rw
n=rw.engine(up/'native_source.py')
D,A=n.Direction,n.Action
E,S,W,N=D.RIGHT,D.DOWN,D.LEFT,D.UP
HEAD=(E,S,W,N)
F,T,L,R,Z=A.FORWARD,A.TOGGLE_LOAD,A.LEFT,A.RIGHT,A.NOOP
DIR={(1,0):E,(0,1):S,(-1,0):W,(0,-1):N}
YROW=(2,4)
BAY=((3,2),(3,4))

def run(permutation,required,policy,grant=(True,True),read=(True,True)):
    # Two old shippers, two on-cell guards, two path-ready loaded successors,
    # and one independent operator. Arrays not delivered to the remote issuer.
    pos=((1,1),(5,5),(3,1),(3,5),(5,2),(5,4),(0,6))
    ds=(E,W,S,N,W,W,E)
    n.Agent.counter=n.Shelf.counter=0
    agents=[n.Agent(*p,h,0) for p,h in zip(pos,ds,strict=True)]
    load=[0,1,4,5,6]
    dummies=((0,0),(6,0),(6,6),(0,5),(6,5))
    shelves=[n.Shelf(*p) for p in (*(pos[j] for j in load),*dummies)]
    for j,c in zip(load,shelves):agents[j].carrying_shelf=c
    env=rw.iso.NS(grid_size=(7,7),msg_bits=0,n_agents=7,agents=agents,
                  grid=np.zeros((2,7,7),dtype=int),highways=np.zeros((7,7),dtype=bool),
                  shelf_count=len(shelves),shelfs=shelves,request_queue=shelves[:5],
                  reward_type=n.RewardType.TWO_STAGE,_cur_steps=0,
                  _cur_inactive_steps=0,max_steps=200,max_inactivity_steps=None,
                  _make_obs=lambda a:None,_get_info=lambda:{})
    env.goals=[(2,1),(4,5),(2,2),(2,4),(1,6)]
    for x,y in env.goals:env.highways[y,x]=True
    env.np_random=rw.iso.NS(choice=lambda opts:min((s for s in opts if s.id>=6),key=lambda s:s.id))
    env._recalc_grid=lambda:n._recalc_grid(env)
    env._is_highway=lambda x,y:n._is_highway(env,x,y)
    env._recalc_grid()

    def step(cmd):
        choices=[cmd.get(i,Z).value for i in range(7)]
        _,r,*_=n.step(env,choices)
        assert len({(a.x,a.y) for a in agents})==len(agents)
        return tuple(float(x) for x in r)
    def at(i):
        return (agents[i].x,agents[i].y)
    def rot(i,d):
        current=HEAD.index(agents[i].dir)
        target=HEAD.index(d)
        right=(target-current)%4
        actions=[R]*right if right<=2 else [L]*(4-right)
        for x in actions:
            assert step({i:x})==(0,)*7
        assert agents[i].dir==d
    def move(i,path):
        for next_p in path:
            x,y=at(i); a,b=next_p
            rot(i,DIR[a-x,b-y])
            assert step({i:F})==(0,)*7
            assert at(i)==next_p
    def via_y(x,y,z):
        sign=1 if z>y else -1
        return [(x,v) for v in range(y+sign,z+sign,sign)]
    def pad(t):
        assert env._cur_steps<=t
        while env._cur_steps<t:
            assert step({})==(0,)*7
    assert step({0:F,1:F})==(.5,.5,0,0,0,0,0)
    yx=YROW[permutation]
    yy=YROW[1-permutation]
    move(0,via_y(2,1,yx)+[(3,yx)])
    pad(10)
    rr=step({0:T})
    x_return=env._cur_steps
    assert rr==(.5,0,0,0,0,0,0)
    move(0,[(x,yx) for x in (2,1,0)]+via_y(0,yx,3))
    rot(0,E)
    pad(25)
    move(1,via_y(4,5,yy)+[(3,yy)])
    pad(35)
    rs=step({1:T})
    y_return=env._cur_steps
    assert rs==(0,.5,0,0,0,0,0)
    move(1,[(3,3)])
    rot(1,E)
    assert (at(0),at(1))==((0,3),(3,3))
    assert all(not a.has_delivered and a.carrying_shelf is None for a in agents[:2])
    pad(45)
    assert step({2:F,3:F})==(0,)*7
    assert (at(2),at(3))==BAY
    coarse={
        'agents':[(a.x,a.y,str(a.dir)) for a in agents],
        'occupied':sorted((int(x),int(y)) for y,x in np.argwhere(env.grid[1]>0)),
        'paid_old_delivery_and_unload':(.5,.5,rr,rs),
        'old_carrying':(False,False),
        'qualified_cut_tick':env._cur_steps,
        'old_unload_ticks':(x_return,y_return),
    }
    bay_cargo=[int(env.grid[1,y,x]) for x,y in BAY]
    assert bay_cargo[permutation]==shelves[0].id and bay_cargo[1-permutation]==shelves[1].id

    permit={shelves[0].id}
    # On-cell local read, no other bay's identity used by either guard.
    # Public input is conditional permission, not the hidden permutation.
    elected=[]
    direct=[]
    for j,(x,y) in enumerate(BAY):
        possible=(int(env.grid[1,y,x]),) if read[j] else tuple(s.id for s in shelves[:2])
        enabled=lawful(grant[j],possible,permit)
        reference=grant[j] and read[j] and int(env.grid[1,y,x])==shelves[0].id
        assert enabled==reference
        if reference:direct.append(j)
        if policy=='local' and enabled:elected.append(j)
        if policy==f'fixed-{j}' and enabled:elected.append(j)
    if policy=='local':assert elected==direct
    assert len(elected)<=1 and all(bay_cargo[i] in permit for i in elected)
    r=step({6:F,**{i+2:T for i in elected}})
    assert r==(0,0,0,0,0,0,.5)
    for j in range(2):
        assert (agents[j+2].carrying_shelf is shelves[0])==(j in elected)
    protected=(shelves[1].x,shelves[1].y)
    assert protected==BAY[1-permutation]
    # Both guards retreat, even if only one acquired the authority and cargo.
    # This charges the same geometry/ticks in all controls.
    assert step({2:L,3:L})==(0,)*7
    assert step({2:L,3:L})==(0,)*7
    assert step({2:F,3:F})==(0,)*7
    # Authorized physical relocation to the off-route safe storage footprint.
    if elected:
        j=elected[0]; assert at(j+2)==(3,1 if j==0 else 5)
        assert step({j+2:T})==(0,)*7
        assert agents[j+2].carrying_shelf is None
        assert (shelves[0].x,shelves[0].y)==at(j+2)
    else:assert step({})==(0,)*7
    assert not any(env.grid[0,y,x] for x,y in BAY)
    assert (shelves[1].x,shelves[1].y)==protected
    assert all(a.carrying_shelf is not shelves[1] for a in agents)
    k=required+4
    r1=step({k:F}); r2=step({k:F}); r3=step({k:F})
    assert at(k)==((2,YROW[required]) if required in elected else (4,YROW[required]))
    assert r1==(0,)*7 and r2==(0,)*7
    paid=(r3[k]==.5)
    assert paid==(required in elected)
    return coarse,dict(policy=policy,permutation=permutation,required=required,grant=grant,
                    local_read=read,pickup=elected,pay_later=paid,independent_paid=True,
                    stored_footprint=[(s.x,s.y) for s in shelves[:2]])

def campaign():
    rows=[];coarse=None
    courses=(
        ('local',(True,True),(True,True)),
        ('local',(True,True),(False,False)),
        ('local',(False,False),(True,True)),
        ('local',(True,False),(True,True)),
        ('local',(True,True),(True,False)),
        ('fixed-0',(True,True),(True,True)),
        ('fixed-1',(True,True),(True,True)),
    )
    for orient,demand,(policy,grant,read) in product(range(2),range(2),courses):
        a,record=run(orient,demand,policy,grant,read)
        if coarse is None:coarse=a
        assert a==coarse
        if policy=='local' and all(grant) and all(read):
            assert record['pickup']==[orient]
            assert record['pay_later']==(orient==demand)
        if not any(grant) or not any(read):assert not record['pickup'] and not record['pay_later']
        rows.append(record)
    print(json.dumps(dict(cases=rows,shared_remote_snapshot=coarse),sort_keys=True,indent=2))

if __name__=='__main__':campaign()

"""Pinned native warehouse: actual unloading, actual subsequent delivery."""
from hashlib import sha1
from itertools import product
from pathlib import Path
import json
import sys
from footprint import Footprint,available

up=Path(sys.argv[1]).resolve()
for n,sha in [('native_source.py','9797bf36970d5eb14fef7a150fab7562c450dff6'),
              ('rware_rotation.py','9803d1607cccf88a4a58e58f18528232790056be'),
              ('isolated.py','610a81b316a9b3538106387467c4e2f4437b28f4')]:
    b=(up/n).read_bytes()
    assert sha1(f"blob {len(b)}\0".encode()+b).hexdigest()==sha
sys.path.insert(0,str(up))
import rware_rotation as rw
api=rw.engine(up/"native_source.py")
D,A=api.Direction,api.Action

def execute(bay,request):
    pos=((1,2),(1,1),(1,3),(3,4))
    cast=tuple(enumerate(pos))+((None,(0,0)),(None,(0,4)),(None,(4,0)))
    env=rw.plant(api,pos,(D.RIGHT,)*4,cast,request=(0,1,2,3))
    env.goals=[(2,2),(3,1),(3,3),(4,4)]
    for x,y in env.goals:
        env.highways[y,x]=True
    env.np_random=rw.iso.NS(choice=lambda options:min((s for s in options if s.id>=5),key=lambda s:s.id))
    old,top,lower,other=env.agents
    cargo=env.shelfs[0]

    def step(*a):
        _,r,*_=api.step(env,[x.value for x in a])
        assert len({(v.x,v.y) for v in env.agents})==4
        return [float(x) for x in r]
    N,F=A.NOOP,A.FORWARD
    receipt=step(F,N,N,N)
    assert receipt==[.5,0,0,0] and old.has_delivered
    assert step(A.LEFT if bay==1 else A.RIGHT,N,N,N)==[0]*4
    assert step(F,N,N,N)==[0]*4
    assert (old.x,old.y)==(2,bay)
    retire=step(A.TOGGLE_LOAD,N,N,N)
    assert retire==[.5,0,0,0]
    assert step(F,N,N,N)==[0]*4
    assert old.carrying_shelf is None and not old.has_delivered
    assert not env.grid[0,bay,2] and env.grid[1,bay,2]==cargo.id
    datum=Footprint("old",None,True,(cargo.x,cargo.y))
    same=(datum.settled,old.has_delivered,old.carrying_shelf is None,tuple(receipt),tuple(retire))
    ctl=top if request==1 else lower
    arm=(F,N) if request==1 else (N,F)
    first=step(N,*arm,F)
    cross=(ctl.x,ctl.y)==(2,request)
    assert first==[0,0,0,.5]
    second=step(N,*arm,N)
    paid=second[1 if request==1 else 2]==.5
    assert paid==cross==available(datum,(2,request))==(bay!=request)
    assert cross==bool((ctl.x,ctl.y)==(3,request))
    return dict(return_bay=bay,requested_lane=request,proxy=same,native_cross=cross,
                next_due_paid=paid,independent_paid=first[3]==.5,physical_storage=datum.storage)

if __name__=='__main__':
    rows=[execute(b,r) for b,r in product((1,3),repeat=2)]
    assert all(x['proxy']==rows[0]['proxy'] for x in rows)
    assert sum(x['next_due_paid'] for x in rows)==2
    print(json.dumps(rows,sort_keys=True,indent=2))

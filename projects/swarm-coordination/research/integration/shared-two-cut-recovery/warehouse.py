"""Adapter retains native moves, cargo identity, and actual reward."""
from pathlib import Path
import rware_rotation as rw
from itertools import product
import sys

def execute(n,h,early,late,stale_queue=False):
    # Early and late primary cars approach the same berth on orthogonal edges.
    # B carries an interchangeable, separately requested part, not a copy of
    # a unique physical shelf. Last-cut clearance is not an available action.
    P=((1,1),(2,0),(4,0),(3,3))
    D=n.Direction
    w=rw.plant(n,P,(D.RIGHT,D.DOWN,D.DOWN,D.LEFT),
        [(i,p) for i,p in enumerate(P)],request=(0,1,2))
    w.np_random=rw.iso.NS(choice=lambda C:min(C,key=lambda shelf:shelf.id))
    old=w.agents[3]
    old.has_delivered=True
    A,B=(2,1),(4,1)
    def run(at,goal):
        w.goals=goal
        for x,y in goal:w.highways[y,x]=True
        cmd=[0]*4
        if at is not None:cmd[at]=1
        out=n.step(w,cmd)
        assert len({(a.x,a.y) for a in w.agents})==4
        assert old.has_delivered and old.carrying_shelf is w.shelfs[3]
        return sum(out[1])==.5
    copy=False
    # In F the alternate really retrieves its own shelf rather than reading a
    # declaration that it is ready. Make pickup established by a native toggle.
    if h=='F':
        w.agents[2].carrying_shelf=None
        w._recalc_grid()
        cmd=[0,0,n.Action.TOGGLE_LOAD.value,0]
        assert sum(n.step(w,cmd)[1])==0
        copy=w.agents[2].carrying_shelf is w.shelfs[2]
        assert copy
    else:
        # No alternate authority when it cannot act on an authenticated grant.
        # It holds a staged shelf but is not licensed to fulfill this task.
        assert w.agents[2].carrying_shelf
    early_done=run(0 if early=='p' else None,[A] if h=='G' else [])
    effect=(w.agents[0].x,w.agents[0].y)==A
    assert effect==(early=='p')
    a_auth=h!='G'
    b_auth=copy
    allowed=(['a'] if a_auth else [])+(['b'] if b_auth else [])
    if callable(late):
        late=late(early_done)
    who={'a':1,'b':2}.get(late) if late in allowed else None
    if not early_done and not stale_queue:
        # The second authorization accepts the two late carriers, not the
        # old berth reservation / early lot. Native scoring uses this queue.
        w.request_queue=[*w.shelfs[1:3]]
    final_done=early_done or run(who,([A] if a_auth else [])+([B] if b_auth else []))
    if final_done and not early_done and not stale_queue:
        assert who is not None and w.agents[who].has_delivered
        assert w.agents[who].carrying_shelf is w.shelfs[who]
    return early_done,final_done,effect,copy

def main():
    n=rw.engine(Path(__file__).with_name('native_source.py'))
    # Diagnostic control: changing just the goal while retaining the old
    # request counts the stationary early lot; not a new carrier arrival.
    assert execute(n,'F','p','a',stale_queue=True)==(False,True,True,True)
    if len(sys.argv)==3:
        early,after_miss=sys.argv[1:]
        for h in 'GF':
            chosen=[]
            def controller(early_done):
                chosen.append('s' if early_done else after_miss)
                return chosen[0]
            a,b,c,d=execute(n,h,early,controller)
            print(h+early+chosen[0],int(a),int(b),int(c),int(d))
        return
    for h,e,l in product('GFZ','wp','sab'):
        a,b,c,d=execute(n,h,e,l)
        print(h+e+l,int(a),int(b),int(c),int(d))
if __name__=='__main__':
    main()

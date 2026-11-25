"""Preregistered guard versus native state search, on exact extracted effects."""
import copy, hashlib, json, sys
from pathlib import Path
from collections import deque
if (Path(__file__).with_name("isolated.py")).exists():
    import isolated as iso
else:
    sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"rware-source-and-return"))
    import replay as iso

GOAL=(4,1)
NEW=(1,1)
OLDPARK=(4,0)

def world(n):
    w=iso.make(n,False)
    a,b=w.agents
    a.x,a.y,a.dir=4,2,n.Direction.UP
    b.x,b.y,b.dir=*NEW,n.Direction.RIGHT
    a.carrying_shelf=w.shelfs[0];w.shelfs[0].x,w.shelfs[0].y=4,2
    w.shelfs[1].x,w.shelfs[1].y=NEW
    w._recalc_grid()
    pre=act(n,w,n.Action.FORWARD,n.Action.NOOP)
    assert pre==[.5,0.] and at(a)==GOAL
    assert w.request_queue[0] is w.shelfs[1] and a.has_delivered
    return w

def at(a): return a.x,a.y
def act(n,w,a,b):
    assert a==n.Action.NOOP or b==n.Action.NOOP
    return n.step(w,[a.value,b.value])[1]
def clone(n,w):
    v=copy.deepcopy(w)
    v._recalc_grid=lambda:n._recalc_grid(v)
    v._is_highway=lambda x,y:n._is_highway(v,x,y)
    return v
def old_program(n,reentry,exit,drop):
    A=n.Action
    p={1:A.FORWARD,drop:A.TOGGLE_LOAD}
    if reentry:
        p.update({2:A.RIGHT,3:A.RIGHT,reentry:A.FORWARD,exit:A.FORWARD})
    return p

def trace_old(n,p,h):
    w=world(n); a=w.agents[0]; port={}; credits={}
    for t in range(1,h+1):
        port[t]=at(a)
        rewards=act(n,w,p.get(t,n.Action.NOOP),n.Action.NOOP)
        credits[t]=rewards[0]
    return port,credits

def plan(n,w,old,h,pause=False):
    # Static old trajectory is justified only via the declared effect-side
    # schedule. This controller cannot run old and new actions in one slot.
    A=n.Action; a,b=w.agents
    pos,credit=trace_old(n,old,h)
    S={(b.x,b.y,b.dir,False):()}
    for t in range(1,h+1):
        out={}
        dropped=any(credit[j]==.5 for j in range(1,t))
        for (x,y,d,hold),past in S.items():
            ops=(A.NOOP,A.FORWARD,A.LEFT,A.RIGHT,A.TOGGLE_LOAD)
            if t in old or (pause and not dropped): ops=(A.NOOP,)
            for o in ops:
                v=iso.NS(x=x,y=y,dir=d,req_action=o)
                u,z=n.Agent.req_location(v,w.grid_size) if o==A.FORWARD else (x,y)
                q=n.Agent.req_direction(v) if o in (A.RIGHT,A.LEFT) else d
                carries=hold
                if o==A.FORWARD and (u,z)==pos[t]: continue
                if o==A.TOGGLE_LOAD:
                    if hold or (x,y)!=NEW:continue
                    carries=True
                if t in old and pos.get(t+1,pos[t])==(u,z):continue
                if carries and (u,z)==GOAL:
                    return t,past+(o,)
                out.setdefault((u,z,q,carries),past+(o,))
        S=out
    return None,()

def blunt(n,p,h):
    w=world(n)
    op=n.Action
    # At the cut after tick 1 the port is empty and the new shelf is
    # requested. A fixed path based on that occupancy ignores reentry,
    # even when it honours the old actor's movement slot reservations.
    # Submit a fixed short trace that moves as quickly as the authorised old
    # time ledger permits; no new action in an already reserved old slot.
    route=[op.TOGGLE_LOAD,op.FORWARD,op.FORWARD,op.FORWARD]
    timeline=[];first=None
    for t in range(1,h+1):
        a=p.get(t,op.NOOP)
        o=op.NOOP if t in p or not route else route.pop(0)
        rwd=act(n,w,a,o)
        timeline.append((t,[a.name,o.name],at(w.agents[0]),at(w.agents[1]),rwd))
        if rwd[1]==.5:
            first=t;break
    return first,timeline

def run(n,old,seq):
    w=world(n); trace=[]
    for t in range(1,len(seq)+1):
        o=old.get(t,n.Action.NOOP)
        v=seq[t-1]
        rw=act(n,w,o,v)
        a,b=w.agents
        tr=(t,o.name,v.name,at(a),at(b),bool(a.carrying_shelf),bool(b.carrying_shelf),
            a.has_delivered,b.has_delivered,rw,w.request_queue[0].id)
        trace.append(tr)
    return trace

def finish_both(n,p,seq,park):
    w=world(n); A=n.Action
    acc=[0.,0.]
    for t in range(1,25):
        a=p.get(t,A.NOOP); b=A.NOOP
        if t<=len(seq):b=seq[t-1]
        elif t not in p and w.agents[1].carrying_shelf:
            if at(w.agents[1])==park: b=A.TOGGLE_LOAD
            else:
                r=iso.route(n,w,1,park,set())
                assert r
                b=r[0]
        got=act(n,w,a,b)
        acc=[x+y for x,y in zip(acc,got)]
        if acc==[.5,1.]:
            assert all(not z.carrying_shelf for z in w.agents)
            assert [at(z) for z in w.shelfs]==[at(w.agents[0]),park]
            return t
    raise AssertionError(acc)

def direct(n,old,h,pause=False):
    # Clone and execute the actual plant for every distinct reached state
    # used by the same-information reference. Cut by first native new credit.
    w=world(n); A=n.Action
    W={():w}; probes=0
    for t in range(1,h+1):
        V={}
        for live in W.values():
            a=old.get(t,A.NOOP)
            ops=(A.NOOP,) if t in old or (pause and live.agents[0].carrying_shelf) else tuple(A)
            for b in ops:
                if b==A.TOGGLE_LOAD and (live.agents[1].carrying_shelf or at(live.agents[1])!=NEW):
                    continue
                q=clone(n,live); old_a=q.agents[0]
                rewards=act(n,q,a,b);probes+=1
                if a==A.FORWARD and old_a.req_action==A.NOOP: continue
                if rewards[1]==.5: return t,probes
                z=q.agents[1]
                aa=q.agents[0]; key=(*at(aa),aa.dir,bool(aa.carrying_shelf),*at(z),z.dir,bool(z.carrying_shelf))
                V.setdefault(key,q)
        W=V
    return None,probes

def local_feedback(n,old,h,pause=False):
    # The arbiter exposes only the present grant. This controller does not
    # read a forecast, inspect the old route, or see a future reservation.
    w=world(n); A=n.Action
    for t in range(1,h+1):
        a=w.agents[0]; b=w.agents[1]
        grant=t not in old
        port_free=at(a)!=GOAL
        op=A.NOOP
        if grant and (not pause or not a.carrying_shelf):
            if not b.carrying_shelf:
                assert at(b)==NEW
                op=A.TOGGLE_LOAD
            elif at(b)!=(3,1) or port_free:
                op=A.FORWARD
        r=act(n,w,old.get(t,A.NOOP),op)
        if r[1]==.5:return t
    return None

def exact_cut(n,p,h,pause):
    P,R=trace_old(n,p,h)
    have=0
    for t in range(1,h+1):
        if t in p or (pause and not any(R[j]==.5 for j in range(1,t))):
            continue
        if have<3: have+=1
        elif P[t]!=GOAL: return t
    return None

def main(src):
    n=iso.load_native(src)
    cases=[]; total=0
    for reentry,exit,drop in [(None,None,k) for k in range(6,13)]+[
        (r,k,s) for r in (4,5,6) for k in (r+1,r+3,r+4) for s in (k+1,k+3)]:
        p=old_program(n,reentry,exit,drop)
        for pause in (False,True):
            f,seq=plan(n,world(n),p,20,pause)
            q,c=direct(n,p,20,pause)
            assert q==f==exact_cut(n,p,20,pause)==local_feedback(n,p,20,pause),(reentry,exit,drop,pause,f,q)
            tr=run(n,p,seq); total+=c
            assert f is None or tr[-1][-2][1]==.5
            cases.append(dict(reentry=reentry,exit=exit,drop=drop,pause=pause,
                              time=f,probes=c,trace=tr))
    examples=[r for r in cases if r['drop']==12 and (r['reentry'] is None or
                                                     (r['reentry'],r['exit'])==(5,9))]
    old=old_program(n,5,9,12)
    failed,bad=blunt(n,old,12)
    assert failed is None
    clear=old_program(n,None,None,12)
    a=run(n,clear,(n.Action.NOOP,)); b=run(n,old,(n.Action.NOOP,)); assert a==b
    full={}
    for name,p,park in [('clear',clear,(4,2)),('reentry',old,(4,0))]:
        full[name]={}
        for pause in (False,True):
            due,path=plan(n,world(n),p,20,pause)
            full[name]['pause' if pause else 'scoped']=[due,finish_both(n,p,path,park)]
    assert full=={'clear':{'scoped':[5,12],'pause':[16,19]},
                  'reentry':{'scoped':[10,14],'pause':[16,19]}},full
    return dict(full_return=full,cases=cases,native_search_probes=total,equal_projection=a,examples=examples,blunt_trace=bad)

if __name__=='__main__':
    d=main(Path(sys.argv[1])/'native_source.py')
    raw=json.dumps(d,sort_keys=True,separators=(',',':'))+'\n'
    print([(r['reentry'],r['exit'],r['drop'],r['pause'],r['time']) for r in d['examples']])
    print(len(d['cases']),d['native_search_probes'],hashlib.sha256(raw.encode()).hexdigest())
    Path(sys.argv[2]).write_text(raw)

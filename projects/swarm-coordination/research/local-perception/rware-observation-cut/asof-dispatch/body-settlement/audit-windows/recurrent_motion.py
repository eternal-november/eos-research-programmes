"""Native recurring body-effect separation: an observed reset is not audit settlement."""
from itertools import product
import json
from same_queue import start,native,A,D,freeze

def trial(seed,origin,outcomes):
    w=start(origin,seed);w.max_steps=None
    x=6-origin
    re=native.Agent(x,3,D.DOWN,0)
    low=native.Agent(x,6,D.UP,0)
    high=native.Agent(x+(1 if x==4 else -1),0,D.LEFT if x==4 else D.RIGHT,0)
    w.agents.extend((re,low,high));w.n_agents+=3;w._recalc_grid()
    def step(who=0,act=A.NOOP):
        actions=[A.NOOP]*6;actions[who]=act
        obs,r,t,tr,info=native.step(w,actions)
        assert not t and not tr and not info
        return tuple(freeze(o) for o in obs),r
    def go(who,*acts):
        for a in acts:
            obs,r=step(who,a)
            assert not any(r)
        return obs
    assert step(1,A.FORWARD)[1]==[0,.5,0,0,0,0]
    m=w.request_queue[0].id
    assert m==(1 if seed==14 else 2)
    q=go(0,A.FORWARD)
    flag=any(v['shelf_requested'][0] for v in q[0]['sensors'])
    go(0,A.LEFT,A.LEFT,A.FORWARD)
    left,right=(A.LEFT,A.RIGHT) if m==1 else (A.RIGHT,A.LEFT)
    go(2,right,A.FORWARD,left,A.FORWARD,A.TOGGLE_LOAD,A.LEFT,A.LEFT,A.FORWARD,right)
    _,r=step(2,A.FORWARD)
    assert r==[0,0,.5,0,0,0] and tuple(y.id for y in w.request_queue)==(4,)
    go(5,A.FORWARD,A.LEFT if x==4 else A.RIGHT)
    def snapshot():
        return (tuple((b.id,int(b.x),int(b.y),b.dir.name,
                  b.carrying_shelf.id if b.carrying_shelf else None,b.has_delivered)
                  for b in w.agents),tuple((s.id,int(s.x),int(s.y)) for s in w.shelfs),
                  tuple(s.id for s in w.request_queue))
    anchor=snapshot();anchor_obs=freeze(w._make_obs(re))
    assert w._cur_steps==17 and (re.x,re.y,re.dir)==(x,3,D.DOWN)
    receipts=[];commands=[];views=[];native_rows=[]
    for i,effect in enumerate(outcomes):
        # Causal allowed histories differ only in the earlier positioning of
        # these passive occupants; there is no simultaneous forward request.
        move=A.NOOP if effect else A.FORWARD
        go(4,move,move);go(5,move,move)
        issued_at=w._cur_steps+1
        req=(A.FORWARD,A.LEFT,A.LEFT,A.FORWARD,A.LEFT,A.LEFT)
        for j,a in enumerate(req):
            pre=(re.x,re.y,re.dir)
            go(3,a)
            post=(re.x,re.y,re.dir)
            if a==A.FORWARD:
                assert bool(pre!=post)==effect
                assert re.req_action==(A.FORWARD if effect else A.NOOP)
            if j==0:receipts.append((re.id,i,issued_at,int(pre[1]),int(post[1])))
        for k in (4,5):go(k,A.LEFT,A.LEFT,move,move,A.LEFT,A.LEFT)
        # Reset even the native prev_x/prev_y & last command fields exposed
        # by the object after one final native no-op.
        end=go(3,A.NOOP)
        assert snapshot()==anchor and end[3]==anchor_obs
        assert all((a.prev_x,a.prev_y,a.req_action)==(a.x,a.y,A.NOOP) for a in w.agents)
        assert w._cur_steps==17+23*(i+1)
        views.append(end[3]);commands.append(tuple(a.name for a in req))
        native_rows.append(snapshot())
    return {"receipts":receipts,"commands":commands,"snapshots":native_rows,
            "observations":views,"source":(1,3,m,flag),"tick":w._cur_steps}

def audit(events,windows):
    return tuple(int(any(i==j and y0==3 and y1==4 for _,i,_,y0,y1 in events))
                 for j in windows)

def main():
    totals=[]
    for size in range(1,6):
        n=0
        for seed,origin in product((14,9),(2,4)):
            classes={};baskets=set();endpoints=set();own=set()
            for h in product((0,1),repeat=size):
                r=trial(seed,origin,h)
                current=(r['source'],r['tick'],r['commands'],r['snapshots'])
                endpoints.add(str(current));own.add(str(r['observations']))
                a=audit(r['receipts'],range(size))
                assert a==h
                assert int(any(a))==int(any(h))
                baskets.add(int(any(a)));classes[h]=a
                n+=1
            assert len(endpoints)==len(own)==1 and len(baskets)==2
            assert len(set(classes.values()))==2**size
        totals.append([size,n,2**size])
    print(json.dumps({"worlds":sum(n for _,n,_ in totals),"checks":totals,
       "invariant":"same sampled positions, headings, loads, queue and full local views for every outcome word",
       "slot_queries":"whichever prior row-4 entry the receiving auditor names"},sort_keys=True,separators=(',',':')))
if __name__=='__main__':main()

from pathlib import Path
from types import SimpleNamespace as NS
from fractions import Fraction
from itertools import product,permutations
import json,sys
if Path(__file__).with_name("native_adapter.py").exists():
    import native_adapter as bridge
    import rware_rotation as rot
else:
    root=Path(__file__).resolve().parents[1]
    sys.path.insert(0,str(root/'rware-simultaneous-port'))
    import check as rot
    sys.path.insert(0,str(root/'native-handoff-receipts'))
    import replay as bridge
bridge.rot=rot
from receiver import Cut,confirm

# O old at port, N incoming service, X lead of that chain,
# Q independent contender, every commanded physical step is square-grid cardinal.
P={'O':(1,3),'N':(1,4),'X':(2,3),'Q':(3,2)}
S=(2,2); PORT=P['O']
ONE={'O':P['X'],'N':PORT,'X':S,'Q':S}
EXITS={'X':(2,1),'Q':(1,2)}

def strict_longest(g):
    # Same DAG longest-path result, with unique maximizer checked. Native
    # handles self-loops before calling this. Refuse any ambiguous tie.
    chains=[]
    for s in set(g.s)-set(g.s.values()):
        row=[s]
        while row[-1] in g.s: row.append(g.s[row[-1]])
        chains.append(row)
    count=max(map(len,chains)); best=[r for r in chains if len(r)==count]
    assert len(best)==1,(g.s,best)
    return best[0]

def rware(src):
    n=bridge.load_warehouse(src)
    rot.iso.nx.algorithms.dag_longest_path=strict_longest
    D=n.Direction
    return n,{'O':D.RIGHT,'N':D.UP,'X':D.UP,'Q':D.LEFT}

def arm_warehouse(n,dirs,grant):
    order=['O','N','X','Q']
    w=rot.plant(n,tuple(P[i] for i in order),tuple(dirs[i] for i in order),
                ((0,P['O']),(1,P['N'])),PORT,[1])
    w.agents[0].has_delivered=True
    finished={'N':None,'Q':None}; log=[]
    for t in (1,2):
        before={i:(a.x,a.y) for i,a in zip(order,w.agents)}
        targets=ONE if t==1 else {**{i:ONE[i] for i in order if before[i]==P[i]},
                                  **{i:EXITS[i] for i in EXITS if before[i]==S}}
        acts=[int(i in targets and (t==2 or i in grant)) for i in order]
        _,credit,*_=n.step(w,acts)
        after={i:(a.x,a.y) for i,a in zip(order,w.agents)}
        moved=tuple(i for i in order if before[i]!=after[i])
        srv=tuple((i,PORT) for i,v,a in zip(order,credit,w.agents) if v==.5 and a.has_delivered)
        pend=frozenset({('O','return')}) if w.agents[0].has_delivered and w.agents[0].carrying_shelf else frozenset()
        rx=confirm(Cut(tuple(before.items()),tuple(after.items()),srv,pend),PORT,'O','N','return')
        if rx: finished['N']=t
        if after['Q']==S and before['Q']!=S: finished['Q']=t
        assert pend
        log.append(dict(t=t,moved=moved,after=after,confirmed=rx))
    return finished,log

def ep(p,q):
    dirs={(0,-1):0,(1,0):1,(0,1):2,(-1,0):3}
    return p,dirs[q[0]-p[0],q[1]-p[1]]

def arm_rail(n, grant, ranks, terminal_q=False):
    order=list(P); counter=dict(zip(order,ranks))
    W=NS(remove_agents_at_target=False,rail=NS(edge_length=lambda a,b:Fraction(1)),
      distance_map=None,rewards_dict={i:0 for i in ranks},dones={})
    W.rewards=NS(cumulate=lambda a,b:a+b,step_reward=lambda **kw:0)
    W.handle_done_state=lambda a:n.handle_done_state(W,a)
    res=n.GridResourceMap()
    # Choice of orientation after next point not examined by this resource map;
    # use the same heading and one more cardinal cell for the fixture routes.
    V={}
    for i in order:
        c=ep(P[i],ONE[i]);d=(ONE[i],c[1])
        a=NS(handle=counter[i],current_entry_point=c,next_entry_point=d,
             target_entry_point=None,arrival_time=None,
             targets=[d] if i=='N' or (i=='Q' and terminal_q) else [((4,4),0)],speed_counter=bridge.Speed())
        V[i]=a
    finished={'N':None,'Q':None};log=[]
    for t in (1,2):
        W._elapsed_steps=t;W.resource_check=n.MotionCheck()
        before={i:res.get_resource(a.current_entry_point,a.next_entry_point) for i,a in V.items()}
        T={}
        for i,a in V.items():
            c=a.current_entry_point;d=a.next_entry_point;a.old_entry_point=c
            vx,vy=(d[0][0]-c[0][0],d[0][1]-c[0][1])
            z=((d[0][0]+vx,d[0][1]+vy),d[1])
            # Old trip is still ongoing, but once it vacates port it holds
            # the next cell for the rest of this two-cut experiment.
            hold=(t==1 and i not in grant) or (i=='O' and before[i]!=PORT)
            done=a.target_entry_point is not None
            b,c1=n._candidate_entry_points(n.RailEnvActions.MOVE_FORWARD,c,d,done,hold,
                       t,z,1,c,False,True,False,False,False,False)
            T[i]=NS(candidate_entry_point=b,candidate_next_entry_point=c1,is_cell_exit=True,
              done=done,candidate_distance=Fraction(0),candidate_speed=Fraction(1),
              distance=Fraction(0),edge_length=Fraction(1))
            W.resource_check.add_agent(a.handle,before[i],res.get_resource(b,c1))
        W.resource_check.find_conflicts()
        for i,a in V.items():n.distribute(W,a,T[i])
        after={i:res.get_resource(a.current_entry_point,a.next_entry_point) for i,a in V.items()}
        svc=tuple((i,res.get_resource(a.target_entry_point,None))
                  for i,a in V.items() if a.arrival_time==t)
        pending=frozenset((i,'trip') for i,a in V.items() if a.arrival_time is None)
        rx=confirm(Cut(tuple(before.items()),tuple(after.items()),svc,pending),PORT,'O','N','trip')
        if rx:finished['N']=t
        if after['Q']==S and before['Q']!=S: finished['Q']=t
        assert ('O','trip') in pending
        log.append(dict(t=t,moved=tuple(i for i in order if before[i]!=after[i]),
                        after=after,confirmed=rx))
    return finished,log

def reference(grant, arbitration, ranks=None):
    # Initial targets merge in S, otherwise disjoint. For this fixture the
    # old chain's downstream prefix length is 1+X's consecutive followers.
    chain=[]
    for i in ['X','O','N']:
        if i not in grant:break
        chain.append(i)
    q='Q' in grant
    if not chain:return {'Q'} if q else set()
    if not q:return set(chain)
    if arbitration=='warehouse':
        assert len(chain)>1
        return set(chain)
    return set(chain) if ranks['X']<ranks['Q'] else {'Q'}

def main(src):
    w,d=rware(src); n=bridge.native_rail(src)
    rows=[]; keys=list(P)
    for v in product((False,True),repeat=4):
        grant={i for i,f in zip(keys,v) if f}
        # No warehouse tie-breaking claim when both have length one.
        if not ('X' in grant and 'O' not in grant and 'Q' in grant):
            a,t=arm_warehouse(w,d,grant)
            assert set(t[0]['moved'])==reference(grant,'warehouse')
            rows.append(dict(model='warehouse',grants=sorted(grant),finished=a,trace=t))
        for rank in permutations(range(4)):
            a,t=arm_rail(n,grant,rank)
            assert set(t[0]['moved'])==reference(grant,'rail',dict(zip(keys,rank)))
            rows.append(dict(model='rail',rank=rank,grants=sorted(grant),finished=a,trace=t))
    s=[a for a in rows if set(a['grants'])==set(keys)]
    assert s[0]['finished']=={'N':1,'Q':2}
    for a in s[1:]:
        q=a['rank'][3]<a['rank'][2]
        assert a['finished']==({'N':2,'Q':1} if q else {'N':1,'Q':2}),a
    # Chosen visibility/authority regime: other agent must receive its
    # grant before the effect; once issued, no hidden intervention may erase it.
    Xhigher=arm_rail(n,set(keys),(0,1,2,3))[0]
    Qhigher=arm_rail(n,set(keys),(0,1,3,2))[0]
    WithdrawQ=arm_rail(n,set(keys)-{'Q'},(0,1,3,2))[0]
    assert Xhigher==WithdrawQ=={'N':1,'Q':2} and Qhigher=={'N':2,'Q':1}
    assert arm_warehouse(w,d,set(keys)-{'X'})[0]=={'N':2,'Q':1}
    terminal=arm_rail(n,set(keys),(0,1,3,2),terminal_q=True)
    assert terminal[0]=={'N':None,'Q':1}
    return dict(rows=rows,examples=dict(Xhigher=Xhigher,Qhigher=Qhigher,WithdrawQ=WithdrawQ,terminal=terminal))
if __name__=='__main__':
    x=main(Path(sys.argv[1]))
    print(json.dumps(x,sort_keys=True,separators=(',',':')))

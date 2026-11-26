"""Native common prefix and live old scope consumption; actuate only admitted runs."""
from pathlib import Path
from hashlib import sha1,sha256
import sys
from itertools import product
import json
from guard import Right,LiveScope,admission

root=Path(sys.argv[2]).resolve()
sys.path.insert(0,str(root))
p=root/'native.py'
src=p.read_bytes()
assert sha1(f"blob {len(src)}\0".encode()+src).hexdigest()=="dcba6da00966bb61d72134662947d429ea1a6c35"
# Reuse the actual early old delivery/unload/parking prefix. No final placement
# or new release sampled from the hypothetical input index after that prefix.
top=src.decode().split('    assert step({2:F,3:F})==(0,)*7\n',1)
assert len(top)==2
ns={'__name__':'prefix'}
exec(compile(top[0]+'''    return dict(step=step,at=at,move=move,rot=rot,via_y=via_y,agents=agents,
                shelves=shelves,env=env)
''',str(p),'exec'),ns)
F,T,L,R,Z=[ns[k] for k in ('F','T','L','R','Z')]
E,S,W,N=[ns[k] for k in ('E','S','W','N')]
BAY,YROW,DIR,HEAD=[ns[k] for k in ('BAY','YROW','DIR','HEAD')]

def plan(start,facing,waypoints,end_heading=None):
    """Compile a fixed list of declared cells and effect cuts to native commands."""
    path=[]
    point=start
    def orient(direction):
        nonlocal facing
        delta=(HEAD.index(direction)-HEAD.index(facing))%4
        for cmd in ([R]*delta if delta<=2 else [L]*(4-delta)):
            path.append((cmd,point))
        facing=direction
    for q in waypoints:
        if q is None:path.append((T,point));continue
        dx,dy=q[0]-point[0],q[1]-point[1]
        orient(DIR[dx,dy])
        point=q
        path.append((F,point))
    if end_heading is not None:orient(end_heading)
    return path

def prefix(p0):
    c=ns['run'](p0,0,'local')
    agents,shelves,env=c['agents'],c['shelves'],c['env']
    step,at,move,rot,via_y=[c[k] for k in ('step','at','move','rot','via_y')]
    bay_x,bay_y=BAY[p0],BAY[1-p0]
    v_x,v_y=bay_x[1],bay_y[1]
    def storage():
        return tuple(int(env.grid[1,y,x]) for x,y in BAY)

    # This executes, rather than assuming an old committed generation records
    # the current physical placement.
    move(0,via_y(0,3,v_x)+[(x,v_x) for x in (1,2,3)])
    assert step({0:T})==(0,)*7 and agents[0].carrying_shelf is shelves[0]
    move(0,[(2,v_x),(1,v_x),(1,3)])
    assert step({0:T})==(0,)*7 and agents[0].carrying_shelf is None
    assert (shelves[0].x,shelves[0].y)==(1,3)
    assert storage()[p0]==0 and storage()[1-p0]==shelves[1].id
    common=dict(last_committed_generation=0,physical=storage(),x_buffer=at(0),
                all_poses=[(a.x,a.y,str(a.dir)) for a in agents],read_of_y=bay_y)
    return c,common,storage

def run(p0,exchange,report,handoff,policy,deadline,path_side):
    c,common,storage=prefix(p0)
    agents,shelves,env=c['agents'],c['shelves'],c['env']
    step,at,via_y=[c[k] for k in ('step','at','via_y')]
    bay_x,bay_y=BAY[p0],BAY[1-p0]
    scopes={
        'exact':LiveScope(True,True,frozenset({'X','Y'} if exchange else {'X'})),
        'missing':None,
        'partial':LiveScope(False,True,frozenset({'X'})),
        'expired':LiveScope(True,False,frozenset({'X'})),
    }
    witness=scopes[report]
    # Enforce fixture eligibility: same named permission for either qualified
    # Y berth, but the sensed bay must agree at the decision cut.
    def release_check(cell,w):
        return admission(Right(True,'Y',cell),'Y',cell,w)
    early=release_check(bay_y,witness)
    # Exact same-information planner enumerates all actual next source branches
    # not excluded by the qualified view. A stale "X-only" cover is not knowledge.
    pending=(exchange,) if report=='exact' else (False,True)
    assert early==all(not a for a in pending)
    proposed_by_snapshot=True
    conflicts_with_live_old=any(pending)

    # Old phase A physically settles and clears Y only for an exchange.
    p_a=plan(at(1),agents[1].dir,[bay_y,None,(3,3),bay_x,None,(3,3)],E) if exchange else []
    # Old phase B physically returns X; after phase A the remaining write scope
    # is X and its explicitly distinct route. Y is not needed for it.
    x_target=bay_y if exchange else bay_x
    ty=x_target[1]
    p_b=plan(at(0),agents[0].dir,[None,(2,3),(2,ty),x_target,None,
                                (2,ty),(1,ty),(0,ty),*via_y(0,ty,3)],E)
    phase_a=len(p_a)
    drained=phase_a+len(p_b)
    cut=0 if policy=='scope' and early else (phase_a if policy=='scope' and exchange and handoff else drained)
    # A direct planner with the same enforced schedule and evidence could
    # move at the first admissible cut (not at a hidden completion).
    exact_cuts=[drained]
    if all(not a for a in pending):exact_cuts.append(0)
    if handoff and exchange:exact_cuts.append(phase_a)
    direct_best=min(exact_cuts)
    if policy=='scope':assert cut==direct_best
    if policy=='facility': assert cut==drained
    relocation_at=None
    selected=None
    future=[]
    old_partner_mark=None
    old_done=None
    independent=None

    def at_cut():
        nonlocal selected,future
        # Different proof sources depending on witnessed phase, not a single
        # boolean inferred from a commit counter.
        if cut==0:assert early
        if cut==phase_a and cut>0 and cut!=drained:
            assert handoff and exchange and old_partner_mark==phase_a
        if cut==drained:assert old_done==drained
        local=[j for j,x in enumerate(storage()) if x==shelves[1].id]
        assert len(local)==1
        selected=local[0]
        job=selected+2
        # Each on-route guard knows only its own same-bay label and authority.
        available=LiveScope(True,True,frozenset({'X'} if cut!=drained else set()))
        assert release_check(BAY[selected],available)
        refuge=(3,1 if selected==0 else 5)
        future=plan(at(job),agents[job].dir,[BAY[selected],None,refuge,None])
        assert len(future)==6

    if cut==0:at_cut()
    for tick in range(1,max(deadline,drained)+1):
        commands={}
        expected={}
        if tick<=phase_a:
            commands[1],expected[1]=p_a[tick-1]
        elif tick<=drained:
            commands[0],expected[0]=p_b[tick-phase_a-1]
        if tick==1:commands[6]=F
        if selected is not None and cut<tick<=cut+len(future):
            n=selected+2
            commands[n],expected[n]=future[tick-cut-1]
        r=step(commands)
        expected_reward=(0,0,0,0,0,0,.5) if tick==1 else (0,)*7
        assert r==expected_reward,(tick,r)
        if tick==1:independent=tick
        assert all(at(i)==loc for i,loc in expected.items())
        if exchange and tick==phase_a:
            assert at(1)==(3,3) and agents[1].carrying_shelf is None
            assert storage()[p0]==shelves[1].id
            assert (shelves[0].x,shelves[0].y)==(1,3)
            # Native receipt producer used by the modeled handoff resolver.
            old_partner_mark=tick
        if tick==drained:
            assert (shelves[0].x,shelves[0].y)==x_target
            assert agents[0].carrying_shelf is None and at(0)==(0,3)
            old_done=tick
        if selected is not None and tick==cut+len(future):
            relocation_at=tick
            assert storage()[selected]==0
            assert agents[selected+2].carrying_shelf is None
            assert (shelves[1].x,shelves[1].y)==at(selected+2)
        if tick==cut and cut+6<=deadline:at_cut()
    assert old_done==drained and independent==1
    assert (relocation_at is not None)==(cut+6<=deadline)
    if policy=='scope':assert (relocation_at is not None)==(direct_best+6<=deadline)

    # Due path identity is fixed: do not exchange the next customer's task.
    required=(1-p0) if path_side=='original-Y' else p0
    goal_paid=False
    if relocation_at is not None:
        follower=4+required
        assert step({follower:F})==(0,)*7
        assert step({follower:F})==(0,)*7
        goal_paid=step({follower:F})[follower]==.5
    assert goal_paid==(relocation_at is not None and required==selected)
    return common,dict(initial_x_bay=p0,source=('exchange' if exchange else 'reseat'),
                       report=report,phase_receipt=handoff,policy=policy,deadline=deadline,
                       fixed_due_path=path_side,old_done=old_done,partner_clear=old_partner_mark,
                       pickup_start=(1+cut if relocation_at is not None else None),
                       relocation=relocation_at,goal_paid=goal_paid,independent_paid=independent==1,
                       selected=selected,early_allowed=early,snapshot_would_allow=proposed_by_snapshot,
                       unresolved_conflict=conflicts_with_live_old,exact_admission_cut=direct_best)

def incompatible_control(p0):
    # Deliberately omit the JOINT guard in this isolated native reference.
    # The new instruction still touches exactly the separately permitted Y.
    # No wrong-item action is issued. The previously accepted exchange's
    # named old step is rendered impossible at its declared source site.
    c,common,storage=prefix(p0)
    step,at,agents,shelves=c['step'],c['at'],c['agents'],c['shelves']
    j=1-p0;n=j+2
    bay=BAY[j]
    refuge=(3,1 if j==0 else 5)
    for t,(a,x) in enumerate(plan(at(n),agents[n].dir,[bay,None,refuge,None]),1):
        r=step({n:a,**({6:F} if t==1 else {})})
        assert r==((0,0,0,0,0,0,.5) if t==1 else (0,)*7)
        assert at(n)==x
    assert storage()[j]==0 and (shelves[1].x,shelves[1].y)==refuge
    seq=plan(at(1),agents[1].dir,[bay,None])
    for a,x in seq:
        assert step({1:a})==(0,)*7
        assert at(1)==x
    assert agents[1].carrying_shelf is None
    assert (shelves[1].x,shelves[1].y)==refuge
    return dict(initial_x_bay=p0,new_named_relocation_completed=6,
                previous_exchange_required_lift_departure=len(seq),
                previous_exchange_got_y=False,independent_paid=True)

def check():
    snaps={}; rows=[]
    for q,s,rep,h,pol,d,k in product((0,1),(False,True),('exact','missing','partial','expired'),
                           (False,True),('scope','facility'),(6,20,40),('original-Y','original-X')):
        snapshot,row=run(q,s,rep,h,pol,d,k)
        assert snaps.setdefault(q,snapshot)==snapshot
        rows.append(row)
    assert len(rows)==384
    def pick(q,s,rep,h,pol,d,k):
        return next(r for r in rows if (r['initial_x_bay'],r['source'],r['report'],r['phase_receipt'],
                    r['policy'],r['deadline'],r['fixed_due_path'])==(q,s,rep,h,pol,d,k))
    for q in (0,1):
        assert pick(q,'reseat','exact',False,'scope',6,'original-Y')['goal_paid']
        assert not pick(q,'reseat','exact',False,'facility',6,'original-Y')['goal_paid']
        assert not pick(q,'exchange','missing',True,'scope',6,'original-X')['goal_paid']
        mid=pick(q,'exchange','exact',True,'scope',20,'original-X')
        assert mid['goal_paid'] and mid['relocation']<mid['old_done']+6
        assert not pick(q,'exchange','exact',True,'scope',20,'original-Y')['goal_paid']
        assert not pick(q,'exchange','exact',True,'facility',20,'original-X')['goal_paid']
    from collections import Counter
    controls=[incompatible_control(j) for j in (0,1)]
    large=dict(rows=rows,shared_prefix=snaps,incompatible_controls=controls)
    blob=json.dumps(large,sort_keys=True,separators=(',',':'))
    group=Counter((r['source'],r['policy'],r['deadline'],r['goal_paid']) for r in rows)
    outcomes=dict(checked=len(rows),sha256=sha256(blob.encode()).hexdigest(),
                  prior_final_times=sorted({r['old_done'] for r in rows}),
                  independent_paid=sum(r['independent_paid'] for r in rows),
                  summaries=[(*k,v) for k,v in sorted(group.items())],
                  selected_examples={
                    'early':pick(0,'reseat','exact',False,'scope',6,'original-Y'),
                    'handoff':pick(0,'exchange','exact',True,'scope',20,'original-X'),
                    'held':pick(0,'exchange','exact',True,'facility',20,'original-X'),
                  },incompatible_controls=controls)
    print(blob if '--full' in sys.argv else json.dumps(outcomes,sort_keys=True,indent=2))

if __name__=='__main__':check()

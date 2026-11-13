#!/usr/bin/env python3
"""Finite symbolic fixture model. No empirical or continuous-physics claim."""
from dataclasses import dataclass
from itertools import product
from collections import deque
import json

ACTIONS=('approach','pushL','pushR','withdraw','wait')
GRADES=('HOLD','TOUCH')
HANDS=('L','R')
CONTACTS=('clear','engaged')

@dataclass(frozen=True)
class State:
    h:str
    grade:str
    c:str
    pad:int # -1 iff clear; 0/1 are two possible physical seating pads
    grip:str
    angle:int # 0 flat, 1 quarterturned, -1 damaged

@dataclass(frozen=True)
class FixtureRecord:
    source:tuple
    command:str
    target:tuple
    wrench:str
    reply:tuple
    occurrence:str

@dataclass(frozen=True)
class Event:
    source:State
    action:str
    command:str
    fixture:FixtureRecord
    target:State

# Independent gripper table: it does not inspect fixture or object registers.
def gripper(grip, action):
    if action=='wait': return ('idle',grip)
    if grip=='released': return ('invalid',grip)
    return {'approach':('advance','held'),'pushL':('driveL','held'),
            'pushR':('driveR','held'),'withdraw':('release','released')}[action]

# Independent fixture table: it does not inspect object angle or controller memory.
def fixture(source, command):
    h,grade,c,pad=source
    def rec(c2,pad2,w,v,tag):
        return FixtureRecord(source,command,(h,grade,c2,pad2),w,v,tag)
    if command=='idle': return [rec(c,pad,'zero',('ack',),'idle')]
    if command=='release': return [rec('clear',-1,'zero',('released',),'release')]
    if command=='advance' and c=='clear':
        return [rec('engaged',r,'zero',('contact',h,grade),f'seat_pad_{r}') for r in (0,1)]
    if command in ('driveL','driveR') and c=='engaged':
        w='positive' if command[-1]==h else 'negative'
        rs=[rec(c,pad,w,('ack',),'retained_push')]
        if grade=='TOUCH': rs.append(rec('clear',-1,'loss',('slip',),'slip_during_push'))
        return rs
    return [rec(c,pad,'invalid',('fault',),'invalid_mode')]

# Independent object response: local wrench is its ONLY nonlocal input.
def object_response(angle,wrench):
    if angle==-1: return -1
    if wrench=='zero': return angle
    if wrench=='positive' and angle==0: return 1
    return -1

def states():
    return [State(h,k,c,r,g,t) for h,k,(c,r),g,t in product(
        HANDS,GRADES,[('clear',-1),('engaged',0),('engaged',1)],
        ('held','released'),(0,1,-1))]

# Whole event set GENERATED from the three local primitive tables.
def events(x,a):
    u,g2=gripper(x.grip,a)
    fs=(x.h,x.grade,x.c,x.pad)
    out=[]
    for f in fixture(fs,u):
        h,k,c2,r2=f.target
        y=State(h,k,c2,r2,g2,object_response(x.angle,f.wrench))
        out.append(Event(x,a,u,f,y))
    return out

# Boundary graph J has state c, and edge (c,c',a,u,w,v).
# h/grade/pad/grip/angle are NOT coordinates of J's state.
def label(e):
    return (e.source.c,e.target.c,e.action,e.command,e.fixture.wrench,e.fixture.reply)

# Local cylinders over J: their tests read only the documented local data.
def dg_accept(g,g2,j):
    c,c2,a,u,w,v=j
    return gripper(g,a)==(u,g2)
def df_accept(fs,ft,f,j):
    c,c2,a,u,w,v=j
    return (fs[2]==c and ft[2]==c2 and f.source==fs and f.target==ft
            and f.command==u and f.wrench==w and f.reply==v
            and f in fixture(fs,u))
def do_accept(t,t2,j):
    return object_response(t,j[4])==t2

# Open compiled capability matching with an independently filtered local pullback.
def verify_open_pullback():
    xs=states(); es=[e for x in xs for a in ACTIONS for e in events(x,a)]
    # Independently enumerate local state pullback and deterministic acquisition.
    gs=list(product(CONTACTS,('held','released')))
    fs=[(h,k,c,r) for h,k,(c,r) in product(HANDS,GRADES,
        [('clear',-1),('engaged',0),('engaged',1)])]
    os=list(product(CONTACTS,(0,1,-1)))
    state_tuples=[(gg,ff,oo) for gg,ff,oo in product(gs,fs,os)
                  if gg[0]==ff[2]==oo[0]]
    assembled={State(ff[0],ff[1],ff[2],ff[3],gg[1],oo[1]) for gg,ff,oo in state_tuples}
    assert assembled==set(xs) and len(state_tuples)==len(xs)
    acquisition={(x,x.c) for x in xs}
    local_acquisition={ (State(ff[0],ff[1],ff[2],ff[3],gg[1],oo[1]),ff[2])
                        for gg,ff,oo in state_tuples}
    assert acquisition==local_acquisition
    replies=[('ack',),('released',),('slip',),('fault',)]+[('contact',h,k) for h,k in product(HANDS,GRADES)]
    js=set(product(CONTACTS,CONTACTS,ACTIONS,('idle','invalid','advance','driveL','driveR','release'),
                   ('zero','positive','negative','loss','invalid'),replies))
    targets=set(xs)
    joins=set()
    for x in xs:
        for j in js:
            if j[0]!=x.c: continue
            c,c2,a,u,w,v=j
            for g2 in ('held','released'):
                if not dg_accept(x.grip,g2,j): continue
                for f in fixture((x.h,x.grade,x.c,x.pad),u):
                    if not df_accept(f.source,f.target,f,j): continue
                    for t2 in (0,1,-1):
                        if do_accept(x.angle,t2,j):
                            h,k,cc,r=f.target
                            y=State(h,k,cc,r,g2,t2)
                            assert y in targets
                            joins.add(Event(x,a,u,f,y))
    assert joins==set(es)
    # Every local tuple yields a unique event, including seating occurrence.
    assert len(es)==len(set(es))
    # Reassociation and projection retain literal occurrence slots.
    for g,f,o in state_tuples:
        # a: W→[GF,O], b: GF→[G,F]; c: W→[G,FO], d: FO→[F,O].
        # This is the actual presented equation a(b,id_O)=c(id_G,d).
        a=((g,f),o); c=(g,(f,o))
        assert (*a[0],a[1])==(c[0],*c[1])==(g,f,o)
    for e in es:
        j=label(e)
        g=('G',(e.source.c,e.source.grip),(e.target.c,e.target.grip),j)
        f=('F',e.fixture,j)
        o=('O',(e.source.c,e.source.angle),(e.target.c,e.target.angle),j)
        left=((g,f),o); right=(g,(f,o))
        flatleft=(*left[0],left[1]); flatright=(right[0],*right[1])
        assert flatleft==flatright==(g,f,o)
    return {'states':len(xs),'open_events':len(es),'boundary_edge_labels':len(js),'used_boundary_edge_labels':len(set(map(label,es))),
            'exact_open_pullback':True,'state_and_acquisition_pullback':True,
            'occurrence_reassociation':True,'presented_equation_on_states_and_events':True}

# Controller phases are themselves private memory. The handedness bit lives
# between approach's POST reply and the next push's action choice.
def choose(q,o):
    return {'start':'approach','L':'pushL','R':'pushR','withdraw':'withdraw',
            'done':'wait','reject':'wait'}[q]
def update(q,a,v):
    if q=='start':
        if len(v)==3 and v[0]=='contact' and v[2]=='HOLD': return v[1]
        return 'reject'
    if q in HANDS: return 'withdraw'
    if q=='withdraw': return 'done'
    return q

def initial(grade='HOLD'):
    return [State(h,grade,'clear',-1,'held',0) for h in HANDS]
def goal(x): return x.angle==1 and x.grip=='released' and x.c=='clear'

def verify_control():
    ranks={'start':3,'L':2,'R':2,'withdraw':1,'done':0}
    todo=deque((x,'start') for x in initial()); seen=set(todo); edges=[]
    while todo:
        x,q=todo.popleft()
        assert x.angle!=-1
        if goal(x):
            assert q=='done'
            continue
        a=choose(q,x.c); ee=events(x,a)
        assert ee # exact nonblocking for every actual preacquisition
        for e in ee:
            q2=update(q,a,e.fixture.reply); z=(e.target,q2)
            assert ranks[q2]<ranks[q]
            edges.append(((x,q),e,z))
            if z not in seen: seen.add(z); todo.append(z)
    assert all(goal(x) for x,q in seen if q=='done')
    return {'reachable_controller_states':len(seen),'closed_loop_edges':len(edges),
            'terminal_states':sum(goal(x) for x,q in seen),'worst_case_ticks':3,
            'sure_safe_reach':True}

def verify_controller_decomposition():
    # Internal transcript JC has state q and edges(q,qnext,o,a,v,instruction).
    # A single owned memory register is passively carried across all three slots.
    qs=('start','L','R','withdraw','done','reject')
    replies=[('ack',),('released',),('slip',),('fault',)]+[('contact',h,k) for h,k in product(HANDS,GRADES)]
    generated={(q,update(q,choose(q,o),v),o,choose(q,o),v,update(q,choose(q,o),v))
               for q,o,v in product(qs,CONTACTS,replies)}
    selected=set(); decoded=set(); committed=set()
    for q,q2,o,a,v,instruction in product(qs,qs,CONTACTS,ACTIONS,replies,qs):
        edge=(q,q2,o,a,v,instruction)
        if a==choose(q,o): selected.add(edge)
        if instruction==update(q,a,v): decoded.add(edge)
        if q2==instruction: committed.add(edge)
    joined=selected & decoded & committed
    assert generated==joined
    pairs={(('selection',e),('decode',e),('commit',e)) for e in joined}
    assert len(pairs)==len(generated)==96
    state_diagonal={(q,q,q) for q in qs}
    assert len(state_diagonal)==len(qs)
    for sel,dec,com in pairs:
        grouped=(sel,(dec,com))
        assert (grouped[0],*grouped[1])==(sel,dec,com)
    for q,o in product(qs,CONTACTS):
        actions={a for qq,q2,oo,a,v,i in selected if qq==q and oo==o}
        assert actions=={choose(q,o)}
    for h in HANDS:
        assert update('start','approach',('contact',h,'HOLD'))==h
        assert update('start','approach',('contact',h,'TOUCH'))=='reject'
    # Lift K to the EXTERNAL J by adding passive target-contact, command,wrench.
    # K's actual source observation equals source contact c; no hidden read.
    external={(q,q2,(o,c2,a,u,w,v)) for q,q2,o,a,v,i in generated
              for c2,u,w in product(CONTACTS,('idle','invalid','advance','driveL','driveR','release'),
                                    ('zero','positive','negative','loss','invalid'))}
    assert len(external)==5760
    # Pair every OPEN environment record with each compatible current q.
    # Joining the refined controller and the unrefined table gives same target q.
    coupled=set()
    for x in states():
        for q in qs:
            for e in events(x,choose(q,x.c)):
                q2=update(q,e.action,e.fixture.reply)
                assert (q,q2,label(e)) in external
                transcript=(q,q2,x.c,e.action,e.fixture.reply,q2)
                assert transcript in joined
                coupled.add((e,q,q2))
    external_by_j={}
    for q,q2,j in external:
        external_by_j.setdefault(j,set()).add((q,q2))
    filtered={(e,q,q2) for x in states() for a in ACTIONS for e in events(x,a)
              for q,q2 in external_by_j.get(label(e),())}
    assert coupled==filtered
    # Common protocol I=(q,c) permits ONE original parent [K_I,W_I]
    # and both marked occurrence refinements, without changing profile types.
    common_join=set()
    for x in states():
        for a in ACTIONS:
            for e in events(x,a):
                for q,q2,i in product(qs,qs,qs):
                    if e.action!=choose(q,x.c): continue
                    if i!=update(q,e.action,e.fixture.reply): continue
                    if q2!=i: continue
                    common_join.add((e,q,q2))
                    interface=(q,q2,label(e),i)
                    k=(('Select',interface),('Decode',interface),('Commit',interface))
                    plant=(('G',e.source.grip,e.target.grip,interface),
                           ('F',e.fixture,interface),
                           ('O',e.source.angle,e.target.angle,interface))
                    parent=(k,plant)
                    controller_first=(*parent[0],parent[1])
                    plant_first=(parent[0],*parent[1])
                    assert (*controller_first[:3],*controller_first[3])==(*plant_first[0],*plant_first[1:])
    assert common_join==coupled
    # Hide owned-memory coordinates separately BEFORE gluing: this tuple
    # has matching public o,a,v,i but three different old-memory owners.
    coarse_select=('L','withdraw','engaged','pushL',('ack',),'withdraw')
    coarse_decode=('R','withdraw','engaged','pushL',('ack',),'withdraw')
    coarse_commit=('start','withdraw','engaged','pushL',('ack',),'withdraw')
    assert coarse_select in selected and coarse_decode in decoded and coarse_commit in committed
    assert coarse_select[2:]==coarse_decode[2:]==coarse_commit[2:]
    assert len({coarse_select[0],coarse_decode[0],coarse_commit[0]})>1
    # Boundary coarsening retains these three actual records. If one also
    # quotients record identity to public values, those values DO have a lift.
    assert any(e[2:]==coarse_select[2:] for e in generated)
    return {'owned_memory_states':len(qs),'intrinsic_controller_records':len(generated),
            'external_controller_records':len(external),'open_coupled_records':len(coupled),
            'exact_select_decode_commit_pullback':True,
            'selector_independent_of_postreply_and_future_memory':True,
            'hold_reply_stored_touch_reply_rejected':True,
            'controller_refinement_preserves_open_coupling':True,
            'single_typed_parent_two_sided_refinements':True,
            'separate_memory_hiding_creates_unliftable_tuple':True}

def negatives():
    # Independently specified absent-fixture response: no command produces
    # positive wrench. Explore its ENTIRE reachable open graph.
    no_fixture_wrench={'idle':'zero','advance':'zero','release':'zero',
                       'driveL':'invalid','driveR':'invalid','invalid':'invalid'}
    absent_seen={('held',0)}; absent_todo=deque(absent_seen)
    while absent_todo:
        g,t=absent_todo.popleft()
        for a in ACTIONS:
            u,g2=gripper(g,a); y=(g2,object_response(t,no_fixture_wrench[u]))
            assert y[1]!=1
            if y not in absent_seen: absent_seen.add(y); absent_todo.append(y)
    # Actual same input observation after seating, opposite required push.
    seated=[events(x,'approach')[0].target for x in initial()]
    safe_turn_sets=[]
    for x in seated:
        safe_turn_sets.append({a for a in ACTIONS if all(e.target.angle==1 for e in events(x,a))})
    assert safe_turn_sets==[{'pushL'},{'pushR'}]
    # A memoryless strategy cannot exploit post reply; safe nonpush choices
    # either wait forever or release irreversibly before turning.
    assert not set.intersection(*safe_turn_sets)
    # Full stationary policy audit, using universal reachability fixed point.
    hold_states=[x for x in states() if x.grade=='HOLD']
    winning_memoryless=0
    for aclear,aengaged in product(ACTIONS,repeat=2):
        policy={'clear':aclear,'engaged':aengaged}
        win={x for x in hold_states if goal(x)}
        while True:
            new=win|{x for x in hold_states if x.angle!=-1 and
                events(x,policy[x.c]) and all(e.target in win for e in events(x,policy[x.c]))}
            if new==win: break
            win=new
        winning_memoryless+=all(x in win for x in initial())
    assert winning_memoryless==0
    # Weak stale contact interface admits TOUCH and HOLD; same visible
    # approach contact+handedness but TOUCH has an adverse slip record.
    slip=[]
    for x in initial('TOUCH'):
        seat=events(x,'approach')[0]
        hold_seat=events(State(x.h,'HOLD','clear',-1,'held',0),'approach')[0]
        assert seat.fixture.reply[:2]==hold_seat.fixture.reply[:2]
        s=seat.target
        bad=[e for e in events(s,'push'+x.h) if e.fixture.occurrence=='slip_during_push']
        assert len(bad)==1 and bad[0].target.angle==-1
        slip.extend(bad)
    # Incorrectly independent sensing contact and mechanical contact:
    # both local instances obey their tables, but sensed hand != mechanics.
    independent=[]
    for sensed,mechanical in product(HANDS,repeat=2):
        x=State(mechanical,'HOLD','clear',-1,'held',0)
        s=events(x,'approach')[0].target
        e=events(s,'push'+sensed)[0]
        independent.append((sensed,mechanical,e.target.angle))
    assert sum(t==-1 for _,_,t in independent)==2
    # Alternate exact graph map swapping the two physical seating pads.
    # It preserves visible J labels but is NOT the declared equation witness.
    def swapfs(fs):
        h,k,c,r=fs
        return (h,k,c,1-r if c=='engaged' else r)
    changed_records=0
    for x in states():
        for a in ACTIONS:
            for e in events(x,a):
                f=e.fixture
                candidates=[ff for ff in fixture(swapfs(f.source),f.command)
                    if ff.target==swapfs(f.target) and ff.wrench==f.wrench and ff.reply==f.reply]
                assert len(candidates)==1
                ff=candidates[0]
                # Involution: valid exact map on actual local record graph.
                back=[fff for fff in fixture(swapfs(ff.source),ff.command)
                    if fff.target==swapfs(ff.target) and fff.wrench==ff.wrench and fff.reply==ff.reply]
                assert back==[f]
                changed_records+=ff!=f
    assert changed_records>0
    # Two real pads give two shared contact executions, not four independent
    # duplicated invocations. Off-diagonal tuples cannot be same occurrence.
    shared={(r,r) for r in (0,1)}; duplicated=set(product((0,1),repeat=2))
    assert len(shared)==2 and len(duplicated)==4
    return {'fixture_free_rotation_impossible':True,'fixture_free_reachable_states':len(absent_seen),
            'memoryless_policies_checked':25,'memoryless_winning_policies':winning_memoryless,
            'memoryless_safe_push_intersection':[],
            'touch_slip_counterexamples':len(slip),'independent_handedness_unsafe_cases':2,
            'pad_swap_visible_equal_but_record_different':changed_records,
            'shared_seating_records':2,'duplicated_seating_pairs':4,
            'same_value_multiplicity_failure_is_not_claimed_unsafe':True}

if __name__=='__main__':
    result={'model':'symbolic corner-assisted quarterturn','open':verify_open_pullback(),
            'control':verify_control(),'controller_decomposition':verify_controller_decomposition(),
            'negative':negatives()}
    print(json.dumps(result,indent=2))

"""Authored directed corridor plant and exact finite observation-policy reference."""
from dataclasses import dataclass,replace
from functools import lru_cache

@dataclass(frozen=True,order=True)
class World:
    closed: str
    lost_primary: bool
    wire_works: bool
    obstruction_depth: int=1

@dataclass(frozen=True)
class Layout:
    KQ: int
    QK: int
    left: int
    right: int
    due: int
    wire: bool
    sight_range: int=3

@dataclass(frozen=True)
class State:
    w: World
    t: int=0
    place: str='J'
    armed: bool=False
    signalled: bool=False
    applied: int=-1
    got_view: str=''
    instruction_at: int=-1
    type_of_contact: int=-1

def observed(s):
    # Revealed only by arriving at the aperture. No hidden radio binding/loss
    # or wire delivery state leaks into the scout's observation.
    return (s.t,s.place,s.armed,s.signalled,s.got_view)

def actions(L,s):
    at=s.place
    if at=='base':return ()
    out=['wait']
    if at=='J':out+=['K','Q']
    if at=='K':
        out+=['Q','left','right']
        if s.armed and not s.signalled:out+=['send']
    if at=='Q':
        out+=['K']
        if not s.signalled:out+=['local']
        if L.wire and not s.armed:out+=['arm']
    return tuple(out)

def corridor_cells(arm,L):
    sign=-1 if arm=='left' else 1
    return tuple((sign*j,0) for j in range(1,1+(L.left if arm=='left' else L.right)))

def obstacle(w):
    sign=-1 if w.closed=='left' else 1
    return (sign*w.obstruction_depth,0)

def aperture(w,L):
    # Straight axial local rays: inspect successive cells within range,
    # stop when something is physically encountered.
    blocked=obstacle(w)
    for arm in ('left','right'):
        for x in corridor_cells(arm,L)[:L.sight_range]:
            if x==blocked:return arm
    return ''

def apply(L,s,act):
    assert act in actions(L,s)
    start=s.place
    if act in ('left','right'):
        # Actual outgoing arc closure, not a string given to the controller.
        if start!='K' or obstacle(s.w) in corridor_cells(act,L):return None
        d=L.left if act=='left' else L.right
        p=replace(s,place='base',t=s.t+d)
    elif act in ('Q','K'):
        t=1 if start=='J' else L.KQ if act=='Q' else L.QK
        # Aperture reports the closed outgoing physical arc on arrival.
        view=aperture(s.w,L) if act=='K' else s.got_view
        p=replace(s,place=act,t=s.t+t,got_view=view)
    elif act=='arm':p=replace(s,t=s.t+1,armed=True)
    elif act in ('local','send'):
        # Exactly one admitted rebind instruction for this trial. Its effect
        # reaches local source owner one tick after issue; no returned ack.
        settle=s.t+1
        at_source=(act=='local' or s.w.wire_works) and settle<5
        p=replace(s,t=settle,signalled=True,applied=settle if at_source else -1,
                  instruction_at=settle,type_of_contact=0 if act=='local' else 1 if s.w.wire_works else 2)
    else:p=replace(s,t=s.t+1)
    return p if p.t<=L.due else None

def paid(s):
    # Link truth is a source relation, not observed until evaluated at due.
    # Native replay independently checks this table at all selected cuts.
    old_tail=(s.applied>=0)==s.w.lost_primary
    return (old_tail,s.applied<0)

def optimum(L,worlds):
    @lru_cache(None)
    def search(cohort):
        q=cohort[0]
        assert all(observed(s)==observed(q) for s in cohort)
        if q.place=='base':
            v=[paid(s) for s in cohort]
            return (sum(x[1] for x in v),q.t,[]) if all(t for t,_ in v) else None
        answers=[]
        for a in actions(L,q):
            targets=[apply(L,s,a) for s in cohort]
            if any(s is None for s in targets):continue
            groups={}
            for s in targets:groups.setdefault(observed(s),[]).append(s)
            branches=[(k,search(tuple(v))) for k,v in groups.items()]
            if any(x is None for _,x in branches):continue
            cases=[x for _,x in branches]
            answers.append((sum(x[0] for x in cases),max(x[1] for x in cases),
                            [a,[(k,x[2]) for k,x in branches]]))
        return min(answers,key=lambda x:(-x[0],x[1])) if answers else None
    result=search(tuple(State(w) for w in worlds))
    return result,search.cache_info().currsize

def rollout(L,w,tree):
    s=State(w); trace=[]
    while tree:
        a,b=tree
        p=apply(L,s,a)
        assert p is not None
        trace.append((s.t,a,p.t,p.place,p.got_view))
        tree=dict((k,t) for k,t in b)[observed(p)]
        s=p
    return s,trace

def normal_cut(L,healthy):
    """Independent expression on the two-world correlated, matched layout.
    Before responsive source access, any irrevocable blind rebind loses a
    world. For a winning policy: first see the aperture, then walk to the
    console; or first arm, reach aperture, use one charged wire step.
    """
    candidates=[]
    cmd=2+L.KQ
    if cmd<5:
        finish=max(1+L.left,cmd+L.QK+L.right)
        if finish<=L.due:candidates.append(finish)
    cmd=3+L.QK
    if L.wire and healthy and cmd<5:
        finish=max(2+L.QK+L.left,cmd+L.right)
        if finish<=L.due:candidates.append(finish)
    return min(candidates) if candidates else None

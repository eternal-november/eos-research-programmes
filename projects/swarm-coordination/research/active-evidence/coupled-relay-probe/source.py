"""A two-report inspection sortie with a real shared forwarding reserve.
Truth, observable evidence, physical copies and egress are distinct.
"""
from dataclasses import dataclass
from itertools import product
from functools import cache

J,P,Q1,Q,L,R,BASE=range(7)
WAIT,PROBE,FORWARD=-1,-2,-3
EDGES={(J,P),(J,Q1),(Q1,Q),(J,L),(J,R),(L,BASE),(R,BASE)}
COPIES=(frozenset({0,1}),frozenset({1,2}))
@dataclass(frozen=True)
class World:
    blocked:int
    failed:int
    q_open:bool=True
    p_aux:bool=False
    contact:bool=False
    q_reports_fault:bool=True
    probe_disturbance:bool=False
    release_feed_on_departure:bool=False

@dataclass(frozen=True)
class State:
    pos:int=J
    read:int=0         # 0 none, 1 contact, 2 P read, 3 Q read; value source-based
    held:int=-1        # relay whose feeding circuit is diverted until mission end
    delivered:bool=False

def phase0(w):
    # Two local inspections, then a local wired write while the source can
    # physically reach the depot, before the remote partition. No output
    # counts as delivered to base at this stage.
    inspections=(True,True)
    durable=tuple(c for c,bit in zip(COPIES,inspections) if bit)
    assert durable==COPIES
    return State(read=int(w.contact)),durable

@cache
def adj(w,p):
    bad={(w.blocked,BASE)} if w.blocked in (L,R) else set()
    if not w.q_open:bad.add((Q1,Q))
    candidates={b if a==p else a for a,b in EDGES-bad if p in (a,b)}
    # Egress ducts are one-way for this crew; past the choice point
    # they cannot return through the inlet or drive to the opposite duct.
    if p in (L,R):candidates.discard(J)
    return tuple(sorted(candidates))

@cache
def dist_to_base(w,p):
    q=[p];dist={p:0}
    for a in q:
        if a==BASE:return dist[a]
        for z in adj(w,a):
            if z not in dist:dist[z]=dist[a]+1;q.append(z)
    return 10**6

def observe(w,s):
    known_exit=w.blocked if s.read else -1
    known_failed=w.failed if s.read and (s.read!=3 or w.q_reports_fault) else -2
    return (s.pos,adj(w,s.pos),known_exit,known_failed,s.held,s.delivered,s.read)

def radio_schedule(w,s,assignment,durable):
    # This actually forwards appeared copies to base.
    # A channel slot sends at most one report; no simultaneous sharing.
    i,j=assignment
    physical_failed={w.failed}
    # Plant event AFTER local test, before output. A source guarantee with
    # probe_disturbance=False is needed to use its observed current state.
    if w.probe_disturbance and s.read==3:physical_failed.add(1)
    return i!=j and i in durable[0] and j in durable[1] and all(
               a not in (physical_failed|{s.held}) for a in assignment)

def options(w,s,t,required_report,cap):
    if s.pos==BASE:return (WAIT,) # egress completes; no later command
    cmds=[WAIT,*adj(w,s.pos)]
    if s.read==0 and s.pos in (P,Q):cmds.append(PROBE)
    # One physical forwarding round can be chosen at or before cut,
    # independent of the egress edge but competes for operator's tick.
    if not s.delivered and t+1<=required_report and s.pos in (J,P,Q):
        cmds.extend((FORWARD,a,b) for a,b in product(range(cap),repeat=2) if a!=b)
    return tuple(cmds)

def effect(w,s,a,t,durable):
    if a==WAIT:return s
    if isinstance(a,tuple):
        if not radio_schedule(w,s,a[1:],durable):return None
        return State(s.pos,s.read,s.held,True)
    if a==PROBE:
        if s.pos==P:
            return State(P,2,-1 if w.p_aux else 1,s.delivered)
        return State(Q,3,-1,s.delivered)
    hold=-1 if w.release_feed_on_departure and s.pos==P else s.held
    return State(a,s.read,hold,s.delivered)

def split(old,z):
    m={}
    return tuple(m.setdefault((p,q),len(m)) for p,q in zip(old,z))

def plan(worlds,D,report_due,trace=False,cap=3,marginal=False):
    pairs=tuple(phase0(w) for w in worlds)
    init=tuple(a for a,_ in pairs);durable=tuple(b for _,b in pairs)
    witness={}
    @cache
    def solve(t,S,C):
        if any(t+dist_to_base(w,s.pos)+int(not s.delivered)>D
               for w,s in zip(worlds,S)):return False
        if any(not s.delivered for s in S) and t>=report_due:return False
        if t==D:return all(s.delivered and s.pos==BASE for s in S)
        tags=split(C,[observe(w,s) for w,s in zip(worlds,S)])
        choices=[set.intersection(*(set(options(w,s,t,report_due,cap))
                 for w,s,g in zip(worlds,S,tags) if g==j)) for j in range(max(tags)+1)]
        def sort(a):
            if isinstance(a,tuple):return (0,a)
            return (1,(a!=PROBE,a==WAIT,a))
        for actions in product(*(sorted(a,key=sort) for a in choices)):
            T=[]
            for w,s,g,stock in zip(worlds,S,tags,durable):
                a=actions[g]
                if marginal and isinstance(a,tuple) and s.held!=-1:
                    # Ablation: independently accepted local behaviors
                    # forget the effect of observation on relay supply.
                    k=effect(w,State(s.pos,s.read,-1,s.delivered),a,t,stock)
                    if k is not None:k=State(k.pos,k.read,s.held,k.delivered)
                else:k=effect(w,s,a,t,stock)
                if k is None:break
                T.append(k)
            if len(T)==len(S) and solve(t+1,tuple(T),tags):
                witness[t,S,C]=(tags,actions,tuple(T))
                return True
        return False
    eq=(0,)*len(worlds)
    if not solve(2,init,eq):return None
    if not trace:return True
    C=eq;S=init
    hist=[() for w in worlds];policy={}
    for t in range(2,D):
        tags,A,T=witness[t,S,C]
        for i,(w,s,g) in enumerate(zip(worlds,S,tags)):
            key=hist[i]+(observe(w,s),)
            assert policy.setdefault(key,A[g])==A[g]
            hist[i]=key+((A[g],),)
        C,S=tags,T
    out=[]
    for w,s,stock in zip(worlds,init,durable):
        h=();row=[]
        for t in range(2,D):
            key=h+(observe(w,s),);a=policy[key]
            assert a in options(w,s,t,report_due,cap)
            z=effect(w,s,a,t,stock)
            row.append((t,s.pos,a,z))
            if z is None:break
            s=z;h=key+((a,),)
        out.append(row)
    return out

def cases():
    joint=(World(L,0),World(R,2))
    tests=[
        ("nominal", (World(-1,-1,contact=True),)),
        ("blocked travel alone", (World(L,-1,contact=True),World(R,-1,contact=True))),
        ("lost contact alone", (World(-1,-1),)),
        ("closure and loss of advisory only", (World(L,-1),World(R,-1))),
        ("closure and radio loss but advisory intact", (World(L,0,contact=True),World(R,2,contact=True))),
        ("joint closure and later radio loss",joint),
        ("severed Q access", (World(L,0,q_open=False),World(R,2,q_open=False))),
        ("P has independent feed", (World(L,0,p_aux=True),World(R,2,p_aux=True))),
        ("factor-only false pass", joint),
        ("probe reports only route, not failure", (World(L,0,q_reports_fault=False),World(L,2,q_reports_fault=False),World(R,0,q_reports_fault=False),World(R,2,q_reports_fault=False))),
        ("post-test relay loss", (World(L,0,probe_disturbance=True),World(R,2,probe_disturbance=True))),
    ]
    for name,W in tests:
        proof=None
        for t in range(4,12):
            res=plan(W,t,t,trace=True,marginal=name.startswith("factor"))
            if res is not None:
                proof=t
                chosen=[[(tk,loc,a) for tk,loc,a,s in row if a==PROBE or isinstance(a,tuple)] for row in res]
                did_finish=all(row[-1][-1] is not None and row[-1][-1].pos==BASE and row[-1][-1].delivered for row in res)
                assert (not did_finish)==name.startswith("factor")
                print(name,"finish",t,"actual valid",did_finish,"probe and forwarding choices",chosen,flush=True)
                break
        if proof is None:print(name,"infeasible through 11",flush=True)
if __name__=="__main__":cases()

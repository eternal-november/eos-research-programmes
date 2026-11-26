"""Actual native load state ABA; by-duty versus by-publisher fencing."""
from pathlib import Path
from hashlib import sha1
from itertools import product
from dataclasses import dataclass
import json,sys
up,flight,named,core=map(lambda p:Path(p).resolve(),sys.argv[1:])
sys.path.insert(0,str(core))
from core import Event,Row,check
sys.path.insert(0,str(flight))
sys.argv=[sys.argv[0],str(up),str(named)]
p=flight/'native.py'
data=p.read_bytes()
assert sha1(f'blob {len(data)}\0'.encode()+data).hexdigest()=='3c8870664b7bd6054cd756a6ffc7c365d8aae0c6'
ns={'__name__':'dependency'}
exec(compile(data,str(p),'exec'),ns)
BAY,T,F,W=[ns[k] for k in ('BAY','T','F','W')]
MODES=('latch','publisher','scoped','monotone-epoch','reset-epoch')
ARRIVAL=(-1,1,3,5,7)

@dataclass(frozen=True)
class Command:
    duty:int
    publisher:str
    epoch:int

OLD=Command(17,'P',41)

def allowed(policy,cmd,current):
    if policy=='publisher':return cmd.publisher!='P'
    if policy=='scoped':return cmd.duty!=OLD.duty
    if policy in ('monotone-epoch','reset-epoch'):return cmd.epoch==current
    if policy=='latch':return True
    raise ValueError(policy)

def run(side,arrival,backup,policy):
    plant,_,_=ns['prefix'](side)
    step,at,agents,shelves=[plant[k] for k in ('step','at','agents','shelves')]
    j=1-side; k=j+2; shelf=shelves[1]
    refuge=(3,1 if j==0 else 5); end=(2,refuge[1])
    def holds():return agents[k].carrying_shelf is shelf
    def view():
        return at(k),str(agents[k].dir),holds(),(shelf.x,shelf.y)
    for op,pos in ns['plan'](at(k),agents[k].dir,[BAY[j],None,refuge],W):
        assert step({k:op})==(0,)*7 and at(k)==pos
    before=view()
    assert before[2]
    # The realized first set-down is always paid; broad fencing of its
    # old publisher occurs later and cannot rewrite this history.
    assert step({k:T,6:F})==(0,0,0,0,0,0,.5)
    assert at(k)==refuge and not holds() and (shelf.x,shelf.y)==refuge
    events=[Event(0,0,paid=('old-fulfilled','side-work'))]
    epoch=41 if policy=='reset-epoch' else 42
    new=Command(18,'Q' if backup else 'P',epoch)
    pickup=4 if backup else 2
    stale_at=None; new_at=None; carried_to=None; recurrence=None
    for t in range(1,8):
        cmds={}
        if t==pickup and not holds() and allowed(policy,new,epoch):cmds[k]=T
        if t==arrival and at(k)==refuge and holds() and allowed(policy,OLD,epoch):
            assert k not in cmds
            cmds[k]=T
            stale_at=t
        if t==6 and holds():cmds[k]=F
        assert step(cmds)==(0,)*7
        if t==pickup and k in cmds:
            assert view()==before
            new_at=t;recurrence=True
        if t==stale_at:
            assert not holds()
            events.append(Event(t,0,paid=('unexpected-old-effect',)))
        if t==6 and k in cmds:
            assert holds() and at(k)==end and (shelf.x,shelf.y)==end
            carried_to=t
            events.append(Event(t,0,paid=('loaded-departure',)))
    ok=check(Row((),frozenset(),tuple(events),{'policy':()}),'policy',1,
             {'old-fulfilled':0,'side-work':0,'loaded-departure':6})
    return dict(recur=bool(recurrence),replayed=stale_at,carry_end=carried_to,
                ok=ok,issuer=new.publisher,epochs=[OLD.epoch,epoch])

def reference(time,backup,policy):
    issued=policy!='publisher' or backup
    later=(4 if backup else 2)<time<6
    stale=issued and later and policy in ('latch','reset-epoch')
    return (time if stale else None,6 if issued and not stale else None)

def reach(graph,start,deleted):
    marks={start}; todo=[start]
    while todo:
        for l,v in graph.get(todo.pop(),()):
            if l not in deleted and v not in marks:
                marks.add(v);todo.append(v)
    return marks

def compile_world(arrival,backup):
    # Independent symbolic reference graph. Following the positive source
    # interpretation, label each optional issuing edge by immutable duty.
    # Deleting publisher P is a different, coarser label map.
    pickup=4 if backup else 2
    def g(t,held,damaged):return (t,held,damaged)
    graph={}
    for t,harmed,held in product(range(1,8),range(2),range(2)):
        src=g(t,held,harmed)
        ed=[]
        if t==pickup and not held:
            ed.append(('new-duty',g(t+1,1,harmed)))
        if t==arrival and t<6 and held:
            ed.append(('old-duty',g(t+1,0,1)))
        # A withheld scheduled action or canceled path advances time. This
        # produces extra cases only in the safety graph, not a service proof.
        ed.append((None,g(t+1,held,harmed)))
        graph[src]=ed
    return graph

def frontier(time,backup,suppress):
    g=compile_world(time,backup)
    seen=reach(g,(1,0,0),suppress)
    bad=any(k[2] for k in seen)
    # Separate deterministic productive policy: allowing the new operation
    # enables due service, but only if no reachable stale effect exists.
    return not bad, 'new-duty' not in suppress

def main():
    out={}
    for k in product(range(2),ARRIVAL,range(2),MODES):
        q=run(*k)
        r,d=reference(*k[1:])
        assert q['replayed']==r and q['carry_end']==d and q['ok']==(d is not None)
        out[k]=q
    extra=0
    # Frozen elimination audit against actual native traces for the one
    # branch distinguished by a forced offered B action. A separate
    # required independent job is preserved even when broader fence fails.
    for t,backup in product(ARRIVAL,range(2)):
        assert frontier(t,backup,{'old-duty'})==(True,True)
        broad={'old-duty'} | ({'new-duty'} if not backup else set())
        assert frontier(t,backup,broad)==(True, bool(backup))
        assert frontier(t,backup,set())[0]==(out[0,t,backup,'latch']['replayed'] is None)
        extra+=3
    correlated={(3,1),(1,0)}
    product_support=set(product({t for t,b in correlated},{b for t,b in correlated}))
    exposed=product_support-correlated
    bad={x for x in product_support if not frontier(*x,set())[0]}
    assert bad=={(3,0)} and bad<=exposed
    for side in range(2):
        assert all(out[(side,*w,'latch')]['ok'] for w in correlated)
        assert not out[side,3,0,'latch']['ok']
        assert all(out[(side,*w,'scoped')]['ok'] for w in correlated|bad)
    point=(0,5,0)
    assert out[point+('latch',)]['recur'] and not out[point+('latch',)]['ok']
    assert out[point+('reset-epoch',)]['replayed']==5
    assert not out[point+('publisher',)]['ok']
    assert out[point+('scoped',)]['ok'] and out[point+('monotone-epoch',)]['ok']
    assert not any(out[k]['replayed'] is not None for k in out if k[1]==7)
    print(json.dumps(dict(native=len(out),frozen_graph_controls=extra,
          selected={m:out[point+(m,)] for m in MODES},
          joint_safe_pairs=sorted(correlated),
          false_product_counterexample=sorted(bad),
          standby_keeps_service=out[0,5,1,'publisher']['ok'],
          after_leaving_no_latch_permission=True),indent=2,sort_keys=True))
if __name__=='__main__':main()

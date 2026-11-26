"""Native RWARE restart on either side of a reversible load toggle."""
from itertools import product
from pathlib import Path
from hashlib import sha1
import json,sys
up,flight,named,core=map(lambda s:Path(s).resolve(),sys.argv[1:])
sys.path.insert(0,str(core))
from core import Event,Row,check
sys.path.insert(0,str(flight))

# The existing verified native prefix sets up the same named two bays and
# live old obligation. Everything after its cut explicitly executes commands.
sys.argv=[sys.argv[0],str(up),str(named)]
source=flight/'native.py'
data=source.read_bytes()
assert sha1(f'blob {len(data)}\0'.encode()+data).hexdigest()=="3c8870664b7bd6054cd756a6ffc7c365d8aae0c6"
src={'__name__':'dependency'}
exec(compile(data,str(source),'exec'),src)
BAY,F,T,L,R,Z,HEAD=[src[k] for k in ('BAY','F','T','L','R','Z','HEAD')]
NAMES=('wait','retry','read','both-guarded','new-guarded','drain-and-read')

def run(side,phase,fault,notice,policy,clear):
    plant,_,storage=src['prefix'](side)
    step,at,agents,shelves=[plant[k] for k in ('step','at','agents','shelves')]
    e=plant['env']
    j=1-side
    carrier=j+2
    refuge=(3,1 if j==0 else 5)
    slot=(2,refuge[1])
    Y=shelves[1]
    def carried():return agents[carrier].carrying_shelf is Y
    def correct_berth():return int(e.grid[1,refuge[1],refuge[0]])==Y.id
    def settled():return at(carrier)==refuge and not carried() and correct_berth()
    poses=lambda:tuple(at(i) for i in range(7))
    def path(points):
        for cmd,pos in src['plan'](at(carrier),agents[carrier].dir,points):
            assert step({carrier:cmd})==(0,)*7 and at(carrier)==pos
    path([BAY[j],None,refuge])
    assert carried() and correct_berth()
    other_before=tuple(at(i) for i in range(7) if i not in (carrier,6))
    # Preinstalled terminal action now has the same pose in both worlds
    # and the same coarse {refuge, ID, absent acknowledgment, halt} view.
    write_count=0
    physical=[]
    def toggle(t):
        nonlocal write_count
        prior=carried()
        assert step({carrier:T})==(0,)*7
        assert carried()!=prior
        assert correct_berth() and at(carrier)==refuge
        physical.append((t,prior,carried()))
        write_count+=1
    if phase==1:toggle(0)      # completed; ACK deliberately absent
    else:assert step({})==(0,)*7
    zero=e._cur_steps
    prior=settled()
    view=(at(carrier),Y.id,None,
          int(prior) if notice else None)
    # independent still-authorized transport during outage in this same plant
    rr=step({6:F})
    assert rr==(0,0,0,0,0,0,.5)
    # Same one-step orientation preparation before the second fault.
    prep=src['plan'](refuge,agents[carrier].dir,[],src['W'])
    assert len(prep)==1 and prep[0][1]==refuge
    assert step({carrier:prep[0][0]})==(0,)*7
    assert e._cur_steps==zero+2

    # Route loss delays exercise of the same actuator by one native tick.
    # An old request still at large can land at tick 5 through a separate
    # old path; it is not removed by the change in publisher.
    force=(policy=='retry' or (policy=='read' and view[3]==0))
    guard=policy in ('both-guarded','new-guarded')
    for t in (3,4):
        if t==(4 if fault else 3) and (force or (guard and carried())):
            toggle(t)
        else:assert step({})==(0,)*7
        assert e._cur_steps==zero+t
    if phase==2 and (policy!='both-guarded' or carried()):
        toggle(5)
    else:assert step({})==(0,)*7
    assert e._cur_steps==zero+5
    # Serial reference closes all old paths after tick 5. It has the same
    # physical state access, but does not use it as an every-writer gate.
    p=settled()
    delay=(policy=='drain-and-read' and not p)
    if delay:
        toggle(6)
        p=settled()
    elif clear and p:
        assert step({carrier:F})==(0,)*7
    else:assert step({})==(0,)*7
    assert e._cur_steps==zero+6
    if delay and clear and p:assert step({carrier:F})==(0,)*7
    else:assert step({})==(0,)*7
    assert e._cur_steps==zero+7
    # Measure robot occupancy of the storage cell separately from storage.
    # A loaded traveller would also need a shelf-layer compatibility check.
    empty=not int(e.grid[0,refuge[1],refuge[0]])
    assert empty==(clear and p)
    cleared_at=(7 if delay else 6) if empty else None
    assert tuple(at(i) for i in range(7) if i not in (carrier,6))==other_before
    assert at(carrier) in (refuge,slot)
    events=[Event(1,0,paid=('independent',))]
    # The completion predicate includes the terminal clearance, not each
    # raw toggle. The safety check below retains all toggles separately.
    if empty and correct_berth():events.append(Event(cleared_at,0,paid=('settle-clear',)))
    for t,old,new in physical:
        if not old and new:events.append(Event(t,1,paid=('forbidden-repickup',)))
    assert len(physical)==write_count
    checked=check(Row((),frozenset(),tuple(events),{'fixed':()}),'fixed',2,
                  {'independent':1,'settle-clear':6})
    return dict(ok=checked,view=list(view),phys=[list(row) for row in physical],
                clear=empty,clear_at=cleared_at,work=rr[6],terminal_setdown=p,
                writer='local-replacement' if fault else 'primary-owner')

def direct(phase,fault,notice,policy,clear):
    paid=phase==1
    records=[[0,1,0]] if paid else []
    if policy=='retry' or (policy=='read' and notice and not paid) or (policy in ('both-guarded','new-guarded') and not paid):
        records.append([4 if fault else 3,int(not paid),int(paid)])
        paid=not paid
    if phase==2 and (not paid or policy!='both-guarded'):
        records.append([5,int(not paid),int(paid)])
        paid=not paid
    delay=(policy=='drain-and-read' and not paid)
    if delay:
        records.append([6,1,0])
        paid=True
    return records,paid,paid and clear and not delay and all(bool(r[1]) for r in records)

def main():
    records={}
    for k in product(range(2),range(3),range(2),range(2),NAMES,range(2)):
        d=run(*k)
        ref,paid,ok=direct(*k[1:])
        assert d['phys']==ref and d['terminal_setdown']==paid and d['ok']==ok, (k,d,ref)
        assert d['work']==.5
        records[k]=d
    take=lambda phase,pol,notice=0,clear=1:records[0,phase,1,notice,pol,clear]
    A,B=take(0,'wait'),take(1,'wait')
    assert A['view']==B['view'] and not A['ok'] and B['ok']
    assert take(0,'retry')['ok'] and not take(1,'retry')['ok']
    assert take(0,'read',1)['ok'] and take(1,'read',1)['ok']
    assert not take(2,'read',1)['ok'] and not take(2,'new-guarded')['ok']
    assert take(2,'both-guarded')['ok'] and not take(2,'both-guarded',0,0)['ok']
    assert all(r['ok'] for k,r in records.items() if k[-2:] == ('both-guarded',1))
    drained=take(0,'drain-and-read')
    assert not drained['ok'] and drained['clear_at']==7
    assert take(0,'both-guarded')['clear_at']==6
    print(json.dumps(dict(native_cases=len(records),copies_same_view=[A,B],
       retry_after_effect=take(1,'retry'),negative_with_old_pending=take(2,'read',1),
       new_gate_not_on_old_path=take(2,'new-guarded'),fully_guarded=take(2,'both-guarded'),
       serial_terminal_fence=drained,
       settlement_without_clearance=take(2,'both-guarded',0,0)),indent=2,sort_keys=True))
if __name__=='__main__':main()

from itertools import product
from pathlib import Path
import importlib.util
import json
import subprocess
import sys
from live import pick_core

up=Path(sys.argv[1])
spec=importlib.util.spec_from_file_location('fixture',up/'isolated.py')
iso=importlib.util.module_from_spec(spec);spec.loader.exec_module(iso)
n=iso.load_native(up/'native_source.py')

class Wire:
    def __init__(self):
        self.p=subprocess.Popen([sys.argv[2]],stdin=subprocess.PIPE,stdout=subprocess.PIPE,
                                text=True,bufsize=1)
    def ask(self,*s):
        self.p.stdin.write(' '.join(map(str,s))+'\n')
        self.p.stdin.flush()
        return self.p.stdout.readline().strip()

def direct(t,cap,need,has_permit,clear,backup,radio):
    x,y,z=radio
    if not (clear and has_permit) or z+need>cap:
        return None
    if x+need<=cap:return 'P'
    if backup and y+need<=cap:return 'Q'
    return None

# The entry labelled "hazard causes return" is the installed fallback policy
# for this authored second fault, not a claimed actuator model for damage.
def shape(name):
    stay,turn,move=[n.Action.NOOP,n.Action.RIGHT,n.Action.FORWARD]
    well=[stay,stay,n.Action.TOGGLE_LOAD,move]
    if name=='hold':return well+[stay]*7
    prior=well+[turn,turn,move]
    if name=='return':return prior+[stay]*4
    return prior+[turn,turn,move,stay]

def simulate(wire,case,policy):
    cap,a,b,fault,backup,lag,due,numbered=case
    assert wire.ask('reset',cap)=='ok'
    grid=iso.make(n,True)
    p,s=grid.agents
    p.dir=n.Direction.RIGHT
    s.x,s.y,s.dir=1,3,n.Direction.RIGHT
    grid._recalc_grid()
    arrived=None;failed=False;unlawful=False
    issued=None;permits=[];other=None;clears=[];epoch=0;raw=[]
    for tick,step in enumerate(shape(fault),1):
        if tick==2 and b:
            # This is a genuinely attempted diagnostic that loses its RF path.
            assert wire.ask('send',tick,'P','probe',b,0)=='0'
            failed=True
        n.step(grid,[step.value,(n.Action.FORWARD if tick==5 else n.Action.NOOP).value])
        clear=(p.x,p.y)==(3,0) and p.carrying_shelf is None
        if clear and (not clears or tick!=clears[-1]+1):
            # The time at which the named true receipt becomes readable.
            epoch+=1
            permits.append((tick+lag,epoch))
        if clear:
            clears.append(tick)
            raw.append((tick,epoch))
        if tick==4:
            other=wire.ask('send',tick,'Side','unrelated',1,1)
        if tick<5 or tick>due or issued is not None:
            continue
        valid_scope=any(r<=tick and (not numbered or g==epoch) for r,g in permits)
        permit=(valid_scope if policy not in ('latched','old-epoch')
                else any(r<=tick for r,_ in permits))
        radio=tuple(map(int,wire.ask('sample',tick).split()))
        fresh=clear
        if policy=='latched':
            fresh=permit  # incorrect: old truthful arrival is not reusable clearance
        exact=pick_core(tick,cap,a,permit,fresh,backup,radio)
        plain=direct(tick,cap,a,permit,fresh,backup,radio)
        assert exact==plain
        if policy=='direct':exact=plain
        if exact:
            assert wire.ask('send',tick,exact,'owed',a,1)=='1'
            issued=(tick,exact)
            unlawful=(not clear or not valid_scope)
            if not unlawful:
                arrived=tick
    assert other=='1' and (s.x,s.y)==(2,3)
    return dict(paid=arrived,issued=issued,unlawful=unlawful,probe_erased=failed,
                clear_ticks=clears,clear_epochs=raw,receipts=permits)

wire=Wire()
run=0
stats={p:{'valid':0,'improper':0,'refused':0} for p in ('fresh','latched','old-epoch')}
w={}
for case in product((4,5,6),(1,3,4),(0,3),('hold','return','re-exit'),(0,1),(0,1,3),(6,7,9,10,11),(0,1)):
    cap,a,b,fault,backup,lag,due,numbered=case
    pos=simulate(wire,case,'fresh')
    baseline=simulate(wire,case,'direct')
    stale=simulate(wire,case,'latched')
    old_epoch=simulate(wire,case,'old-epoch')
    assert pos==baseline and not pos['unlawful']
    # A separate oracle uses reconstructed native clearance and explicit
    # positive physical permissions; radio budget pure prefix is one debit.
    ts=[t for t,g in pos['clear_epochs'] if 5<=t<=due and
        any(r<=t and (not numbered or g==gg) for r,gg in pos['receipts']) and
        (backup or t>6 or a+b<=cap)]
    assert pos['paid']==(min(ts) if ts else None)
    for k,r in [('fresh',pos),('latched',stale),('old-epoch',old_epoch)]:
        stats[k]['valid']+=r['paid'] is not None
        stats[k]['improper']+=r['unlawful']
        stats[k]['refused']+=r['issued'] is None
    if (cap,a,b,fault,lag)==(5,3,3,'re-exit',0) and due in (7,10) and not numbered:
        w[f'{backup}/{due}']={'fresh':pos,'stale':stale}
    if case==(5,3,3,'re-exit',0,3,11,1):
        w['renew-required']={'fresh':pos,'stale-epoch':old_epoch}
    run+=1
wire.p.stdin.close()
assert wire.p.wait()==0
assert w['0/7']['fresh']['issued'] is None and w['0/7']['stale']['unlawful']
assert w['0/10']['fresh']['paid']==10 and w['1/7']['fresh']['paid']==5
assert w['renew-required']['fresh']['issued'] is None
assert w['renew-required']['stale-epoch']['issued']==(10,'P') and w['renew-required']['stale-epoch']['unlawful']
print(json.dumps(dict(installed_cases=run,verdicts=stats,witness=w),sort_keys=True))

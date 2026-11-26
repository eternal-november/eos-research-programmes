import importlib.util
import json
from itertools import product
from pathlib import Path
import subprocess
import sys

up=Path(sys.argv[1])
spec=importlib.util.spec_from_file_location('headless',up/'isolated.py')
iso=importlib.util.module_from_spec(spec)
spec.loader.exec_module(iso)
n=iso.load_native(up/'native_source.py')
cuts={}
for short,delay in product((False,True),repeat=2):
    w=iso.make(n,True)
    a=w.agents[0]
    a.dir=n.Direction.RIGHT if short else n.Direction.UP
    seq=[n.Action.NOOP]*2+[n.Action.TOGGLE_LOAD]
    if not short:
        seq.append(n.Action.RIGHT)
    if delay:
        seq.append(n.Action.NOOP)
    seq.append(n.Action.FORWARD)
    for t,c in enumerate(seq,1):
        n.step(w,[c.value,n.Action.NOOP.value])
        if a.carrying_shelf is None and (a.x,a.y)==(3,0):
            cuts[short,delay]=t
            break
    assert cuts[short,delay]==4+int(not short)+int(delay)

# Qualified arrival has a separately modeled shift and transport delay.
# The consumption arm is not given the local departure clock or offset.
arrivals={2*t-shift+d for t in cuts.values()
          for shift,d in product((0,1,2),(0,2,4))}
arrivals.add(100) # no valid receipt in the horizon (not a measured delay)
plans=[]
expected=[]
preflight=0
for cap,a,b,tx,rx,erase in product((4,5,6),(1,3,4),(1,3,4),range(2),range(2),range(2)):
    # Explicit native-style reference: look for a starting successful
    # attempt in each independent window, not "await all timers".
    prior_tx={'P':[(0,b)]} if tx else {}
    prior_rx={'R1':[(0,b)]} if not erase else {}
    def can(t):
        return (sum(x for u,x in prior_tx.get('P',[]) if u>=t-8)+a<=cap and
                sum(x for u,x in prior_rx.get('R1' if rx else 'R0',[]) if u>=t-8)+a<=cap)
    for due in (8,9,10,12,16):
        possible=[]
        for r in sorted(arrivals):
            for m in (0,1):
                sold=next((k for k in range(r,due+1) if can(k) and (m==0 or k>=9)),-1)
                got=tx or (rx and not erase)
                stop=max(r,9) if (m or (got and a+b>cap)) else r
                assert sold==(stop if stop<=due else -1)
                plans.append((m,cap,a,b,tx,rx,erase,r,due,0,0))
                expected.append((sold,sold,0,0))
                if m==0 and r!=100:
                    possible.append((r,sold))
        for scope in ({6,7,8},{8,9,10},{9,10,11},{12,13,14}):
            valid=all(y>=0 for r,y in possible if r in scope)
            threshold=max(max(scope),9 if (tx or (rx and not erase)) and a+b>cap else 0)
            assert valid==(threshold<=due)
            preflight+=1

serial=0
for cap,a,c,d,rx,due in product((4,5,6),(1,3,4),(1,3,4),(1,3,4),range(2),(18,19,20)):
    # Effect-aligned ordering C before A or D, both C,D due at this cut.
    stale_paid=not rx or a+c<=cap
    early_ok=(not rx or a+c<=cap) and a+d<=cap
    fresh=10 if early_ok else 19 if due>=19 else -1
    # Direct decision can try A first or D first, or wait to later tick.
    # Same-cut order allows A first only if it and D both pay.
    direct=[]
    for t in range(10,due+1):
        overlap=t<=18
        if not overlap or ((not rx or a+c<=cap) and a+d<=cap):
            direct.append(t)
    assert fresh==(min(direct) if direct else -1)
    plans.extend([(2,cap,a,0,0,rx,0,10,due,c,d),(3,cap,a,0,0,rx,0,10,due,c,d)])
    expected.extend([(10 if stale_paid else -1,10,int(a+d<=cap),a),
                     (fresh,fresh,1,0 if fresh<0 else a)])
    serial+=1

p=subprocess.run([sys.argv[2]],input=''.join(' '.join(map(str,row))+'\n' for row in plans),
                 check=True,text=True,capture_output=True)
got=[tuple(map(int,v.split())) for v in p.stdout.splitlines()]
assert len(got)==len(expected)
assert all(a==b for a,b in zip(got,expected))
stats={m:dict(runs=0,paid=0,failed_attempt=0,side_paid=0) for m in range(4)}
examples={}
for plan,(paid,attempt,side,burn) in zip(plans,got):
    m,cap,a,b,tx,rx,erase,r,due,c,d=plan
    group=stats[m]
    group['runs']+=1
    group['paid']+=paid!=-1
    group['failed_attempt']+=attempt!=-1 and paid==-1
    group['side_paid']+=side
    if cap==5 and a==3 and rx and ((m<2 and b==3 and not tx and erase and r==8 and due==8)
                                  or (m>=2 and c==d==3 and due in (18,19))):
        examples[f'{m}/{due}']=[paid,attempt,side,burn]
print(json.dumps(dict(warehouse_event_cuts=list(cuts.values()),preflight_checks=preflight,
    serial_order_checks=serial,cases=stats,examples=examples),sort_keys=True))

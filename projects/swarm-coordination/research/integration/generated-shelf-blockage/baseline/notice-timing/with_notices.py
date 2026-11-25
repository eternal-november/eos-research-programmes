"""Instrument the pinned MRWS #412 wrapper without changing the native plant files."""
from hashlib import sha256
from itertools import product
from pathlib import Path
import json, sys

def instrument(src):
    def sub(old,new):
        nonlocal src
        assert src.count(old)==1,old
        src=src.replace(old,new)
    sub('def run(seed,arm,lag,off_shelf):','def run(seed,arm,lag,off_shelf,delays):')
    sub('    old=s.reassign_orders_if_faulted','    observed=set(); due={}; notices=[]; assignments=[]\n    old=s.reassign_orders_if_faulted')
    sub('    s.reassign_orders_if_faulted=reassign','''    s.reassign_orders_if_faulted=reassign
    schedule=s.schedule
    def dispatch(step):
        # Source-visible status only inside the commissioner's synchronous call.
        cut=w.get_total_steps()
        for a,t in tuple(due.items()):
            if t==cut:
                observed.add(a);pending.add(a);notices.append((cut,a));del due[a]
        exact={a:r.battery_faulted_critical for a,r in w._robots.items()}
        for a,r in w._robots.items():r.battery_faulted_critical=a in observed
        try:return schedule(step)
        finally:
            for a,r in w._robots.items():r.battery_faulted_critical=exact[a]
    s.schedule=dispatch''')
    sub('                pending.add(a)','''                delay=delays[0 if a==first[1] else 1]
                if delay is not None: due[a]=w.get_total_steps()+delay''')
    sub('        try:w.step()','''        try:
            w.step()
            if t in due.values():s.schedule(t)''')
    sub("        pos=[r.get_position()",'''        now=tuple(sorted(s._robot_to_order))
        if not assignments or assignments[-1][1]!=now:assignments.append((t,now))
        pos=[r.get_position()''')
    sub("    return dict(seed=seed,arm=arm","    return dict(notice_delays=delays,notices=notices,assigned_trace=assignments,seed=seed,arm=arm")
    env={'__name__':'mrws_instrumented'}
    exec(compile(src,'pinned_base_with_notice_hooks.py','exec'),env)
    return env['run']

def verify(base):
    run=instrument(base.read_text())
    shifts=(0,1,2,4,None)
    config=[(a,None,(u,0)) for a,u in product(('discard','retain'),shifts)]
    config += [(a,b,(u,v)) for a,b,u,v in product(('discard','retain'),(1,4),shifts,shifts)]
    config += [('clean',None,(0,0))]
    rows=[]
    for a,b,ds in config:
        r=run(0,a,b,True,ds)
        assert r['first']==(19,'robot0') if a!='clean' else r['first'] is None
        assert r['second']==(19+b,'robot1') if b is not None else r['second'] is None
        actual=[(t,x['objName']) for t,x in r['events'] if x['command']=='ROBOTFAULT']
        expected=[(t+d,x) for (t,x),d in zip(actual,ds) if d is not None]
        assert sorted(r['notices'])==sorted(expected)
        assert not any(x['command']=='MOVEROBOT' and x['objName']==robot and tick>=t
                       for t,robot in actual for tick,x in r['events'])
        assert not any(x['command']=='ITEMGAINED' and x['objName']=='robot3' and
                       not any(n<=t for n,_ in r['notices']) for t,x in r['events'])
        rows.append(r)
    return rows
if __name__=='__main__':
    base=Path(sys.argv[1])
    rows=verify(base)
    Path(sys.argv[2]).write_text(json.dumps(rows,sort_keys=True,separators=(',',':'))+'\n')
    for a,b in product(('discard','retain'),(None,1,4)):
        print(a,b)
        for u in (0,1,2,4,None):
            print(u,[(r['notice_delays'][1],r['finish'],r['result']) for r in rows
               if (r['arm'],r['lag'],r['notice_delays'][0])==(a,b,u)])

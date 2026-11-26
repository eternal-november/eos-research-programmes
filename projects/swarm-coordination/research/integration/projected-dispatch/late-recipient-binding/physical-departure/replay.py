"""Build the trace support from native plant histories before early admission."""
from pathlib import Path
from itertools import product
import importlib.util
import json
import subprocess
import sys

def module(path):
    spec=importlib.util.spec_from_file_location('plant_fixture',path)
    src=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(src)
    return src

def produce(iso,n,short,stutter,gate):
    # Q's movement at tick 4 is independent of the first carrier's unload.
    w=iso.make(n,True)
    a,b=w.agents
    a.dir=n.Direction.RIGHT if short else n.Direction.UP
    b.x,b.y,b.dir=1,3,n.Direction.RIGHT
    w._recalc_grid()
    word=[n.Action.NOOP]*2+[n.Action.TOGGLE_LOAD]
    if not short:
        word.append(n.Action.RIGHT)
    if stutter:
        word.append(n.Action.NOOP)
    word.append(n.Action.FORWARD)
    rows=[]
    for t,cmd in enumerate(word,1):
        cmd2=n.Action.FORWARD if t==4 else n.Action.NOOP
        n.step(w,[cmd.value,cmd2.value])
        rows.append((t,(a.x,a.y),a.carrying_shelf is None,(b.x,b.y)))
    drop=next(t for t,_,unloaded,_ in rows if unloaded)
    clear=next(t for t,pos,unloaded,_ in rows if unloaded and pos==(3,0))
    assert rows[3][-1]==(2,3)
    assert rows[drop-1][1]==(2,0) and clear>drop
    return (drop,clear,rows,clear if gate=='departure' else drop)

def verify_no_shortcut(iso,n,short):
    options=[n.Action.NOOP,n.Action.LEFT,n.Action.RIGHT,n.Action.FORWARD]
    checks=0
    reached=[]
    for length in (0,1,2):
        for tail in product(options,repeat=length):
            w=iso.make(n,True)
            a=w.agents[0]
            a.dir=n.Direction.RIGHT if short else n.Direction.UP
            for cmd in [n.Action.NOOP,n.Action.NOOP,n.Action.TOGGLE_LOAD,*tail]:
                n.step(w,[cmd.value,n.Action.NOOP.value])
            if a.carrying_shelf is None and (a.x,a.y)==(3,0):
                reached.append(3+length)
            checks+=1
    assert min(reached)==(4 if short else 5)
    return checks

def support(plant,gate,skew):
    # This one body admits two different fault trajectories. Qualification is
    # only from the exact installed gate, tape family and candidate tick map.
    result=set()
    for drop,clear,rows,_ in plant:
        result.add((False,drop*2-skew))
        result.add((True,(clear if gate=='departure' else drop)*2-skew))
    return sorted(result)

def permitted(S,a,b,cap,shared,method):
    if method=='late':
        return False
    if method=='snapshot':
        S=[(False,t) for _,t in S]
    if method=='marginal':
        S=list(product({x for x,_ in S},{t for _,t in S}))
    return all(not (rx or shared) or t>8 or a+b<=cap for rx,t in S)

iso=module(Path(sys.argv[1])/'isolated.py')
n=iso.load_native(Path(sys.argv[1])/'native_source.py')
shape_comparisons=sum(verify_no_shortcut(iso,n,s) for s in (False,True))
runs=[]
notes=[]
def direct(S,a,b,cap,shared):
    feasible=[]
    for now in (False,True):
        valid=True
        for alias,t in S:
            A=('P','R1' if alias else 'R0',a,t)
            B=('P' if shared else 'Q','R1',b,0 if now else t+10)
            tx={};rx={}
            for x,y,item,cut in sorted((A,B),key=lambda entry:entry[3]):
                for key,L in ((x,tx),(y,rx)):
                    if item+sum(s for t0,s in L.get(key,[]) if t0>=cut-8)>cap:
                        valid=False
                    L.setdefault(key,[]).append((cut,item))
        if valid:
            feasible.append(now)
    assert feasible
    return max(feasible)

witness_long=[produce(iso,n,False,j,'departure') for j in (False,True)]
for short in (False,True):
    predictions=[produce(iso,n,short,j,'departure') for j in (False,True)]
    for skew in (0,1,2):
        for gate in ('departure','unload'):
            S=support(predictions,gate,skew)
            actual=[produce(iso,n,short,j,gate) for j in (False,True)]
            for cap,a,b,shared in product((4,5,6),range(1,5),range(1,5),(False,True)):
                assert permitted(S,a,b,cap,shared,'joint')==direct(S,a,b,cap,shared)
                for stutter,trace in enumerate(actual):
                    for alias,t in support([trace],gate,skew):
                        for method in ('late','snapshot','marginal','joint','stale-proof','stale-heading'):
                            X=(support(predictions,'departure',skew) if method=='stale-proof'
                               else support(witness_long,gate,skew) if method=='stale-heading'
                               else S)
                            early=permitted(X,a,b,cap,shared,method)
                            passed=not early or a+b<=cap or (not alias and not shared) or t>8
                            runs.append((cap,a,b,int(alias),t,int(early),int(shared)))
                            notes.append((method,passed,early,short,gate,skew,S,t,int(alias),cap,a,b,shared,stutter))
proc=subprocess.run([sys.argv[2]],input=''.join(' '.join(map(str,v))+'\n' for v in runs),
                    text=True,capture_output=True,check=True)
ls=proc.stdout.splitlines()
assert len(ls)==len(runs)
stats={}
special={}
for line,(method,expected,early,short,gate,skew,S,t,alias,cap,a,b,share,stutter) in zip(ls,notes):
    native=tuple(map(int,line.split()))
    assert native==(expected,1,1)
    if method in ('late','marginal','joint'):
        assert expected
    d=stats.setdefault(method,dict(scenarios=0,chosen_early=0,old_lost=0))
    d['scenarios']+=1
    d['chosen_early']+=early
    d['old_lost']+=not expected
    if (cap,a,b,share)==(5,3,3,False) and alias and not stutter:
        k=f'{int(short)}/{gate}/{skew}/{t}'
        special.setdefault(k,{})[method]=[int(early),int(expected)]
print(json.dumps(dict(role_and_motion_prefix_checks=shape_comparisons,
                      operations=stats,selected= special),sort_keys=True))

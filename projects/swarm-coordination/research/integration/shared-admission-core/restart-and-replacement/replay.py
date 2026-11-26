"""One joined native packet/terminal-application history per policy and case."""
from itertools import product
import json,subprocess,sys
from pathlib import Path
if sys.argv[1]!="child":
    wire,common=sys.argv[1:]
    sys.path.insert(0,common)
    from core import Event,Row,check

def decide(label,view):
    # Only handed the stable intent and a fresh read (or lack thereof).
    # Neither diagnosis of old effect nor future supplier fault is passed.
    assert set(view)=={"intent","prior_receipt","terminal_read"}
    assert view["intent"]==7 and view["prior_receipt"] is None
    mode={"wait":0,"local":1,"qualified":2,"gate":3,"timer":4}[label]
    keep=mode in (1,3,4) or (mode==2 and view["terminal_read"]==0)
    return mode,int(keep)

def reference(p):
    old,qfail,notice,gate,prep,policy=p
    view=(old==1) if notice==1 else -1
    keep=policy in (1,3,4) or (policy==2 and view==0)
    cue=keep and policy!=4
    heard=cue and qfail==1
    backup=keep and (policy==4 or heard)
    effects=([1] if old==1 else [])+([4] if keep and not qfail else [])+([6] if old==2 else [])+([6 if prep else 8] if backup else [])
    copies=len(effects)
    if gate:effects=effects[:1]
    paid=effects+[-1]*(3-len(effects))
    return (int(view),int(keep),len(effects),paid[0],copies,1,0,int(keep),
            int(keep and (prep or backup)),int(notice>0),
            3+int(notice>0)+2*keep+int(keep and (prep or backup))+cue+backup,paid[1],paid[2],int(heard))

def admits(raw):
    r=tuple((t,"new-owner",("paid",raw[0])) for t in [2] if raw[0]>=0)
    ev=[Event(3,0,paid=('isolated-work',))]
    for i,t in enumerate((raw[3],raw[11],raw[12]),1):
        if t>=0:ev.append(Event(t,i,paid=('critical-obligation',)))
    row=Row(r,frozenset(),tuple(ev),{'plan':()})
    return check(row,'plan',2,{'isolated-work':3,'critical-obligation':7})

def run():
    cases=tuple(product(range(3),range(3),range(3),range(2),range(2),range(5)))
    stream=''.join(' '.join(map(str,p))+' 0\n' for p in cases)
    data=subprocess.run([wire],input=stream,capture_output=True,text=True,check=True).stdout.splitlines()
    assert len(data)==len(cases)
    got={p:tuple(map(int,z.split())) for p,z in zip(cases,data)}
    for p,x in got.items():
        y=reference(p)
        assert x==y,(p,x,y)
        assert admits(x)==(y[2]==1 and y[3]<=7)
    menu={}
    for policies in range(5):
        menu[policies]=[admits(got[old,1,0,0,1,policies]) for old in (0,1)]
    assert all(not all(q) for q in menu.values())
    # With same durable restart view, local reissue misses safety and waiting
    # misses service in opposite worlds. Neither case sees a receipt.
    assert menu[0]==[False,True] and menu[1]==[True,False]
    assert all(got[old,1,0,0,1,p][0]==-1 for old,p in product((0,1),range(5)))
    assert all(admits(got[old,1,1,0,1,2]) for old in (0,1))
    assert all(admits(got[old,1,0,1,1,3]) for old in (0,1))
    assert not admits(got[0,1,0,1,0,3])
    assert not admits(got[0,1,2,0,1,2])
    assert not admits(got[2,1,1,0,1,2])
    assert admits(got[2,1,1,1,1,3])

    assert not admits(got[0,2,0,1,1,3])
    assert admits(got[0,2,0,1,1,4])
    assert all(admits(got[i,j,0,1,1,4]) for i,j in product(range(3),repeat=2))
    assert got[0,0,0,1,1,3][10]==got[0,0,0,1,1,4][10]
    assert got[0,1,0,1,1,3][10]==1+got[0,1,0,1,1,4][10]

    # Actually restart the owner process. Only the application Plant state
    # and the semantic read live in this same running native replay.
    boundary=[]
    for old,q,n,g,p,label in [(0,1,0,0,1,'wait'),(1,1,0,0,1,'local'),
            (0,1,1,0,1,'qualified'),(1,1,1,0,1,'qualified'),
            (0,1,0,1,1,'gate'),(1,1,0,1,1,'gate'),
            (2,1,1,0,1,'qualified'),(2,1,0,1,1,'gate'),
            (0,2,0,1,1,'gate'),(0,2,0,1,1,'timer')]:
        with subprocess.Popen([wire],stdin=subprocess.PIPE,stdout=subprocess.PIPE,text=True) as sim:
            sim.stdin.write(f"{old} {q} {n} {g} {p} 0 1\n");sim.stdin.flush()
            tag,read,receipt=sim.stdout.readline().split()
            assert tag=='restart'
            # New interpreter receives only its declared view, not the oracle.
            spec={'intent':7,'prior_receipt': bool(int(receipt)) or None,
                   'terminal_read':None if read=='-1' else int(read)}
            k=subprocess.run([sys.executable,'-B',str(Path(__file__).resolve()),'child',label],
                input=json.dumps(spec),capture_output=True,text=True,check=True)
            policy,decision=map(int,k.stdout.split())
            assert (policy,decision)==decide(label,spec)
            sim.stdin.write(f"{policy} {decision}\n");sim.stdin.flush()
            x=tuple(map(int,sim.stdout.readline().split()))
            sim.stdin.close()
            assert sim.wait(timeout=5)==0
        assert x==got[old,q,n,g,p,policy]
        boundary.append([old,q,n,g,p,label,x[2],x[3],x[5],x[10]])
    print(json.dumps(dict(native_cases=len(cases),same_view_local_actions=menu,
        actual_process_restart=boundary,
        shared_gate_worst_case_effect_tick=max(got[old,q,0,1,1,3][3]
            for old,q in product(range(3),range(2))),
        timer_covers_erased_local_switch=admits(got[0,2,0,1,1,4]),
        signal_cover_refuses_to_claim_erased_case=not admits(got[0,2,0,1,1,3]),
        no_preparation_fault_effect_tick=got[0,1,0,1,0,3][3],
        gated_old_pending_duplicate_suppressed=got[2,1,0,1,1,3][2]==1,
        fresh_negative_without_terminal_old_unsafe=not admits(got[2,1,1,0,1,2])),
        indent=2,sort_keys=True))
if __name__=='__main__':
    if len(sys.argv)>1 and sys.argv[1]=='child':
        print(*decide(sys.argv[2],json.load(sys.stdin)))
    else:
        run()

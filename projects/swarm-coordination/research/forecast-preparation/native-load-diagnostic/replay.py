"""Same-episode parity learned only in a source-valid loaded diagnostic."""
from collections import Counter
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json
import subprocess
import sys
import isolated as iso

n=iso.load_native(Path(sys.argv[1])/"native_source.py")
A=n.Action
w=subprocess.Popen([sys.argv[2]],stdin=subprocess.PIPE,stdout=subprocess.PIPE,text=True,bufsize=1)
def ask(*args):
    w.stdin.write(" ".join(map(str,args))+"\n")
    w.stdin.flush()
    return w.stdout.readline().strip()

def plant(x,M,loaded):
    g=iso.make(n,loaded)
    at,side=g.agents
    y=2*x
    at.x,at.y,at.dir=1,y,n.Direction.RIGHT
    side.x,side.y,side.dir=0,4,n.Direction.RIGHT
    pallet,load=g.shelfs
    pallet.x,pallet.y=(2,y) if M else (4,0)
    load.x,load.y=(1,y) if loaded else (4,3)
    assert (at.carrying_shelf is load)==loaded
    g._recalc_grid()
    return g

def work(g,loaded):
    at,side=g.agents
    x=at.y//2
    n.step(g,[A.FORWARD.value,A.NOOP.value])
    blocked=(at.x==1)
    target=(3,2*(1-x if blocked else x))
    route=iso.route(n,g,0,target,set())
    assert route is not None and len(route)<=8
    for action in list(route)+[A.NOOP]*(8-len(route)):
        n.step(g,[action.value,A.NOOP.value])
    n.step(g,[A.NOOP.value,A.FORWARD.value])
    assert (side.x,side.y)==(1,4)
    assert (at.x,at.y)==target and (at.carrying_shelf is not None)==loaded
    return at.y//2,len(route)+1

def capture(x,M,mode,erased):
    assert ask("reset")=="ok"
    tape=[]
    def send(t,s,d,p,e=False):
        y,b=ask("send",t,s,d,p,int(not e)).split()
        assert y in ("-",p) and int(b) in (0,len(p))
        tape.append((t,s,d,p,y,int(b)))
        return y
    loaded=mode!="unloaded"
    g=plant(x,M,loaded)
    realx=g.agents[0].y//2
    if loaded:assert send(0,"Q","owed","old")=="old"
    xobs=send(1,"P","owed",f"x{realx}") if mode!="y-only" else "-"
    # Foregoing optional work is an actual absent callback; a merely
    # named bypass does not create receiver headroom.
    extra=send(2,"Side","proof","job!") if mode!="loaded-pair" else "-"
    y,native_steps=work(g,loaded)
    assert ask("side",2)=="1"
    endpoint="proof" if mode in ("loaded-pair","unreserved-pair") else "owed"
    yobs=send(3,"Q",endpoint,f"y{y}",erased and mode=="loaded-pair") if mode!="x-only" else "-"
    assert extra==("-" if mode=="loaded-pair" else "job!")
    assert y==(x^int(M and loaded))
    if mode in ("try-both","unreserved-pair"):assert xobs!="-" and yobs=="-"
    if mode=="loaded-pair":assert (yobs=="-")==erased and xobs!="-"
    if mode=="unloaded":assert xobs!="-" and yobs!="-"
    return ((xobs,yobs),y,extra,native_steps,tape)

# Enumerating independent fair X, a 4-state latent draw, and an independent
# erasure coin realizes each persistent law. The coin is not changed after
# observing the realization. Probability is from the specified model.
experiments={}
modes=("x-only","y-only","try-both","unloaded","unreserved-pair","loaded-pair")
for law,mode,interference in product((0,1),modes,(0,1)):
    hist=Counter();pairlog=Counter();spent=Counter()
    for x,u,coin in product(range(2),range(4),range(2)):
        M=u<(1 if law==0 else 3)
        e=bool(interference and coin)
        obs,y,old,ns,tape=capture(x,M,mode,e)
        hist["/".join(obs)]+=1
        pairlog[f"{x}/{y}"]+=1
        spent.update(total_charged=1+sum(t[-1] for t in tape),side_steps=1,
                     optional_completed=int(old=="job!"),carrier_motion=ns)
        if mode=="loaded-pair":
            # Calibrated observer receives X and an erasure or same-episode Y.
            assert obs[0]==f"x{x}" and (obs[1]==f"y{y}" or e)
    experiments[law,mode,interference]=(hist,pairlog,spent)

for m in modes[:-1]:
    for z in (0,1):
        assert experiments[0,m,z][0]==experiments[1,m,z][0]
for law in (0,1):
    loaded=experiments[law,"loaded-pair",0][1]
    assert sum(n for ab,n in loaded.items() if ab in ("0/1","1/0"))==4+law*8
    unloaded=experiments[law,"unloaded",0][1]
    assert not set(unloaded)&{"0/1","1/0"}

def minimax(z):
    c=[experiments[i,"loaded-pair",z][0] for i in (0,1)]
    obs=sorted(set(c[0])|set(c[1]))
    candidates=[]
    for decisions in product((0,1),repeat=len(obs)):
        errors=[F(sum(c[law][o] for o,a in zip(obs,decisions) if a!=law),16)
                    for law in (0,1)]
        candidates.append(max(errors))
    # Equal-prior direct pointwise likelihood min; use L's fair bit to
    # split erased ties equally when constructing a deterministic policy.
    joint=[sum(min(c[0][o],c[1][o]) for o in obs),32]
    lower=F(*joint)
    result=min(candidates)
    assert result==lower==(F(3,8) if z else F(1,4))
    regret=F(1,2)*result # price of staging the wrong reserve under this law
    return dict(error=str(result),regret=str(regret),single_probe_break_even=str(F(1,4)-regret))
out={f"{l}/{m}/{z}":{"public_transcript":h,"actual_pairs":p,"physical_and_radio":t}
     for (l,m,z),(h,p,t) in experiments.items()}
w.stdin.close()
assert w.wait()==0
print(json.dumps(dict(experiments=out,single_probe=[minimax(z) for z in (0,1)]),sort_keys=True))

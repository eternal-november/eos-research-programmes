"""A committed cave transit with an interior, locally timed native callback."""
import argparse
import json
import subprocess
from itertools import product
from pathlib import Path

PATH=((5,29),(6,29),(6,30),(7,30),(8,30))
OTHER=((8,29),(8,28))
SIDE=((11,34),(11,35))
REPORT="old"   # exact expected payload; 3 bytes.

def topology(path):
    P={(x,y) for x,y,_ in json.loads(Path(path).read_text())["occupied"]}
    def adj(a,b): return a in P and b in P and sum(abs(x-y) for x,y in zip(a,b))==1
    for route in (PATH,OTHER,SIDE):
        assert all(adj(a,b) for a,b in zip(route,route[1:]))
    assert [sum(adj(a,b) for b in P) for a in PATH]==[1,2,2,2,3]
    assert not(set(OTHER)&set(PATH) or set(SIDE)&(set(OTHER)|set(PATH)))

def projected(w, deadlines, capacity, background, mode, delay=0):
    d,lo,hi=w; D,E=deadlines
    off=d if mode=="interior" else d+3
    low=max(0,lo-off)
    if background+len(REPORT)>capacity: low=max(low,5-off)
    if len(REPORT)>capacity: return set()
    high=min(hi-1-off,D-off-delay,E-d-3)
    return set(range(low,high+1))

def step(s,w,deadlines,cap,bg,mode,delay=0):
    d,lo,hi=w;D,E=deadlines
    trail=[]
    t=s
    for duration, p in zip((d,1,1,1),PATH[1:]):
        t+=duration
        trail.append((t,p))
    send=trail[0 if mode=="interior" else -1][0]
    live=bg if send<=4 else 0
    safe_send=(lo<=send<hi and live+len(REPORT)<=cap)
    receipt=send+delay if safe_send else None
    return dict(trail=trail,send=send,path=lo<=send<hi,
                receipt=receipt,egress=t,reachable=receipt is not None
                and receipt<=D and t<=E)

class Wire:
    def __init__(self, path):
        self.p=subprocess.Popen([path],text=True,stdin=subprocess.PIPE,stdout=subprocess.PIPE)
    def __enter__(self):return self
    def __exit__(self,*exc):
        self.p.stdin.close()
        if self.p.wait(timeout=10)!=0:raise RuntimeError("native dispatch failed")
    def cmd(self,*p):
        self.p.stdin.write(" ".join(map(str,p))+"\n");self.p.stdin.flush()
        v=self.p.stdout.readline().strip()
        if not v:raise RuntimeError("missing native response")
        return v

def native(wire,s,w,deadlines,cap,bg,mode):
    x=step(s,w,deadlines,cap,bg,mode)
    assert wire.cmd("reset",cap)=="ok"
    if bg:
        assert wire.cmd("send",0,"P","extra","a"*bg,0)==f"- {bg}"
    assert wire.cmd("side",1)=="1"
    position=x["trail"][0 if mode=="interior" else -1][1]
    assert wire.cmd("pose",100*position[0]+position[1])=="ok"
    got,debit=wire.cmd("send",x["send"],"P","proof",REPORT,int(x["path"])).split()
    # Callback is observed at native dispatch, not inferred from link status.
    expected_receipt=x["receipt"] is not None
    accepted_debit=(0 if (bg if x["send"]<=4 else 0)+len(REPORT)>cap
                     else len(REPORT))
    assert (got==REPORT)==expected_receipt and int(debit)==accepted_debit
    if got!=REPORT: assert got=="-"
    D,E=deadlines
    # Receiver uses only its matching callback and local deadline latch.
    old_accepted=got==REPORT and x["send"]<=D
    local_move=(D+1,OTHER[1]) if old_accepted else None
    side_move=(2,SIDE[1])
    return dict(**x,receiver_move=local_move,source_debit=int(debit),side_move=side_move)

def suite(native_path):
    # Pairing matters although the duration, contact and egress marginals match.
    aligned=((1,1,2),(2,2,3))
    crossed=((1,2,3),(2,1,2))
    assert set.intersection(*(projected(w,(2,5),6,0,"interior") for w in aligned))=={0}
    assert not set.intersection(*(projected(w,(2,5),6,0,"interior") for w in crossed))
    assert not set.intersection(*(projected(w,(2,5),6,0,"exit") for w in aligned))
    # A late callback can invalidate receipt but not the egress trajectory.
    assert not set.intersection(*(projected(w,(2,5),6,0,"interior",1) for w in aligned))
    comparisons=0
    for d,lo,width,D,E,cap,bg,mode,delay in product(
        range(1,4),range(9),range(1,4),range(1,10),range(3,11),
        (2,3,6),range(4),("interior","exit"),(0,1)):
        if bg>cap:continue
        w=(d,lo,lo+width)
        predicted=projected(w,(D,E),cap,bg,mode,delay)
        explicit={s for s in range(E+1)
                  if step(s,w,(D,E),cap,bg,mode,delay)["reachable"]}
        assert predicted==explicit
        comparisons+=E+1
    rows={}
    with Wire(native_path) as wire:
        for key,W,mode in (("aligned",aligned,"interior"),
                           ("crossed",crossed,"interior"),("exit_only",aligned,"exit")):
            rows[key]=[native(wire,0,w,(2,5),6,0,mode) for w in W]
        for key,s in (("debit_at_boundary",3),("debit_expired",4)):
            rows[key]=native(wire,s,(1,4,6),(5,8),5,3,"interior")
        assert rows["debit_at_boundary"]["receipt"] is None
        assert rows["debit_expired"]["receipt"]==5
        n=0
        for d,lo,width,s,cap,bg,mode in product((1,2),range(1,5),range(1,3),
                range(4),(3,5,6),range(4),("interior","exit")):
            w=(d,lo,lo+width);D,E=4,8
            r=native(wire,s,w,(D,E),cap,bg,mode)
            assert (r["receiver_move"] is not None and r["egress"]<=E)==(
                    s in projected(w,(D,E),cap,bg,mode))
            n+=1
    rows.update(exact_start_queries=comparisons,native_cases=n)
    return rows

if __name__=="__main__":
    args=argparse.ArgumentParser()
    args.add_argument("topology");args.add_argument("wire")
    a=args.parse_args()
    topology(a.topology)
    print(json.dumps(suite(a.wire),sort_keys=True,indent=2))

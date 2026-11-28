#!/usr/bin/env python3
"""Assemble a finite radio and keyed-journal transducer on one event order."""
from dataclasses import dataclass, replace
from itertools import product
from pathlib import Path
import hashlib
import json
import sys

HERE=Path(__file__).resolve().parent
dep=(HERE/"prior_event_support.py").read_bytes()
assert hashlib.sha1(f"blob {len(dep)}\0".encode()+dep).hexdigest()=="3770cbcea0cc00fdf195785d74f51a3d707c555d"
from prior_event_support import Event, generate

def active(bank,t):
    return tuple((u,w) for u,w in bank if t-16<=u)

def total(bank,t):
    return sum(w for _,w in active(bank,t))

@dataclass(frozen=True)
class Radio:
    d: tuple=() # received at dock
    q: tuple=() # received at collector
    it: tuple=()
    dt: tuple=()
    qt: tuple=()
    link: bool=True

    def send(self,t,src,dst,size,cap):
        tx=active(getattr(self,src),t)
        if sum(w for _,w in tx)+size>cap:
            return self,False
        self=replace(self,**{src:tx+((t,size),)})
        if src=="dt" and not self.link:
            return self,False
        rx=active(getattr(self,dst),t)
        if sum(w for _,w in rx)+size>cap:
            return self,False
        return replace(self,**{dst:rx+((t,size),)}),True

@dataclass(frozen=True)
class Journal:
    record: int=0

    def arrival(self,v):
        assert not self.record and v in (1,2)
        return Journal(v)

    def reopen(self):
        # Reference path genuinely closes/reopens SQLite. This semantic
        # replacement deliberately does not touch the radio component.
        return Journal(self.record)

@dataclass(frozen=True)
class Episode:
    radio: Radio=Radio()
    journal: Journal=Journal()
    probe: int=0
    request: bool=False
    reply: int=0
    t: int=0

def step(s,e,cap,spacing,policy,payload):
    t=s.t
    r,j,probe,request,reply=s.radio,s.journal,s.probe,s.request,s.reply
    if e=="F":
        r=replace(r,link=False)
    elif e=="W":
        j=j.reopen()
    elif e=="S":
        r,arrived=r.send(t,"it","d",4,cap)
        if arrived:
            j=j.arrival(payload)
    elif e=="P":
        if policy==0 or (policy==1 and j.record):
            r,ok=r.send(t,"dt","q",1,cap)
            if ok:
                probe=2 if j.record else 1
    elif e=="R":
        r,request=r.send(t,"qt","d",4,cap)
        if request and j.record:
            r,arrived=r.send(t,"dt","q",4,cap)
            if arrived:
                reply=j.record
    else:
        raise ValueError(e)
    obs=[int(bool(j.record)),probe,int(request),reply]
    obs.extend(total(getattr(r,a),t) for a in ("it","d","dt","q","qt"))
    return Episode(r,j,probe,request,reply,t+spacing),"".join(map(str,obs))

def exact_reply(w,cap,spacing,policy):
    ts,tp,tr,tf=(w.index(e)*spacing for e in "SPRF")
    if not ts<tr<tf or cap<4:
        return False
    if tr-ts<=16 and cap<8:
        return False
    probe_live = tp<tr and tr-tp<=16 and (policy==0 or (policy==1 and ts<tp))
    return not probe_live or cap>=5

def main():
    stream=Path(sys.argv[1])
    native={}
    for line in stream.read_text().splitlines():
        cap,spacing,policy,h,w,*o=line.split()
        k=(*map(int,(cap,spacing,policy,h)),w)
        assert len(o)==5 and all(len(s)==9 for s in o) and k not in native
        native[k]=tuple(o)
    seen=set()
    delivered={}
    examined=0
    for cap,spacing,policy,h in product((3,4,5,8,9),(4,5,6),range(3),range(2)):
        alphabet=tuple(Event(e,frozenset(),lambda s,e=e:step(s,e,cap,spacing,policy,1+h))
                    for e in "FPRSW")
        count=0
        for seq in generate(alphabet,Episode()):
            w="".join(e[0] for e in seq)
            k=(cap,spacing,policy,h,w)
            expected=tuple(e[1] for e in seq)
            assert native.get(k)==expected,(k,native.get(k),expected)
            assert k not in seen
            seen.add(k)
            examined+=len(seq)
            delivered_result=seq[-1][2].reply
            assert delivered_result==(1+h if exact_reply(w,cap,spacing,policy) else 0)
            count+=bool(delivered_result)
        delivered[f"{cap}/{spacing}/{policy}/{h}"]=count
    assert seen==native.keys() and len(seen)==10800
    def row(w,p=2,c=4,t=6,h=0):
        return native[c,t,p,h,w]
    # Restart preserves the exact named row, but inserting its time slot
    # changes which debit is still live when the retry reaches the dock.
    assert row("SWPRF")[-1][3]=="1" and row("SPRFW")[-1][3]=="0"
    # With the same physical episode and at the same eligible receive cut,
    # an earlier paid positive probe spends the byte the exact reply needs.
    assert row("SWPRF",0)[2][1]=="2" and row("SWPRF",0)[-1][3]=="0"
    # For spacing four the original is exactly one second old at R and live.
    assert row("SWPFR",2,4,4)[-1][2]=="0"
    # For the full inclusive one-second fixture, S and R each can
    # arrive, but they cannot both fit at a cap-four dock. The quotient
    # that independently joins those two possibilities invents service.
    small=[o[-1] for (c,t,_,_,_),o in native.items() if (c,t)==(4,4)]
    assert {z[0]+z[2] for z in small}=={"10","01"}
    # In the native radio fixture: F blocks outgoing RF, but sender is still charged
    # when R attempts to return the committed result.
    assert row("SWPFR")[4][0:4]=="1010" and row("SWPFR")[4][6]=="4"
    # A pending / old-committed probe is not inferred from the debit count.
    assert row("PSWRF",1,8)[0][1]=="0"
    assert row("PSWRF",0,8)[0][1]=="1"
    print(json.dumps(dict(schedules=len(seen),timed_cuts=examined,exact_replies=delivered),sort_keys=True))

if __name__=="__main__":
    main()

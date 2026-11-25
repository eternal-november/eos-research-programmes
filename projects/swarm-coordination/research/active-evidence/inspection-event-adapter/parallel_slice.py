"""Restricted two-crew event check: local scouting and separate dispatch.

The scout selects a predeclared station with common available access and
acquires a route observation. The dispatcher has a different observation
history and a single optional receipt. Forwarding can overlap actual feed
use. This module deliberately does not implement arbitrary multi-crew
motion, pursuit or network propagation.
"""
from collections import defaultdict
from itertools import product
from mission import Fixture
from checks import seed

def choices(f):
    A=[(a,b) for a in f.slots for b in f.slots
       if a!=b and f.dispatch_reserves((a,b))]
    return tuple(A)

def support(f,i,a,t,d,hold):
    if a is None:return False
    w=f.worlds[i]
    for r,s in zip(f.reports,a):
        if r not in f.slots[s]["stock"] or s in w.get("absent_stock",{}).get(r,[]):return False
        if not all(f.exists_during(i,k,s,t,t+d) for k in ("slots_down","radio_down")):return False
        if not all(f.exists_during(i,"coupled_resources_down",q,t,t+d)
                   for q in f.slots[s].get("needs",[])):return False
        for s1,l,u in hold:
            if s1==s and max(l,t)<min(u,t+d):return False
    return True

def contexts(f,station,relay_evidence,delay,wait=0):
    # Both known access routes are fixed safe at selection already in the
    # base fixture. The planned delay preserves one action in flight.
    outbound=f.arcs["to-"+station]
    home=f.arcs["from-"+station]
    p=f.probes[station]
    start=f.d["start_epoch"]
    probe=start+outbound["dur"]+wait
    sample=probe+p["dur"]
    leave=sample+home["dur"]
    H=f.d["egress_due"]
    C=[]
    for i,w in enumerate(f.worlds):
        if not f.can_visit(i,outbound["id"],start,outbound["dur"]):return None
        if not f.exists_during(i,"probes_down",station,probe,sample):return None
        if not f.can_visit(i,home["id"],sample,home["dur"]):return None
        if any(not f.exists_during(i,"coupled_resources_down",q,probe,sample)
               for q in p.get("needs",[])):return None
        read=f.truth_read(i,station,sample)
        blocked=read[0]
        passage="right" if blocked=="L" else "left"
        terminal="R-base" if blocked=="L" else "L-base"
        if (leave+2>H or not f.can_visit(i,passage,leave,1)
                   or not f.can_visit(i,terminal,leave+1,1)):return None
        # If scoped local cue missing at its real arrival, dispatcher
        # observes nothing. Scout still locally observed the physical route.
        q=sample+delay
        received=relay_evidence and not w.get("crew_cue_missing",False)
        payload=read if received else None
        release=leave if p.get("release_on_departure",False) else H
        hold=tuple((a,probe,release) for a in p.get("divert",[]))
        C.append((i,q if received else H+1,payload,hold,leave+2))
    return C

def compile_policy(f,C):
    B=min(r["deadline"] for r in f.reports.values())
    start=f.d["start_epoch"];d=f.d["round_d"]
    for default in [*range(start,B-d+1),B+1]:
        groups=defaultdict(list);silent=[]
        for i,q,obs,hold,egress in C:
            if q<=default:groups[q,obs].append((i,hold))
            else:silent.append((i,hold))
        if default>B and silent:continue
        alt={}
        for (q,obs),histories in groups.items():
            v=next(((t,a) for t in range(q,B-d+1) for a in choices(f)
                  if all(support(f,i,a,t,d,h) for i,h in histories)),None)
            if v is None:break
            alt[q,obs]=v
        else:
            a=next((a for a in choices(f) if all(support(f,i,a,default,d,h)
                         for i,h in silent)),None) if silent else None
            if silent and a is None:continue
            return (default,a),alt
    return None

def ref(f,C):
    B=min(r["deadline"] for r in f.reports.values())
    d=f.d["round_d"]
    def go(rows,t):
        based=defaultdict(list)
        for i,q,obs,h,x in rows:
            based[(q,obs) if q<=t else ()].append((i,q,obs,h,x))
        return all(any(all(support(f,i,a,t,d,h) for i,q,obs,h,x in group)
           for a in choices(f)) or (t+1<=B-d and go(group,t+1)) for group in based.values())
    return False if B-d<f.d["start_epoch"] else go(C,f.d["start_epoch"])

def run():
    n=0
    for fed,station,delay,ack,B,d in product((False,True),("P","Q"),range(3),
                                            (False,True),range(4,8),range(1,4)):
        f=Fixture(seed(B,10,fed));f.d["round_d"]=d
        C=contexts(f,station,ack,delay)
        p=compile_policy(f,C)
        assert bool(p)==ref(f,C)
        if p:
            for i,q,o,h,x in C:
                t,a=p[0] if q>p[0][0] else p[1][q,o]
                assert t+d<=B and support(f,i,a,t,d,h) and x<=10
        n+=1
    print(n,"two-crew timed same-source policy and direct checks")
    f=Fixture(seed(7,10))
    CQ=contexts(f,"Q",True,0)
    assert compile_policy(f,CQ) and not compile_policy(f,contexts(f,"Q",False,0))
    # Actual late interference: leave with provided separately controlled
    # relay power, but P turns a shared feed off at tick three.
    CP=contexts(f,"P",True,0)
    assert not compile_policy(f,CP)
    for w in f.worlds:w["slots_down"]={}
    f.exists_during.cache_clear()
    assert support(f,0,("r0","r1"),2,1,CP[0][3])
    assert not support(f,0,("r0","r1"),2,2,CP[0][3])
    print("private scout evidence is not a dispatcher receipt")
    print("a feed usable at dispatch can fail during concurrent scout acquisition")
if __name__=="__main__":run()

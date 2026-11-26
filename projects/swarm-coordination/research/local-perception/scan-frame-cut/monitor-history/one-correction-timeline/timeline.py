#!/usr/bin/env python3
"""Exact joint monitor trace for one correction at an uncertain timestamp."""
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import importlib.util
from random import Random
import json,sys

here=Path(__file__).resolve().parent
def module(name,p):
    spec=importlib.util.spec_from_file_location(name,p)
    m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
    return m
prior=module('prior',here.parent/'replay.py')
evidence=module('evidence',here.parent/'scan-use/corroboration.py')

@dataclass
class Use:
    acquired: int
    seen_at: int
    seq: int
    points: tuple

def coords(es):
    return prior.representatives(sorted(set(es)))

class Online:
    def __init__(self,cut,jump,m,trigger,release,n,init):
        self.ck=sorted(set(cut))
        self.jk=sorted(set(jump))
        self.states={(k,j):(init,(-1,0)) for k,j in product(coords(self.ck),coords(self.jk))}
        self.params=(m,trigger,release,n)
        self.last_use=None
        self.last_seq=-1
    def advance(self,u):
        assert u.acquired<=u.seen_at and isinstance(u.seq,int)
        assert u.seq>=self.last_seq and (self.last_use is None or self.last_use<=u.seen_at)
        self.last_use=u.seen_at
        self.last_seq=u.seq
        ck=sorted(set(self.ck)|{k for k in (u.acquired,u.seen_at) if self.ck[0]<=k<=self.ck[-1]})
        jk=sorted(set(self.jk)|prior.cuts(u.points,self.jk[0],self.jk[-1]))
        def use(c,z):
            hit=prior.count(u.points,z if u.acquired<c<=u.seen_at else 0)>=self.params[0]
            a,b=self.query(c,z)
            return (prior.stamp(a,hit,*self.params[1:3]),
                    evidence.step(b,u.seq,hit,self.params[3]))
        out={(c,z):use(c,z) for c,z in product(coords(ck),coords(jk))}
        self.states,self.ck,self.jk=out,ck,jk
    def query(self,c,z):
        from bisect import bisect_left
        def key(es,p):
            i=bisect_left(es,p)
            if i<len(es) and es[i]==p:return p
            assert 0<i<len(es)
            return F(es[i-1]+es[i],2)
        return self.states[key(self.ck,c),key(self.jk,z)]
    def vals(self):return set(self.states.values())

def direct(uses,cut,jump,m,h,r,n,init):
    # One fixed complete history; no online state/refinement. Native and authored
    # evidence intentionally checked separately against the same list of votes.
    ck=sorted(set(cut)|{v for u in uses for v in (u.acquired,u.seen_at)
             if cut[0]<=v<=cut[-1]})
    jk=sorted(set(jump)|set().union(*(prior.cuts(u.points,*jump) for u in uses)))
    end={}
    for tau,z in product(coords(ck),coords(jk)):
        state=init;votes=[]
        for u in uses:
            yes=prior.count(u.points,z if u.acquired<tau<=u.seen_at else 0)>=m
            state=prior.stamp(state,yes,h,r)
            votes.append((u.seq,yes))
        end[tau,z]=state,evidence.direct(votes,n)[-1]
    return end

def replay():
    low=(( -12,8),)
    higher=((4,8),)
    pairs=(Use(0,2,0,low),Use(2,4,1,low))
    params=((0,4),(14,16),1,2,2,2,(False,0,0))
    q=Online(*params)
    for u in pairs: q.advance(u)
    assert all(not st[0] for st,_ in q.vals())
    assert all(prior.count(u.points,16)==1 and prior.count(u.points,0)==0 for u in pairs)
    overlap=(pairs[0],Use(1,4,1,low))
    q=Online(*params)
    for u in overlap: q.advance(u)
    assert any(st[0] for st,_ in q.vals())
    q=Online((0,4),(14,16),1,2,2,2,(True,0,0))
    for u in pairs: q.advance(Use(u.acquired,u.seen_at,u.seq,higher))
    assert all(st[0] and corroboration[1]<2 for st,corroboration in q.vals())
    q=Online((0,4),(14,16),1,2,2,2,(True,0,0))
    for u in overlap: q.advance(Use(u.acquired,u.seen_at,u.seq,higher))
    assert any(not st[0] and corroboration[1]==2 for st,corroboration in q.vals())

    R=Random(540);compared=points=0
    for _ in range(260):
        cut=tuple(sorted(R.choices(range(12),k=2)))
        jump=tuple(sorted(R.choices(range(-16,18),k=2)))
        args=(cut,jump,*(R.randrange(1,5) for _ in range(4)),(R.choice((False,True)),0,0))
        q=Online(*args)
        uses=[];seq=0;acquired=0
        for t in sorted(R.choices(range(1,13),k=R.randrange(1,9))):
            if R.random()<.6:
                seq+=1
                acquired=R.randrange(acquired,t+1)
            uses.append(Use(acquired,t,seq,tuple((R.randrange(-16,33),R.choice((0,8,16,17)))
                        for _ in range(R.randrange(1,6)))))
            q.advance(uses[-1])
            d=direct(uses,*args)
            assert q.vals()==set(d.values())
            for k,v in d.items():assert q.query(*k)==v
            compared+=1
            points+=len(d)
    return dict(shared_trace_prefix_checks=compared,partition_representative_checks=points,
                adjacent_windows_cannot_share_change=True,overlap_can_restore_trigger_and_release=True)

if __name__=='__main__':
    print(json.dumps(replay(),indent=2,sort_keys=True))

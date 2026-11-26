#!/usr/bin/env python3
"""Invert a scalar bounded-variation envelope for a finite monitor automaton."""
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import importlib.util,json
from random import Random
p=Path(__file__).resolve().parent.parent/'replay.py'
s=importlib.util.spec_from_file_location('hysteresis',p)
hyst=importlib.util.module_from_spec(s);s.loader.exec_module(hyst)

@dataclass(frozen=True,order=True)
class I:
    l: F
    r: F
    lc: bool
    rc: bool
    def nonempty(self):return self.l<self.r or self.l==self.r and self.lc and self.rc
    def close(self):return I(self.l,self.r,True,True)
    def expand(self,d):return I(self.l-d,self.r+d,self.lc,self.rc)
def intersection(a,b):
    l,lc=max((a.l,not a.lc),(b.l,not b.lc));lc=not lc
    r,rc=min((a.r,a.rc),(b.r,b.rc))
    return I(l,r,lc,rc)
def union(terms):
    out=[]
    for i in sorted(set(terms),key=lambda z:(z.l,not z.lc,z.r,z.rc)):
        if not out or out[-1].r<i.l or out[-1].r==i.l and not (out[-1].rc or i.lc):
            out.append(i)
        else:
            j=out[-1]
            r,rc=max((i.r,i.rc),(j.r,j.rc))
            out[-1]=I(j.l,r,j.lc,rc)
    return out

def forward(choices,t,base,start,target,rho,closed=False):
    states={}
    for k,rels in enumerate(choices):
        nxt={}
        for u,v,j in rels:
            if closed:j=j.close()
            if k==0:
                if u==start:nxt.setdefault(v,[]).append(j)
            else:
                for old in states.get(u,[]):
                    val=intersection(old.expand(base[k]-base[k-1]+rho*(t[k]-t[k-1])),j)
                    if val.nonempty():nxt.setdefault(v,[]).append(val)
        states={q:union(x) for q,x in nxt.items()}
    return any(q in states for q in target)

def threshold(choices,t,base,start,target):
    assert len(choices)>0 and len(choices)==len(t)==len(base)
    assert all(b>a for a,b in zip(t,t[1:]))
    assert all(b>=a for a,b in zip(base,base[1:]))
    rates={F(0)}
    for i,ci in enumerate(choices):
        for j in range(i):
            for _,_,a in ci:
                for _,_,b in choices[j]:
                    for e,f in ((a.l,b.r),(b.l,a.r)):
                        rates.add(max(F(0),F(e-f-(base[i]-base[j]),t[i]-t[j])))
    rates=sorted(rates)
    if not forward(choices,t,base,start,target,rates[-1],True):return None
    a,b=0,len(rates)-1
    while a<b:
        m=(a+b)//2
        if forward(choices,t,base,start,target,rates[m],True):b=m
        else:a=m+1
    q=rates[a]
    return q,forward(choices,t,base,start,target,q)

def direct(choices,t,base,start,target):
    answer=None
    for word in product(*choices):
        if word[0][0]!=start or word[-1][1] not in target:continue
        if any(a[1]!=b[0] for a,b in zip(word,word[1:])):continue
        cand=[]
        for i,(_,_,a) in enumerate(word):
            for j,(_,_,b) in enumerate(word):
                if i==j:continue
                rho=F(a.l-b.r-abs(base[i]-base[j]),abs(t[i]-t[j]))
                cand.append((rho,a.lc and b.rc))
        req=max([F(0)]+[q for q,_ in cand])
        attained=all(r<req or cl for r,cl in cand)
        if answer is None or (req,not attained)<(answer[0],not answer[1]):
            answer=(req,attained)
    return answer

def native_shaped():
    # Same native point convention as #538. Units are sixteenths.
    # Build connected components of equal hit cell at each frame, then lift
    # to transitions of the reachable latch/counter states.
    points=[((-16,8),(-32,8)),((-16,8),),((0,8),(-16,8))]
    support=[0,40]
    init=(True,0,0);active={init};rs=[]
    for ps in points:
        keys=sorted(set(support)|hyst.cuts(ps,*support))
        visible=[]
        for i,z in enumerate(keys):
            if i:
                lo=keys[i-1]
                v=I(lo,z,False,False)
                visible.append((v,hyst.count(ps,F(lo+z,2))>0))
            visible.append((I(z,z,True,True),hyst.count(ps,z)>0))
        choices=[(a,hyst.stamp(a,hit,1,3),v) for a in active for v,hit in visible]
        rs.append(choices);active={q for _,q,_ in choices}
    tgt={q for q in active if not q[0]}
    ans=threshold(rs,[0,1,2],[0,0,0],init,tgt)
    assert ans==direct(rs,[0,1,2],[0,0,0],init,tgt)==(16,False)
    assert not forward(rs,[0,1,2],[0,0,0],init,tgt,16)
    assert forward(rs,[0,1,2],[0,0,0],init,tgt,F(33,2))
    # Every pair of miss cut constraints, checked separately at 3/4.
    misses=[[(0,0,j) for u,v,j in r if v[2]==u[2]+1] for r in rs]
    for i,j in ((0,1),(0,2),(1,2)):
        assert forward([misses[i],misses[j]],[i,j],[0,0],0,{0},12)

def test():
    native_shaped()
    R=Random(541);miss=open_=equal=0
    for _ in range(1500):
        k=R.randrange(1,6)
        t=sorted(R.sample(range(18),k))
        base=sorted(R.choices(range(9),k=k))
        choices=[]
        for i in range(k):
            curr=[]
            for j in range(R.randrange(1,6)):
                a,b=sorted(R.choices(range(-6,7),k=2))
                u,v=R.randrange(3),R.randrange(3)
                seg=I(a,b,R.choice((False,True)),R.choice((False,True)))
                if seg.nonempty():curr.append((u,v,seg))
            choices.append(curr)
        ans=threshold(choices,t,base,0,{1,2})
        assert ans==direct(choices,t,base,0,{1,2})
        if ans is None:miss+=1
        elif ans[1]:equal+=1
        else:
            open_+=1
            assert forward(choices,t,base,0,{1,2},ans[0]+F(1,10000))
    return dict(native_three_frame_rate_infimum=1,native_attained=False,
                independent_acceptance_comparisons=1500,
                no_path=miss,attained=equal,strict=open_)
if __name__=='__main__':
    print(json.dumps(test(),indent=2,sort_keys=True))

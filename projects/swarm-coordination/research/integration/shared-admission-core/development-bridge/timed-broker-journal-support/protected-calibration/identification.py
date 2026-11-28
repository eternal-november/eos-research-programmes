#!/usr/bin/env python3
"""Verify the native calibration arms and compute sharp selection bounds."""
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import product
from pathlib import Path
import json

H=Path(__file__).resolve().parent

def observe(row, arm):
    u,v,a,h,_,late,req,reply,at_q,at_t,early,charged=row
    if arm in (1,4): # protected, with absent or current-read tag
        return (u,reply,at_t)
    if arm==6: # bank-0 age; deliberately no route observation
        return (at_t,)
    if arm in (3,5): # exact reply and a paired historical tag
        return (u,reply,at_t)
    if arm in (7,8):
        return (u,reply,early)
    raise ValueError(arm)

def law_check(native):
    laws=(((0,0),(1,1)),((0,1),(1,0)))
    comparisons=0
    for a,h,late in product(range(2),range(2),(8,9)):
        profiles={}
        for arm in (1,3,4,5,6,7,8):
            pair=tuple(Counter(observe(native[u,v,a,h,arm,late],arm) for u,v in law)
                       for law in laws)
            assert (pair[0]==pair[1])==(arm in (1,4,6))
            comparisons+=1
        for i,law in enumerate(laws):
            assert all(native[u,v,a,h,0,late][7]==(1+h if a==i else 0) for u,v in law)
    return comparisons

def bounds(n,p,q,ell):
    e00,e01,e10,e11 = ell
    return max(e11,e00+p+q-n), min(p-e10,q-e01)

def exact_interval():
    cases=0
    all_actions=0
    for n in range(1,10):
        grouped=defaultdict(set)
        for a in range(n+1):
            for b in range(n-a+1):
                for c in range(n-a-b+1):
                    d=n-a-b-c
                    p,q=c+d,b+d
                    for ell in product(*[range(x+1) for x in (a,b,c,d)]):
                        grouped[p,q,ell].add(d)
        for (p,q,ell),xset in grouped.items():
            lo,hi=bounds(n,p,q,ell)
            assert xset==set(range(lo,hi+1))
            l=Fraction(n-p-q+2*lo,n)
            h=Fraction(n-p-q+2*hi,n)
            candidates=(Fraction(0),Fraction(1,2),Fraction(1))
            sure=lambda w:min(w*t+(1-w)*(1-t) for t in (l,h))
            assert max(map(sure,candidates))==max(1-h,l,Fraction(1,2))
            cases+=1
            all_actions+=len(candidates)
    return cases,all_actions

def main():
    native={}
    for ln in (H/"NATIVE.txt").read_text().splitlines():
        row=tuple(map(int,ln.split()))
        u,v,a,h,mode,late,req,reply,q,t,early,charged=row
        k=row[:6]
        assert len(row)==12 and k not in native
        native[k]=row
        e=int(u==v^a)
        good=1+h
        expected=(
            (e,e*good,-1,-1,0),
            (1,good,-1,-1,0),
            (1,0,e,-1,0),
            (1,good,-1,e,0),
            (1,good,-1,1,0),
            (1,good,-1,1-e,0),
            (0,0,-1,int((v^a)==0),0),
            (e,e*good,-1,-1,e*good),
            (1,good,-1,-1,e*good)
        )[mode]
        assert row[6:-1]==expected,(row,expected)
        assert charged==(4+4*e,8,9,9,9,9,1,4+4*e,12-4*e)[mode]
        if mode==3:
            estimate=(u^a) if t else (1^u^a)
            assert estimate==v
        if mode==5:
            estimate=(u^a) if t else (1^u^a)
            assert estimate!=v
    assert len(native)==288
    counterfamilies=law_check(native)
    cells,policies=exact_interval()
    print(json.dumps(dict(native=len(native),same_law_control_checks=counterfamilies,
                          sharp_count_classes=cells,robust_candidate_checks=policies,
                          known_law_service=1,unknown_law_robust_service="1/2"),sort_keys=True))

if __name__=="__main__":
    main()

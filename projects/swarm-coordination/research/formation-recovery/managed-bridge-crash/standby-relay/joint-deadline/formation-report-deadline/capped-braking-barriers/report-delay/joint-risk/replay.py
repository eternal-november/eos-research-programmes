#!/usr/bin/env python3
"""Exact finite checks for mission-risk composition at the braking cutoff."""
from fractions import Fraction as Q
from itertools import product
import json


def allocations(caps,total):
    if not caps:
        if total==0:
            yield ()
        return
    for n in range(max(0,total-sum(caps[1:])),min(caps[0],total)+1):
        for r in allocations(caps[1:],total-n):
            yield (n,)+r


def overlap(mu):
    return sum(min(mu[i],mu[i+1]) for i in range(0,len(mu),2))


def rules(size):
    return list(product((0,1),repeat=size))


def error(weights,rule):
    return sum(weights[2*i+1-b] for i,b in enumerate(rule))


def call_risk(t,law):
    table={}
    for world,mass,events,prior_bad in law:
        h=tuple((tt,s) for tt,s in events if tt<=t)
        a=table.setdefault(h,[Q(0),Q(0)])
        if not prior_bad:
            a[world]+=mass
    return sum(mass for _,mass,_,bad in law if bad)+sum(map(min,table.values()))


def replay():
    games=laws=decoder_checks=0
    for total in range(1,6):
        for ui in allocations((total,)*6,total):
            mu=tuple(2*n for n in ui)
            N=sum(mu)
            e=overlap(mu)
            rs=rules(3)
            for f in range(0,N+1,2):
                all_q=list(allocations(mu,N-f))
                assert all_q
                det=[0]*len(rs)
                bayes_max=0
                for q in all_q:
                    errs=list(map(lambda d:error(q,d),rs))
                    assert min(errs)==overlap(q)
                    decoder_checks+=len(errs)
                    det=[max(d,x) for d,x in zip(det,errs,strict=True)]
                    bayes_max=max(bayes_max,min(errs))
                    laws+=1
                assert f+min(det)==min(N,f+e)
                assert f+bayes_max==f+min(e,(N-f)//2)
                games+=1
    erasure_games=0
    for m in range(1,41):
        for a in range(m+1):
            b=m-a
            for d in range(m+1):
                qa=range(max(0,d-b),min(a,d)+1)
                assert min(max(qa),max(d-x for x in qa))==min(d,a,b)
                # Double the integer law to admit half-unit least-favourable splits.
                aa=range(max(0,2*d-2*b),min(2*a,2*d)+1)
                assert max(min(x,2*d-x) for x in aa)==min(d,2*a,2*b)
                erasure_games+=1
    t=Q(1,4)
    exactly=[(0,Q(1,2),[(t,'A')],False),(1,Q(1,2),[(t,'B')],False)]
    late=[(0,Q(1,2),[(t+Q(1,20),'A')],False),(1,Q(1,2),[(t+Q(1,20),'B')],False)]
    assert call_risk(t,exactly)==0 and call_risk(t,late)==Q(1,2)
    # Equal final error with two different cutoff histories.
    silence=[(0,Q(1,2),[(t,'A')],False),(1,Q(1,2),[(2*t,'B')],False)]
    assert call_risk(t,silence)==0
    concentrated=[(0,Q(1,4),[],True),(0,Q(1,4),[],False),(1,Q(1,2),[],False)]
    independent=list((i,Q(1,8) if bad else Q(3,8),[],bad)
                     for i,bad in product((0,1),(False,True)))
    assert call_risk(t,concentrated)==Q(1,2)
    assert call_risk(t,independent)==Q(5,8)
    # Same initial S=3/8, a=w=1: include actual report deadline witnesses.
    F=lambda q:Q(1,4)+q/2-q*q/4
    assert F(Q(1,4))==Q(23,64)<Q(3,8)<F(Q(1,2))==Q(7,16)
    return dict(unknown_coupling_games=games,joint_laws=laws,
                exact_decoder_costs=decoder_checks,erasure_margin_games=erasure_games,
                risk_exact_cut=str(call_risk(t,exactly)),risk_late=str(call_risk(t,late)),
                risk_informative_absence=str(call_risk(t,silence)),
                risk_known_concentrated=str(call_risk(t,concentrated)),
                risk_known_independent=str(call_risk(t,independent)))


if __name__=='__main__':
    print(json.dumps(replay(),indent=2))

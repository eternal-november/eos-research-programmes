"""Exact probes of the continuous-mode resolvent used in FLOW-EXISTENCE."""
from __future__ import annotations
import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
import json
from pathlib import Path
import sys

if sys.flags.optimize:
    raise RuntimeError('Unoptimized Python is required')
HERE=Path(__file__).resolve().parent

def require(ok,message):
    if not ok: raise AssertionError(message)

def shrink(v,h,b):
    require(h>0 and b>=0,'Invalid physical brake step')
    return max(v-h*b,F(0)) if v>=0 else min(v+h*b,F(0))

def sign_member(x,xi):
    return xi==1 if x>0 else xi==-1 if x<0 else -1<=xi<=1

def normal_member(x,n,lo,hi):
    if not lo<=x<=hi: return False
    if lo==hi: return True
    return n<=0 if x==lo else n>=0 if x==hi else n==0

def scalar_checks():
    brake=0;stop=0
    vals=[F(k,3) for k in range(-12,13)]
    for v,h,b in product(vals,(F(1,7),F(1),F(3)),(F(0),F(1,2),F(4))):
        out=shrink(v,h,b);reaction=(v-out)/h
        require(abs(out-v)<=h*b,'Brake displacement bound fails')
        if b:
            require(sign_member(out,reaction/b),'Soft threshold violates the actual Sign relation')
        else:
            require(reaction==0,'Zero brake supplies a fictional reaction')
        brake+=1
    for v,h,(lo,hi) in product(vals,(F(1,7),F(1),F(3)),((F(0),F(1)),(F(-2),F(3)),(F(2),F(2)))):
        out=max(lo,min(hi,v));reaction=(v-out)/h
        require(normal_member(out,reaction,lo,hi),'Clipped stop violates normal-cone sign')
        for old in (lo,(lo+hi)/2,hi):
            require(abs(out-old)<=abs(v-old),'Physical stop projection expands displacement')
        stop+=1
    graph=[(x,xi) for x in vals for xi in (F(-1),F(-1,2),F(0),F(1,2),F(1)) if sign_member(x,xi)]
    for (x,xi),(y,eta) in product(graph,repeat=2):
        require((xi-eta)*(x-y)>=0,'Scalar brake monotonicity failed')
    return dict(brake_steps=brake,physical_stop_steps=stop,sign_monotonicity_pairs=len(graph)**2)

def coupled_coefficient_checks():
    values=(F(-2),F(-1,2),F(0),F(1,2),F(2));cases=0
    for x,z,u,v,xi,eta in product(values,values,values,values,(-1,0,1),(-1,0,1)):
        if not(sign_member(x,xi) and sign_member(z,eta)):continue
        term=((1+abs(u))*xi-(1+abs(v))*eta)*(x-z)
        distance2=(x-z)**2+(u-v)**2
        require(term>=-distance2,'State-dependent brake estimate failed')
        cases+=1
    world=F(3,5);held_rate=F(1);h=F(1,10);upper=F(13,20)
    actual=world+h*held_rate;fiction=min(upper,actual)
    require(actual>upper and fiction==upper,'Safety-projection counterexample vanished')
    allowed1={F(1)};allowed2={F(2)}
    require(not allowed1.intersection(allowed2),'Inconsistent-source witness disappeared')
    return dict(state_dependent_brake_cases=cases,
        world_projection_counterexample=dict(initial=world,actual_next=actual,fictitious_next=fiction,safety_upper=upper),
        incompatible_same_node_source_values=[1,2],
        arbitrary_active_feedback_not_inferred_from_peak_bound=True)

def serial(value):
    if isinstance(value,F):return str(value)
    if isinstance(value,dict):return {k:serial(v) for k,v in value.items()}
    if isinstance(value,(tuple,list)):return [serial(v) for v in value]
    return value

def generate():
    result=dict(status='independently checked conditional continuous-mode derivation; full source-mode map pending',
                scalar=scalar_checks(),coupled=coupled_coefficient_checks())
    result['sources']={name:sha256((HERE/name).read_text(encoding='utf-8-sig').replace('\r\n','\n').encode()).hexdigest()
                       for name in ('FLOW-EXISTENCE.md','flow_existence_model.py','HYBRID.md')}
    return serial(result)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    choice=parser.add_mutually_exclusive_group(required=True)
    choice.add_argument('--write',action='store_true');choice.add_argument('--check',action='store_true')
    args=parser.parse_args();result=generate();target=HERE/'flow_existence_results.json'
    if args.write:target.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n',encoding='utf-8',newline='\n')
    else:require(json.loads(target.read_text(encoding='utf-8-sig'))==result,'Flow-existence record differs')
    print('flow-existence record '+('written' if args.write else 'matches'))

if __name__=='__main__':main()

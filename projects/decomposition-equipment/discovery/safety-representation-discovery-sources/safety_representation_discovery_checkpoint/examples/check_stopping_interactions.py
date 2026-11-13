#!/usr/bin/env python3
"""Exact finite checks for Stopping_Interaction_Discovery.md; standard library."""
from fractions import Fraction as Q
from itertools import product, combinations
from pathlib import Path
import json, math

bits=list(product((0,1),repeat=3))
def law(q, marg=Q(1,10), pair=Q(1,100)):
    p={}
    for x in bits:
        s=sum(x)
        p[x]=q if s==3 else pair-q if s==2 else marg-2*pair+q if s==1 else 1-3*marg+3*pair-q
    return p

def mean(p,f):return sum((v*f(x) for x,v in p.items()),Q(0))
def hazard(x):return int(sum(x)>=2)
counts={"moment_laws":0,"pointwise_identity":0,"projected_markov_rows":0,"stopping_cells":0,"message_response_rows":0}
for q in (Q(0),Q(1,100),Q(7,1000)):
    p=law(q);assert min(p.values())>=0 and sum(p.values())==1
    for i in range(3):assert mean(p,lambda x:x[i])==Q(1,10)
    for i,j in combinations(range(3),2):assert mean(p,lambda x:x[i]*x[j])==Q(1,100)
    assert mean(p,hazard)==Q(3,100)-2*q
    counts['moment_laws']+=1
for x in bits:
    assert hazard(x)==sum(x[i]*x[j] for i,j in combinations(range(3),2))-2*x[0]*x[1]*x[2]
    counts['pointwise_identity']+=1
# The interval certificate is sharp: upper pair and lower triple values have a feasible law.
eps=Q(1,2000)
pair=Q(1,100)+eps;q=Q(7,1000)-eps
p=law(q,pair=pair)
assert min(p.values())>=0 and sum(p.values())==1
assert mean(p,hazard)==Q(37,2000)<Q(1,50)
assert mean(p,hazard)==Q(2,125)+5*eps
# Actual stopping calibration.
for b,tau in product((Q(1),Q(2)),(Q(0),Q(1,2))):
    distance=2*tau+Q(4)/(2*b)
    assert (distance>Q(5,2))==(b==1 and tau==Q(1,2))
    counts['stopping_cells']+=1
# Arbitrary finite stopping thresholds need m+1 distinguishable one-way messages.
for m in range(1,13):
    brake=[Q(i+1) for i in range(m)]
    thresholds=[Q(5,2)-Q(1,b) for b in brake]
    assert all(thresholds[i]<thresholds[i+1] for i in range(m-1))
    reps=[Q(0)]+[(thresholds[i]+thresholds[i+1])/2 for i in range(m-1)]+[thresholds[-1]+1]
    rows={tuple(int(2*tau+Q(2,b)>5) for b in brake) for tau in reps}
    assert len(rows)==m+1
    counts['message_response_rows']+=len(rows)
# Strong lumpability: all proper projections of either parity-coset chain have exactly the same kernel.
rho=Q(3,4)
for m in range(3,7):
    allstates=list(product((0,1),repeat=m))
    cosets=[[x for x in allstates if sum(x)%2==parity] for parity in (0,1)]
    for k in range(1,m):
        for S in combinations(range(m),k):
            project=lambda x:tuple(x[j] for j in S)
            targets=list(product((0,1),repeat=k))
            reference={}
            for parity,C in enumerate(cosets):
                for x in C:
                    row={z:Q(0) for z in targets}
                    # Increment uniform on even subgroup implies next point uniform in same coset.
                    for y in C:
                        row[project(y)]+=(1-rho)/len(C)+(rho if y==x else 0)
                    expected={z:(1-rho)/len(targets)+(rho if z==project(x) else 0) for z in targets}
                    assert row==expected
                    if parity==0:reference[project(x)]=row
                    else:assert row==reference[project(x)]
                    counts['projected_markov_rows']+=1
# Changing patches within a correlated trajectory CAN reveal parity; protect the acquisition qualification.
C0=[x for x in bits if sum(x)%2==0];C1=[x for x in bits if sum(x)%2==1]
switched=[]
for C in (C0,C1):
    probability=Q(0)
    for x in C:
        if x[0:2]!=(0,0):continue
        for y in C:
            if y[2]==0:probability+=(Q(1,len(C)))*((1-rho)/len(C)+(rho if y==x else 0))
    switched.append(probability)
assert switched==[(1+rho)/8,(1-rho)/8]
assert switched[0]!=switched[1]
# Hazard gap and rare common activation.
even=cosets=None
C0=[x for x in bits if sum(x)%2==0];C1=[x for x in bits if sum(x)%2==1]
r0=sum(map(hazard,C0))/len(C0);r1=sum(map(hazard,C1))/len(C1)
assert r0==.75 and r1==.25
activation=Q(1,100)
assert activation*Q(3,4)==Q(3,400)
assert activation*Q(1,4)==Q(1,400)
# Hoeffding sample burden for 7 predeclared functions, delta .05, epsilon .0005.
N=math.ceil(math.log(280)/(2*float(eps)**2));assert N==11269580
assert Q(983,1000)**300<Q(1,140)
zero_bound=1-(1/140)**(1/300)
assert zero_bound<.017<.02
assert 240+30+30==300
result={"status":"PASS","counts":counts,
 "pair_only_risk_interval":["1/100","3/100"],
 "risk_at_q_7_over_1000":"2/125",
 "interval_robust_risk":"37/2000","risk_budget":"1/50",
 "hoeffding_validation_records":N,
 "zero_event_validation_records":300,"zero_event_upper_bound":zero_bound,
 "zero_event_rational_bound":"17/1000",
 "persistent_proper_patch_history_indistinguishability":"verified by exact strong-lumpability rows for m=3..6; all-horizon proof in note",
 "rare_activation_risks":["3/400","1/400"],
 "switched_patch_distinguishes_correlated_cosets":list(map(str,switched))}
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))

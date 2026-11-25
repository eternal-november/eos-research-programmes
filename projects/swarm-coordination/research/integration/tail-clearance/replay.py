"""Source-semantic slice translated manually; independent rational-time checks."""
from fractions import Fraction as Q
from hashlib import sha1
from itertools import product
from pathlib import Path
from math import ceil

HERE=Path(__file__).resolve().parent
PINS={
 "IncrementalRequirementEnvelopeAdapter.kt":"0535eae644c66cfcd3ffd82542ebca132b457843",
 "SpacingResourceGenerator.kt":"1ffe593c2cd619c11003dc7b74550bd3b9b6af98",
 "SpacingResourceGeneratorTest.kt":"6d1b3900679e833a7793593c49336a896b80a075",
 "RequirementTypes.kt":"36c67018a0ccb6a1907727ca99077727f4c532be",
 "Conflicts.kt":"f83cda6bae415f9b93361752ba54c2fbb788a5a5",
 "RequirementsParser.kt":"15c9c08723f4de4e2571cbaac3cd74d96eacbd09",
}
files={}
for f,digest in PINS.items():
    raw=(HERE/f).read_bytes()
    assert sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==digest
    files[f]=raw.decode()

def source_anchors():
    assert "val criticalPoint = end + rollingStock.length" in files["IncrementalRequirementEnvelopeAdapter.kt"]
    assert "return envelopeWithStops.interpolateDepartureFrom(criticalPoint)" in files["IncrementalRequirementEnvelopeAdapter.kt"]
    generator=files["SpacingResourceGenerator.kt"]
    assert "if (endTime >= simCurrentTime)" in generator
    assert "isComplete = callbacks.simulationComplete" in generator
    assert "if (requirement.isComplete) zonePathsToRemove.add(zonePath)" in generator
    assert "RJSSpacingRequirement(infra.getZoneName(zone), beginTime.seconds, endTime.seconds)" in files["RequirementTypes.kt"]
    assert "endTime <= requirement.beginTime" in files["Conflicts.kt"]
    assert "callbacks.currentTime, requirement.endTime" in files["SpacingResourceGeneratorTest.kt"]
source_anchors()

def head(points,t):
    for (a,x),(b,y) in zip(points,points[1:]):
        if a<=t<=b:return x+(y-x)*(t-a)/(b-a)
    return points[0][1] if t<points[0][0] else points[-1][1]

def modeled_departure(points,zone_end,length):
    # Narrowed constant-stock, continuously moving envelope. No stop dwell.
    target=zone_end+length
    if not points[0][1]<=target<=points[-1][1]:return None
    for (a,x),(b,y) in zip(points,points[1:]):
        if x<=target<=y:return a+(b-a)*(target-x)/(y-x)
    assert False

def export(raw,current,simulation_complete,start=0):
    if raw is None or raw>=current:
        return (start,current,simulation_complete)
    return (start,raw,True)

def witnessed(raw,current):
    return raw is not None and raw<=current

a=((Q(0),Q(0)),(Q(2),Q(2)))
b=((Q(0),Q(0)),(Q(2),Q(3,2)))
tails=[modeled_departure(p,1,1) for p in (a,b)]
assert tails==[Q(2),None]
for done in False,True:
    assert export(tails[0],2,done)==export(tails[1],2,done)==(0,2,done)
assert witnessed(tails[0],2) and not witnessed(tails[1],2)
print('same interval and complete flag, modeled tail at horizon versus not reached')

tests=0
for t0,t1,mid,end,zone_len,stock in product((1,2),(1,3),range(1,8),range(2,11),range(0,6),range(1,5)):
    if mid>=end:continue
    p=((Q(0),Q(0)),(Q(t0),Q(mid)),(Q(t0+t1),Q(end)))
    raw=modeled_departure(p,zone_len,stock)
    expected=p[-1][1]>=zone_len+stock
    assert witnessed(raw,p[-1][0])==expected
    if expected:
        assert head(p,raw)-stock==zone_len
        assert head(p,max(Q(0),raw-Q(1,100)))-stock<zone_len
    for complete in False,True:
        start,out,c=export(raw,p[-1][0],complete)
        assert start==0 and out<=p[-1][0]
        if out<p[-1][0]:assert expected and c and out==raw
        else:assert c==complete
        tests+=1
print('translated finite-envelope export checks',tests)

FAST=((Q(0),Q(0)),(Q(1),Q(3,2)),(Q(2),Q(3)))
SLOW=((Q(0),Q(0)),(Q(1),Q(3,4)),(Q(2),Q(3)))
assert modeled_departure(FAST,Q(1,2),1)==1
assert modeled_departure(SLOW,Q(1,2),1)==Q(4,3)

def start_times(grants,profiles,lags):
    starts=[grants[0]]
    for g,p,l in zip(grants[1:],profiles,lags):
        tail=modeled_departure(p,Q(1,2),1)
        starts.append(max(g,starts[-1]+ceil(tail)+l))
    return starts

def enumerate_earliest(grants,profiles,lags):
    # Independent integer scheduling with actual position at the
    # predecessor's last fully available observation cut.
    N=len(grants)
    best=[None]*N
    def visit(pre):
        i=len(pre)
        if i==N:return
        for s in range(grants[i],max(grants)+4*N+1):
            if i and head(profiles[i-1],Q(s-pre[-1]-lags[i-1]))-1<Q(1,2):
                continue
            if best[i] is None or s<best[i]:best[i]=s
            visit(pre+(s,))
    visit(())
    return best

def verify_footprints(starts,profiles):
    for i,(s,t) in enumerate(zip(starts,starts[1:])):
        # At every breakpoint, check predecessor head minus successor head.
        # Between breakpoints the difference is linear.
        for cut in (s,s+1,s+2,t,t+1,t+2):
            gap=3+head(profiles[i],Q(cut-s))-head(profiles[i+1],Q(cut-t))
            assert gap>=1

checks=0
for n in range(1,4):
    for grants in product(range(0,4),repeat=n):
        for p in product((FAST,SLOW),repeat=n):
            for lag in product(range(2),repeat=n-1):
                starts=start_times(grants,p,lag)
                assert starts==enumerate_earliest(grants,p,lag)
                verify_footprints(starts,p)
                checks+=1
print('exact event recurrence, enumerated starts, continuous footprints',checks)
for p,l,want in [(FAST,0,38),(SLOW,0,42),(FAST,1,42)]:
    grants=[32]*5
    starts=start_times(grants,[p]*5,[l]*4)
    verify_footprints(starts,[p]*5)
    last=max(31+2,max(starts)+2)
    assert last==want
    print('observed release lag per follower',ceil(modeled_departure(p,Q(1,2),1))+l,
          'same #455 grants; last completion',last)

def final(slacks,grants,d=2):
    return d+max(g+s for g,s in zip(grants,slacks))

def suffix_weights(r):
    return tuple(sum(r[i:]) for i in range(len(r)+1))

def corner_profile(slacks,lower,upper):
    base=final(slacks,lower)
    return base,tuple(max(base,g+s+2) for g,s in zip(upper,slacks))

def eval_profile(probes,upper,grants):
    base,spikes=probes
    return max(base,*(value-hi+g for value,hi,g in zip(spikes,upper,grants)))

pc=0
for lower in product(range(2),repeat=3):
    for wiggle in product(range(3),repeat=3):
        upper=tuple(a+b for a,b in zip(lower,wiggle))
        all_grants=tuple(product(*(range(a,b+1) for a,b in zip(lower,upper))))
        p2lang={}
        lang2p={}
        for r in product(range(4),repeat=2):
            c=suffix_weights(r)
            vals=tuple(final(c,g) for g in all_grants)
            probes=corner_profile(c,lower,upper)
            assert vals==tuple(eval_profile(probes,upper,g) for g in all_grants)
            assert p2lang.setdefault(probes,vals)==vals
            assert lang2p.setdefault(vals,probes)==probes
            pc+=len(vals)
x,y=map(suffix_weights,((1,2),(2,1)))
assert corner_profile(x,(0,0,0),(0,1,0))==corner_profile(y,(0,0,0),(0,1,0))
assert final(x,(0,2,0))==6 and final(y,(0,2,0))==5
print('bounded independent grant profiles: exact minimal equivalence',pc,'queries')

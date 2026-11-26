"""Exact continuous within-slot checks for a shared quantized brake."""
from fractions import Fraction as Q
from itertools import combinations,product
from collections import defaultdict
import json

def integrate(bs):
    """Track gap extrema continuously, not just sample endpoints."""
    g=Q(0)
    w=Q(0)
    low=high=g
    sF=sR=Q(0);vF=vR=Q(len(bs),2)
    interior=0
    for a in bs:
        # a=1 awards full brake to rear, expanding the gap.
        assert a in (-1,1)
        if a>0:
            assert vR>=1
            sR+=vR-Q(1,2);sF+=vF;vR-=1
        else:
            assert vF>=1
            sF+=vF-Q(1,2);sR+=vR;vF-=1
        z=-w/a
        if 0<z<1:
            extremum=g+w*z+a*z*z/2
            low=min(low,extremum);high=max(high,extremum)
            interior+=1
        g+=w+Q(a,2)
        w+=a
        low=min(low,g)
        high=max(high,g)
    assert vR==vF==w==0 and g==sF-sR
    return (g,low,high,sF,sR,interior)

def construct(v,k,d,u):
    if abs(k)>v:raise ValueError('inside target range only')
    if ((v-k)%2 or k < -d or k>u or max(d,u)<1):
        return None
    sign = 1 if k>0 or (k==0 and u>=1) else -1
    loops=(v-abs(k))//2
    pairs=[sign,-sign]*loops+[sign]*abs(k)
    ans=tuple(s for q in pairs for s in (q,-q))
    assert len(ans)==2*v
    return ans

def main():
    policies=0;checks=0
    extrema={};endpoint={}
    for v in range(1,8):
        shapes=defaultdict(set)
        for bs in combinations(range(2*v),v):
            aset=set(bs)
            dd=integrate(tuple(1 if i in aset else -1 for i in range(2*v)))
            g,l,h,F,R,_=dd
            assert F+R==2*v*v and g.denominator==1 and int(g)%2==v%2
            assert max(-l,h)>=1
            shapes[int(g)].add((-l,h))
            policies+=1
        for k,d,u in product(range(-v,v+1),(Q(0),Q(1,2),1,Q(3,2),2,v),
                             (Q(0),Q(1,2),1,Q(3,2),2,v)):
            cmd=construct(v,k,d,u)
            direct=any(a<=d and b<=u for a,b in shapes[k])
            assert (cmd is not None)==direct
            if cmd:
                g,l,h,*_=integrate(cmd)
                assert k==g and -l<=d and h<=u
            checks+=1
        extrema[v]=[min(shapes),max(shapes)]
        endpoint[v]=bool(shapes[0])
    # Terminal equality exists in the discrete endpoint problem at v=2,
    # but its valid paths cannot fit the strict persistent tube.
    assert construct(2,0,Q(1,2),Q(1,2)) is None and endpoint[2]
    witness=construct(2,0,0,1)
    assert witness==(1,-1,-1,1)
    assert integrate(witness)[:5]==(0,0,1,4,4)
    assert construct(3,0,9,9) is None and not endpoint[3]
    # Same physical acceleration and deadline; halve the hold, not the
    # commanded deceleration. Distance unit becomes 1/4.
    h=Q(1,2)
    faster=construct(4,0,Q(1,2)/(h*h),Q(1,2)/(h*h))
    g,l,r,f,rear,_=integrate(faster)
    assert (g*h*h,l*h*h,r*h*h,f*h*h,rear*h*h)==(0,0,Q(1,4),4,4)
    print(json.dumps(dict(enumerated_binary_schedules=policies,
          exact_comparisons=checks,terminal_zero_feasible_with_no_gap_tube=endpoint,
          terminal_ranges=extrema,positive_witness=witness,
          positive_one_sided_tube=1,
          negative_tube_half_each_endpoint_feasible=True,
          half_hold_physical_excursion=str(r*h*h),
          continuous_split_equal_gap=0),indent=2,sort_keys=True))
if __name__=='__main__':main()

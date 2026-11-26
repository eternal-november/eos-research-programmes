#!/usr/bin/env python3
"""Authored three-cut schedules; not an implementation-conformance test."""
from itertools import permutations,product
from random import Random
import json

C=("L","R","off")


def fixture(order,dwell,start):
    version="A"
    selected=None
    authority="old"
    for e in order:
        if e=="bind":
            selected="L" if version=="A" else "R"
        if e=="enable":
            version="B"
        if e=="transfer":
            authority="new"
    # A route selected by the old authority may remain physically active
    # after authority moves. Only its actual end releases its capacity.
    return (version,authority), tuple((selected,t) for t in range(start,start+dwell))


def peak(hist,cap):
    return {key:max(h.count(key) for h in hist) for key in cap}


def direct(hist,c,plan):
    return all(all(h.count(k)+plan.count(k)<=v for k,v in c.items()) for h in hist)


def reduced(p,c,plan):
    return all(p[k]+plan.count(k)<=v for k,v in c.items())


def replay():
    cap={(s,t):(1 if s!="off" else 2) for s,t in product(C,range(7))}
    cuts=[fixture(order,d,s) for order in permutations(["bind","enable","transfer"])
          if order.index("bind")<order.index("transfer")
          for d,s in product(range(1,4),range(3))]
    assert {obs for obs,h in cuts}=={("B","new")}
    left=fixture(("bind","enable","transfer"),2,1)
    right=fixture(("enable","bind","transfer"),2,1)
    clear=fixture(("bind","enable","transfer"),1,0)
    assert left[0]==right[0]==clear[0]
    assert [direct([h],cap,[(s,1)]) for _,h in (left,right) for s in ("L","R")]==[False,True,True,False]
    assert not any(direct([left[1],right[1]],cap,[(s,1)]) for s in ("L","R"))
    assert direct([left[1],right[1]],cap,[("off",1)])
    assert direct([clear[1],right[1]],cap,[("L",1)])
    # Distinct observed histories are legal but projected only onto the
    # exact possible capacity already held at each relevant cell and tick.
    cmp=0
    rng=Random(525)
    for i in range(450):
        hs=[rng.choice(cuts)[1] for _ in range(rng.randrange(1,8))]
        a=peak(hs,cap)
        for q in range(10):
            plan=[rng.choice(tuple(cap)) for _ in range(rng.randrange(12))]
            assert direct(hs,cap,plan)==reduced(a,cap,plan)
            cmp+=1
    return dict(exact_effect_replays=cmp, distinct_timed_histories=len(set(h for _,h in cuts)),
                named_left_when_old_bound_first=False,
                named_left_when_new_enabled_first=True,
                unrelated_stays_admissible=True,
                left_admissible_after_actual_clearance=True)


if __name__=="__main__":
    print(json.dumps(replay(),indent=2))

#!/usr/bin/env python3
"""Exact finite clock and release-observation handoff model."""
from dataclasses import dataclass
import json
from random import Random

@dataclass(frozen=True)
class Trace:
    clock_old:int
    clock_new:int
    tail:int
    receipt:int|None
    def cut(self):
        return self.clock_new-self.clock_old+self.tail

def solve(ts):
    assert ts and all(t.tail>=0 and (t.receipt is None or t.receipt>=0) for t in ts)
    g=max(t.cut() for t in ts)
    timer=max(g-t.cut() for t in ts)
    receipt=None if any(t.receipt is None for t in ts) else max(t.receipt for t in ts)
    combined=max(g-t.cut() if t.receipt is None else min(g-t.cut(),t.receipt) for t in ts)
    return g,timer,receipt,combined

def brute(ts):
    # Trace forward directly on world time, using old local withdraw tick 0.
    # Use a range spanning every input and later safe choices.
    lo=min(-t.clock_old+t.tail+t.clock_new for t in ts)-3
    hi=max(-t.clock_old+t.tail+t.clock_new for t in ts)+3
    answer=[]
    for both in (False,True):
        policies=[]
        for send in range(lo,hi+1):
            loss=[]
            for t in ts:
                old_first_free=-t.clock_old+t.tail
                candidate=send-t.clock_new
                if both and t.receipt is not None:
                    candidate=min(candidate,old_first_free+t.receipt)
                if candidate<old_first_free:break
                loss.append(candidate-old_first_free)
            if len(loss)==len(ts):policies.append((max(loss),send))
        answer.append(min(policies))
    return answer

def replay():
    # A late settlement trace and a slow receipt trace need not be the same one.
    current=[Trace(0,0,1,1), Trace(0,4,1,4)]
    assert solve(current)==(5,4,4,1)
    assert brute(current)==[(4,5),(1,5)]
    crossed=[Trace(0,0,1,4),Trace(0,4,1,1)]
    assert solve(crossed)==(5,4,4,4)
    missing=[Trace(0,0,1,None), Trace(0,4,1,4)]
    assert solve(missing)==(5,4,None,4)
    obsolete=[Trace(0,0,0,0),Trace(0,4,0,0)]
    assert solve(obsolete)[0]==4 # using an old zero tail would cut one tick early
    R=Random(555)
    for _ in range(3200):
        ts=[Trace(R.randrange(-4,5),R.randrange(-4,5),R.randrange(5),
                  R.choice([None,0,1,2,3,4,5])) for _ in range(R.randrange(1,10))]
        g,timer,_,hybrid=solve(ts)
        p=brute(ts)
        assert p==[(timer,g),(hybrid,g)]
    return dict(exact_comparisons=3200,timer_only_worst_gap=4,receipt_only_worst_gap=4,
                combined_worst_gap=1,crossed_traces_worst_gap=4,missing_receipt_worst_gap=4)
if __name__=='__main__':print(json.dumps(replay(),sort_keys=True,indent=2))

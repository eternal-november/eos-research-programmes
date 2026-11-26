#!/usr/bin/env python3
"""Prospective owner revocation. Authority/transport/bounded effect laws are inputs."""
from random import Random
import json

def safe_send_span(start,tail,prefix,arrival,brake,cutoff,send):
    a,b=start
    u,v=arrival
    j,k=brake
    lo,hi=send
    assert a<=b and 0<=prefix<=tail and 0<=u<=v and 0<=j<=k
    # All starts remain admitted and each required prefix completes.
    lo=max(lo,b+1-u,b+prefix+1-j-u)
    # If even the uncut tail finishes in time no extra upper fence constraint.
    if b+tail>=cutoff:
        hi=min(hi,cutoff-v-k)
    return None if hi<lo else (lo,hi)

def evaluate(r,start,tail,prefix,arrival,brake,cutoff):
    a,b=start
    u,v=arrival
    j,k=brake
    for s in range(a,b+1):
        for f in range(r+u,r+v+1):
            for lag in range(j,k+1):
                # Abort completion at f+lag, but already-running effects before this cut.
                effects=set(range(s,min(s+tail+1,f+lag))) if s<f else set()
                if any(t not in effects for t in range(s,s+prefix+1)):return False
                if any(t>=cutoff for t in effects):return False
    return True

def replay():
    args=((1,1),6,3)
    send=(0,10)
    remote=(1,3)
    delegated=(1,2)
    cutoff=6
    assert safe_send_span(*args,remote,(1,1),cutoff,send) is None
    assert safe_send_span(*args,delegated,(1,1),cutoff,send)==(3,3)
    assert safe_send_span(*args,delegated,(1,2),cutoff,send) is None
    # Clearing a report at fence receipt says nothing about its following brake lag.
    assert not evaluate(3,*args,delegated,(1,2),6)
    # If both valid actors must wait for remote authorization, delay stays unbounded here.
    # With a local right active at 4 rather than at 3, the generous effect bound misses.
    assert safe_send_span(*args,delegated,(1,1),cutoff,(4,10)) is None
    R=Random(546)
    cases=ticks=0
    for _ in range(7200):
        def pair(a,b):return tuple(sorted(R.choices(range(a,b+1),k=2)))
        start=pair(-3,8)
        tail=R.randrange(8)
        prefix=R.randrange(tail+1)
        arrival,brake=pair(0,7),pair(0,4)
        cutoff=R.randrange(-2,16)
        send=pair(-4,19)
        args=start,tail,prefix,arrival,brake,cutoff
        span=safe_send_span(*args,send)
        attained=[r for r in range(send[0],send[1]+1) if evaluate(r,*args)]
        assert attained==([] if span is None else list(range(span[0],span[1]+1)))
        cases+=1;ticks+=send[1]-send[0]+1
    return dict(exact_scenario_comparisons=cases,individual_send_choices=ticks,
        remote_no_safe_send=True,locally_amended_only_tick=3,
        local_authority_start_at_4_fails=True,unreconciled_stop_lag_can_break_deadline=True)
if __name__=='__main__':print(json.dumps(replay(),indent=2,sort_keys=True))

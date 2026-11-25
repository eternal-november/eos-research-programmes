"""Verify an exact blocker-set composition by complete finite comparisons."""
from itertools import product
import json

def online_pair(schedule, until):
    """Insert/retire the exact occurrence, then derive each resource health."""
    active={}
    out=[]
    for t in range(until):
        for i,(start,end,scope) in enumerate(schedule):
            if t==start: active[i]=scope
            if t==end: del active[i]
        disabled=set().union(*active.values())
        out.append(disabled)
    return out

def joint_window(schedule,t):
    """Pointwise specification; uses neither ledger nor incremental updates."""
    return {r for start,end,scope in schedule if start<=t<end for r in scope}

if __name__=="__main__":
    tests=0
    span=[(s,e) for s in range(4) for e in range(s+1,6)]
    masks=[{i for i in range(3) if bits>>i&1} for bits in range(1,8)]
    event=[(s,e,m) for (s,e), m in product(span,masks)]
    for a,b in product(event,repeat=2):
        result=online_pair([a,b],6)
        for t,disabled in enumerate(result):
            assert disabled==joint_window([a,b],t)
            tests+=1
    print(json.dumps({"two_occurrences_pointwise_checks":tests,
                      "includes_equal_scopes_and_equal_cuts":True},sort_keys=True))

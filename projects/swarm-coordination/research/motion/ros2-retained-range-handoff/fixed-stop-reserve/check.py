#!/usr/bin/env python3
from collections import Counter
from itertools import product
from functools import lru_cache
import json,sys

@lru_cache(None)
def ok(room,p,r,n):
    if p==0:return room>=0
    if n==0:return False
    return any(ok(room-u,u,r,n-1) for u in range(min(room,15)+1) if abs(u-p)<=r)
def formula(p,r):
    q=p//r
    return q*p-r*q*(q+1)//2
checks=0
for room,p,r in product(range(41),range(16),range(1,5)):
    assert ok(room,p,r,15)==(formula(p,r)<=room)
    checks+=1
seen=set()
c=Counter()
for line in open(sys.argv[1],encoding="utf-8"):
    a=line.split()
    W,R,D,g=map(int,a[:4])
    key=W,R,D,g
    assert key not in seen
    seen.add(key)
    isbad=a[-1]=="E"
    cmd=list(map(int,a[4:-1] if isbad else a[4:]))
    p,x=0,0
    first_leave=None
    for j,u in enumerate(cmd):
        low=max(-8-x,-15,p-R)
        high=min(W-x,15,p+R)
        if g:
            exact=[v for v in range(min(15,W-x)+1)
                   if abs(v-p)<=R and ok(W-x-v,v,R,15)]
            assert exact and u==min(exact,key=lambda v:abs(v-D))
        else:
            expected=min(max(D,min(low,high)),max(low,high))
            assert u==expected
        if not 0<=u<=W-x or abs(u-p)>R:
            assert isbad and not g and j==len(cmd)-1
            c["native_bad"]+=1
            assert first_leave is not None and first_leave<j
        else:
            x+=u
            if first_leave is None and not ok(W-x,u,R,15):
                first_leave=j
        p=u
    if g:
        assert not isbad and first_leave is None
        c["guarded_kept_stoppable"]+=1
    elif first_leave is not None:
        c["native_left_stoppable"]+=1
        if not isbad:
            c["left_without_observed_violation"]+=1
    if not isbad:
        assert len(cmd)==12
assert seen==set(product(range(4,41),range(1,5),range(1,11),range(2)))
assert c["guarded_kept_stoppable"]==1480
print(json.dumps({"trace_rows":len(seen),"exact_stopping_states":checks,**c},sort_keys=True))

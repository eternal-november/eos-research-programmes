#!/usr/bin/env python3
"""Finite minimax oracle and a separate one-reservation policy trace replay."""
from functools import lru_cache
from itertools import product
import json

W=((0,0),(0,1),(1,1))


def distance(i,j,complete):
    return int(i!=j) if complete else abs(i-j)


def minimax(s,depth,locks,complete):
    @lru_cache(None)
    def spread(belief):
        return tuple(max([-1]+[r-distance(i,j,complete)
                              for i,r in enumerate(belief) if r>=0]) for j in range(3))
    @lru_cache(None)
    def go(belief,reserved,positive,left):
        if all(any(reserved[g]==v or (positive>>(2*g+v)&1 and all(
                   W[j][g]==v for j,b in enumerate(belief) if b>=0))
                   for v in (0,1)) for g in (0,1)):
            return True
        if not left:return False
        ext=spread(belief)
        for g,v in product((0,1),repeat=2):
            if reserved[g]>=0:continue
            for q in (False,True):
                new=tuple(x if (W[j][g]==v)==q else -1 for j,x in enumerate(ext))
                if max(new)<0:continue
                P=positive|(1<<(2*g+v)) if q else positive
                R=tuple(v if k==g and q and (locks>>g)&1 else rv
                        for k,rv in enumerate(reserved))
                if not go(new,R,P,left-1):break
            else:
                return True
        return False
    return go((s,s,s),(-1,-1),0,depth)


def first_query(s):
    return (0,0) if s%2==0 else (1,1)


def transition(phase,action,ok):
    """Uses only responses and its current phase, never a world or switch count."""
    g,v=action
    if phase=='initial':
        if not ok:
            return ('initial',(1,1) if g==0 else (0,0))
        return ('freeRadio',(1,0)) if g==0 else ('findWarehouse',(0,1))
    if phase=='freeRadio':
        return ('commit',v) if ok else ('freeRadio',(1,1-v))
    if phase=='findWarehouse':
        if not ok:return ('findWarehouse',(0,1-v))
        return ('commit',1) if v==1 else ('confirmRadio',(1,0))
    assert phase=='confirmRadio'
    return ('commit',0 if ok else 1)


def trace(s,complete):
    @lru_cache(None)
    def step(i,left,phase,q,warehouse,priorRadio,used):
        g,v=q
        ok=W[i][g]==v
        if ok and g==0: warehouse=v
        if ok and g==1: priorRadio|=1<<v
        kind,data=transition(phase,q,ok)
        if kind=='commit':
            assert warehouse>=0 and priorRadio>>data&1 and W[i][1]==data
            return (used,1)
        assert used < s+3
        vals=[step(j,left-d,kind,data,warehouse,priorRadio,used+1)
              for j in range(3) if (d:=distance(i,j,complete))<=left]
        return max(x for x,y in vals),sum(y for x,y in vals)
    all=[step(i,s,'initial',first_query(s),-1,0,1) for i in range(3)]
    return max(x for x,y in all),sum(y for x,y in all)


def replay():
    exact=trials=cases=0
    for complete in (False,True):
        assert minimax(0,3,0,complete) and not minimax(0,2,0,complete)
        for s in range(1,9):
            assert not minimax(s,2*s+9,0,complete)
        for s in range(19):
            for lock in (1,2,3):
                assert minimax(s,s+3,lock,complete)
                assert not minimax(s,s+2,lock,complete)
                exact+=1
            m,k=trace(s,complete)
            assert m==s+3
            trials+=k
            cases+=1
    return dict(exact_minimax_budget_checks=exact,
                no_lock_finite_horizon_controls=16,
                one_lock_policy_input_families=cases,
                joined_terminating_state_sequences=trials,
                largest_switch_budget=18)


if __name__=='__main__':
    print(json.dumps(replay(),indent=2))

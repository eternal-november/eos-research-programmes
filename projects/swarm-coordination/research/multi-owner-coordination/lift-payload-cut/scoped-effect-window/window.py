#!/usr/bin/env python3
"""Integer windows for a separately enforced shared-effect authority model."""
from dataclasses import dataclass
from itertools import product
from random import Random
import json

def canon(xs):
    out=[]
    for l,r in sorted(xs):
        if r<l: continue
        if out and l<=out[-1][1]+1:
            a,b=out.pop()
            out.append((a,max(b,r)))
        else:out.append((l,r))
    return out

def subtract(xs,ys):
    xs=canon(xs)
    for a,b in canon(ys):
        n=[]
        for l,r in xs:
            if b<l or r<a:
                n.append((l,r))
            else:
                if l<a:n.append((l,a-1))
                if b<r:n.append((b+1,r))
        xs=n
    return xs

def has(xs,t):return any(l<=t<=r for l,r in xs)

@dataclass(frozen=True)
class Cohort:
    body: str
    exposure: tuple
    permits: tuple

@dataclass(frozen=True)
class Branch:
    name: str
    delay: tuple
    cohorts: tuple

def select(ready,latest,deadline,branches):
    if not branches: return None # no licensed source histories
    end=min(latest,*[deadline-b.delay[1] for b in branches])
    bad=[]
    for b in branches:
        e,f=b.delay
        assert 0<=e<=f
        for c in b.cohorts:
            for l,r in subtract(c.exposure,c.permits):
                bad.append((l-f,r-e))
    return subtract([(ready,end)],bad)

def direct(ready,latest,deadline,branches):
    if not branches:return None
    good=[]
    for issue in range(ready,latest+1):
        winning=True
        for b in branches:
            if issue+b.delay[1]>deadline:winning=False
            for d,c in product(range(b.delay[0],b.delay[1]+1),b.cohorts):
                t=issue+d
                if has(c.exposure,t) and not has(c.permits,t):winning=False
        if winning:good.append((issue,issue))
    return canon(good)

def demo():
    # Both alternative worlds constrain the same proposed trip and issue cut.
    isolated=Branch('fenced', (1,4), (Cohort('old-box',((0,5),),((5,8),)),))
    naked=Branch('fenced but no trip consent', (1,4), (Cohort('old-box',((0,5),),()),))
    early_expiring=Branch('expiry before first possible authorized effect', (1,4), (Cohort('old-box',((0,5),),((0,4),)),))
    late=Branch('entry / late unauthorized party', (1,4), (Cohort('old-box',((0,5),),((5,8),)),
                                      Cohort('unassigned-box',((6,8),),())))
    assert select(4,12,8,[isolated])==[(4,4)]
    assert select(4,12,8,[naked])==[]
    assert select(4,12,20,[naked])[0][0]+4==9
    assert select(4,12,8,[early_expiring])==[]
    assert select(4,12,8,[isolated,late])==[]
    # Delayed dwell affects a held older payload (split first/last hazard cuts).
    occupied=(Cohort('old',((0,12),),((5,8),)),)
    assert select(4,12,8,[Branch('right through effect',(1,4),occupied)])==[(4,4)]
    assert select(4,12,8,[Branch('permission too early',(1,4),(
        Cohort('old',((0,12),),((5,7),)),))])==[]
    # Same two private premises in different branches need not coexist:
    # immediate effect in the clear branch; delayed effect in the occupied branch
    # only after its resident's permission starts.
    real=[Branch('empty',(1,2),(Cohort('old',(),()),)),
          Branch('loading',(3,4),(Cohort('old',((0,8),),((7,8),)),))]
    crossed=Branch('incorrect cross', (1,4), real[1].cohorts)
    assert select(4,8,8,real)==[(4,4)]
    assert select(4,8,8,[crossed])==[]
    return {'deadline_with_authorized_residual':8,
            'first_finish_after_empty_without_permission':9,
            'late_entry_invalidates':True,'early_expiry_invalidates':True,
            'wrong_cross_branch_refuses':True}

def test():
    out=demo()
    R=Random(544)
    checks=effect_queries=0
    def range_pair(k):return tuple(sorted(R.sample(range(k),2)))
    for i in range(2400):
        branches=[]
        for j in range(R.randrange(1,4)):
            cs=tuple(Cohort(str(a),tuple(range_pair(18) for _ in range(R.randrange(4))),
                                    tuple(range_pair(18) for _ in range(R.randrange(4))))
                  for a in range(R.randrange(4)))
            branches.append(Branch(str(j),range_pair(6),cs))
        ready,latest=range_pair(10)
        D=R.randrange(12,20)
        args=ready,latest,D,branches
        assert select(*args)==direct(*args)
        checks+=1;effect_queries+=latest-ready+1
    out.update({'exact_interval_comparisons':checks,'explicit_issue_time_queries':effect_queries})
    return out
if __name__=='__main__':
    print(json.dumps(test(),sort_keys=True,indent=2))

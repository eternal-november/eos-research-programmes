#!/usr/bin/env python3
"""Exact finite diagnostics; generated output is not a test fixture."""
from fractions import Fraction as F
from itertools import product
from math import comb, factorial
from pathlib import Path
import json

def expect(q,f): return sum((a*b for a,b in zip(q,f)),F(0))
def update(q,l):
    z=expect(q,l)
    return None if z==0 else [a*b/z for a,b in zip(q,l)]
def likelihood(w,x,y): return [a*x if y else 1-a*x for a in w]
def word(q,w,ys,adaptive=False):
    f=[F(1)]*len(w)
    history=[]
    for y in ys:
        x=F(1,2) if adaptive and sum(history)%2 else F(1)
        f=[a*b for a,b in zip(f,likelihood(w,x,y))]
        history.append(y)
    return expect(q,f)
def rank(rows):
    a=[list(map(F,r)) for r in rows]; r=0
    for c in range(len(a[0])):
        p=next((i for i in range(r,len(a)) if a[i][c]),None)
        if p is None: continue
        a[r],a[p]=a[p],a[r]; z=a[r][c]; a[r]=[v/z for v in a[r]]
        for i in range(len(a)):
            if i!=r:
                z=a[i][c]; a[i]=[v-z*b for v,b in zip(a[i],a[r])]
        r+=1
        if r==len(a): break
    return r

def closure(ls):
    rows=[[F(1)]*len(ls[0])]
    changed=True
    while changed:
        changed=False
        for f in rows[:]:
            for l in ls:
                v=[a*b for a,b in zip(f,l)]
                if rank(rows+[v])>len(rows): rows.append(v); changed=True
    return rows

counts={'word_pairs':0,'moment_updates':0,'rank_checks':0,'adaptive_class_words':0}
separations={}
for n in range(2,9):
    w=[F(i,n) for i in range(n+1)]
    qe=[F(comb(n,i),2**(n-1)) if i%2==0 else F(0) for i in range(n+1)]
    qo=[F(comb(n,i),2**(n-1)) if i%2 else F(0) for i in range(n+1)]
    assert sum(qe)==sum(qo)==1
    for k in range(n):
        assert expect(qe,[a**k for a in w])==expect(qo,[a**k for a in w])
        for ys in product((0,1),repeat=k):
            for adaptive in (False,True):
                assert word(qe,w,ys,adaptive)==word(qo,w,ys,adaptive)
                counts['word_pairs']+=1
    gap=abs(word(qe,w,[1]*n)-word(qo,w,[1]*n))
    assert gap==F(factorial(n),2**(n-1)*n**n)>0
    assert word(qe,w,[1]*(n-1))>0
    assert word(qe,w,[1]*n)/word(qe,w,[1]*(n-1)) != word(qo,w,[1]*n)/word(qo,w,[1]*(n-1))
    separations[n]=str(gap)
    for k in range(n+2):
        assert rank([[a**j for a in w] for j in range(k+1)])==min(k+1,n+1)
        counts['rank_checks']+=1
    assert len(closure([w,[1-a for a in w]]))==n+1
    # Traverse actual posteriors, testing nonzero and impossible events.
    for prior in (qe,qo,[F(1,n+1)]*(n+1)):
        for ys in product((0,1),repeat=4):
            q=prior
            for t,y in enumerate(ys):
                x=F(1,2) if t%2 else F(1)
                m=[expect(q,[a**j for a in w]) for j in range(n+2)]
                l=likelihood(w,x,y); r=update(q,l)
                if r is None:
                    assert (x*m[1] if y else 1-x*m[1])==0
                    break
                for j in range(n+1):
                    predicted=x*m[j+1]/(x*m[1]) if y else (m[j]-x*m[j+1])/(1-x*m[1])
                    assert expect(r,[a**j for a in w])==predicted
                    counts['moment_updates']+=1
                q=r
# Two queries and four parameter names but just three likelihood classes.
# Hidden-unit/parameter aliases need not survive into an inference interface.
ls=[[F(0),F(1,2),F(1),F(1,2)],[F(1),F(1,2),F(0),F(1,2)]]
assert len(closure(ls+[[1-v for v in l] for l in ls]))==3
q=[F(1,4)]*4; r=[F(1,4),F(1,2),F(1,4),F(0)]
for ys in product((0,1),repeat=7):
    a,b=q,r; za=zb=F(1)
    for t,y in enumerate(ys):
        query=(sum(ys[:t])+t)%2
        l=ls[query] if y else [1-v for v in ls[query]]
        pa,pb=expect(a,l),expect(b,l)
        assert pa==pb
        za*=pa;zb*=pb
        if pa==0: break
        a,b=update(a,l),update(b,l)
        assert [a[0],a[1]+a[3],a[2]]==[b[0],b[1]+b[3],b[2]]
    assert za==zb
    counts['adaptive_class_words']+=1
# Concrete closure failure, not merely a hand-coded unequal integer assertion.
w=[F(0),F(1,2),F(1)]; qe=[F(1,2),F(0),F(1,2)]; qo=[F(0),F(1),F(0)]
assert expect(qe,w)==expect(qo,w)==F(1,2)
assert expect(update(qe,w),w)==1 and expect(update(qo,w),w)==F(1,2)
report={'status':'passed','arithmetic':'exact rational','counts':counts,'horizon_separations':separations,'scope':'finite diagnostics, not formal verification'}
Path(__file__).with_name('results.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))

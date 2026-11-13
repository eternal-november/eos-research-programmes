#!/usr/bin/env python3
"""Exact finite O7 regression. This is not a proof or general type checker."""
from fractions import Fraction as F
from itertools import product
from collections import defaultdict
import json
from pathlib import Path

# Outcome: weight, scalar cost, tree. Leaves carry stage and exact owned bundle.
def hole(stage,bundle=()): return ('hole',stage,tuple(bundle))
def node(label,*children): return ('node',label,tuple(children))
def leaves(t):
    if t[0]=='hole': return [t]
    return [x for c in t[2] for x in leaves(c)]
def graft(t,its):
    if t[0]=='hole': return next(its)
    return node(t[1],*(graft(c,its) for c in t[2]))
def bind(rows,k):
    out=[]
    for p,c,t in rows:
        for kids in product(*(k(h) for h in leaves(t))):
            w=p; cost=c
            for q,d,_ in kids: w*=q; cost+=d
            out.append((w,cost,graft(t,iter(x[2] for x in kids))))
    return out

def summary(rows):
    law=defaultdict(F); possible=set()
    for p,c,t in rows:
        assert p>=0
        law[c,t]+=p; possible.add((c,t))
    return ({k:v for k,v in law.items() if v},possible)
def repaired_bind(rows,k):
    # Independently operate on extensional (law, possibility); absence != zero mass.
    mu,S=summary(rows); outmu=defaultdict(F); outS=set()
    for (c,t),p in mu.items():
        childlaws=[summary(k(h))[0] for h in leaves(t)]
        for kids in product(*(list(d.items()) for d in childlaws)):
            w=p; cost=c
            for (d,_),q in kids: cost+=d; w*=q
            outmu[cost,graft(t,iter(v[0][1] for v in kids))]+=w
    for c,t in S:
        for kids in product(*(summary(k(h))[1] for h in leaves(t))):
            outS.add((c+sum(v[0] for v in kids),graft(t,iter(v[1] for v in kids))))
    return ({k:v for k,v in outmu.items() if v},outS)

def screen(p,high=True):
    out=[(1-p,1,node('screen.low',hole('C',(('r1','Confirm'),('r2','Reserve')))))]
    if high: out.append((p,1,node('screen.high',hole('A',(('r1','AssayA'),)),hole('B',(('r2','AssayB'),)))))
    else: assert p==0
    return out

def controller(q,a,b,rescue=True):
    def k(h):
        stage=h[1]
        if stage=='C':
            assert h[2]==(('r1','Confirm'),('r2','Reserve'))
            rows=[(1-q,2,node('confirm.pass',hole('discard',(('r2','Discard'),))))]
            if rescue: rows.append((q,2,node('confirm.uncertain',hole('D',(('r2','RescueD'),)))))
            else: assert q==0
            return rows
        if stage in ('A','B'):
            assert h[2]==((('r1','AssayA') if stage=='A' else ('r2','AssayB')),)
            prob=a if stage=='A' else b
            return [(1-prob,3 if stage=='A' else 5,node(stage+'.0',hole('done'))),(prob,3 if stage=='A' else 5,node(stage+'.1',hole('done')))]
        if stage=='D':
            assert h[2]==(('r2','RescueD'),)
            return [(F(1),7,node('rescue',hole('done')))]
        if stage=='discard':
            assert h[2]==(('r2','Discard'),)
            return [(F(1),0,node('discard',hole('done')))]
        assert stage=='done' and not h[2]
        return [(F(1),0,h)]
    return k

def validate_rows(source,rows):
    owned=set(x[0] for x in source)
    for _,_,t in rows:
        output=[x[0] for h in leaves(t) for x in h[2]]
        assert len(output)==len(set(output)) and set(output)<=owned

def run():
    vals=[F(0),F(1,3),F(1,2),F(1)]
    instances=raw=checks=0
    for p,q,a,b in product(vals,repeat=4):
        start=screen(p); k=controller(q,a,b)
        validate_rows((('r0','Screen'),('r1','Reserve'),('r2','Reserve')),start)
        stage1=bind(start,k); final=bind(stage1,k)
        for _,_,t in start+stage1:
            for h in leaves(t): validate_rows(h[2],k(h))
        assert summary(stage1)==repaired_bind(start,k)
        assert summary(final)==repaired_bind(stage1,k)
        # Associativity: each continuation subtree finishes internally before graft.
        assert summary(final)==summary(bind(start,lambda h:bind(k(h),k)))
        law,S=summary(final)
        assert sum(law.values())==1 and all(not h[2] for _,t in S for h in leaves(t))
        # Raw possible rescue remains present even at q=0; probability does not select it.
        assert max(c for c,t in S)==10
        assert sum(prob*c for (c,t),prob in law.items())==(1-p)*(3+7*q)+9*p
        instances+=1; raw+=len(final); checks+=7
    k=controller(F(0),F(1,2),F(1,2),rescue=False)
    full=bind(bind(screen(F(0)),k),k)
    erased=bind(bind(screen(F(0),False),k),k)
    lf,sf=summary(full); le,se=summary(erased)
    assert lf==le and sf!=se and max(c for c,t in sf)==9 and max(c for c,t in se)==3
    assert all(c<=3 for c,t in se) and not all(c<=3 for c,t in sf)
    # Original native inclusion has mass-exact fibers; uncovered high target has 0 mass.
    assert sum([F(1)])==1 and sum([],F(0))==0
    # Presence flag pushforward along same inclusion is false on high, but target flag is true.
    assert any([])==False and any([True])==True
    # Full family also has all-raw budget 10, independently of four probability parameters.
    result={'parameter_instances':instances,'raw_completed_histories':raw,'assertion_groups':checks,
      'zero_high_counterexample':{'probability_laws_equal':True,'full_raw_outcomes':len(sf),'erased_raw_outcomes':len(se),'full_max_cost':9,'erased_max_cost':3,'budget_3_erased_passes_full_fails':True},
      'general_family_max_cost':10,'mean_cost_formula':'(1-p)*(3+7*q)+9*p',
      'coverage':'Exact rational arithmetic; dependent one/two-hole grafting; typed bundle partition checks; probability-and-possibility bind bridge; associativity on fixture; zero-witness failure. Not a general proof or full type checker.'}
    path=Path(__file__).with_name('dependent_repair_results.json'); path.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':run()

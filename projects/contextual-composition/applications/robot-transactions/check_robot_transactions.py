#!/usr/bin/env python3
"""Finite corroboration of the stated theorems, not physical validation."""
from itertools import product, permutations
import json

def comp(f,g): return tuple(f[g[x]] for x in range(len(f)))
def inv(p): return tuple(p.index(x) for x in range(len(p)))
def applyword(word,n):
    p=tuple(range(n))
    for a in word: p=comp(a,p)
    return p

def main():
    count={}
    n=3; I=tuple(range(n)); ps=list(permutations(range(n)))
    fs=list(product(range(n),repeat=n))
    checks=0
    for p in ps:
        for e in fs:
            restored=comp(inv(p),comp(e,p))
            assert (restored==e)==(comp(e,p)==comp(p,e))
            checks+=1
    count['all_three_state_single_interruption']=checks
    checks=0
    for a,b in product(ps,repeat=2):
        p=comp(b,a)
        for e,f in product(fs,repeat=2):
            actual=comp(f,comp(b,comp(e,a)))
            rhs=comp(p,comp(comp(inv(p),comp(f,p)),comp(inv(a),comp(e,a))))
            assert actual==rhs
            checks+=1
    count['all_three_state_two_interruption_factorizations']=checks
    # Four-orientation fixture and clock, 12 actual states.
    states=list(product(range(4),range(3))); idx={x:i for i,x in enumerate(states)}
    def table(fun): return tuple(idx[fun(*x)] for x in states)
    a=table(lambda q,h:((q+1)%4,h)); ai=inv(a)
    es=[table(lambda q,h,r=r,s=s:((q+r)%4,(h+s)%3)) for r,s in product(range(4),range(3))]
    word=[a,a,ai,ai]; prefixes=[]; p=tuple(range(12))
    for step in word:
        p=comp(step,p); prefixes.append(p)
        assert all(comp(e,p)==comp(p,e) for e in es)
        assert all(states[p[x]][1]==states[x][1] for x in range(12))
    histories=0; statehistories=0
    for events in product(es,repeat=4):
        for x in range(12):
            actual=baseline=x
            for step,e,p in zip(word,events,prefixes):
                actual=step[actual]
                assert states[actual][1]==states[baseline][1]
                actual=e[actual]; baseline=e[baseline]
                assert actual==p[baseline]
                assert states[actual][1]==states[baseline][1]
            assert actual==baseline
            statehistories+=1
        histories+=1
    count['fixture_abort_event_histories']=histories
    count['fixture_abort_initial_state_histories']=statehistories
    # Commit comparison, with same external history before atomic a^2.
    checks=0
    for e,f in product(es,repeat=2):
        actual=comp(f,comp(a,comp(e,a)))
        assert actual==comp(comp(a,a),comp(f,e))
        checks+=12
    count['fixture_commit_initial_state_histories']=checks
    # Exhaust all two-decision clock-adapted controllers and clock-adapted
    # environment policies drawn from three commuting displacements.
    checks=0
    options=[es[0],es[4],es[8]]
    for first,second in product(list(product([False,True],repeat=3)),repeat=2):
        for epolicy in product(range(3),repeat=3):
            for initial in range(12):
                actual=baseline=initial; p=tuple(range(12)); journal=[]
                def step(act):
                    nonlocal actual,baseline,p
                    actual=act[actual]; p=comp(act,p)
                    assert states[actual][1]==states[baseline][1]
                    event=options[epolicy[states[baseline][1]]]
                    actual=event[actual]; baseline=event[baseline]
                    assert actual==p[baseline]
                    assert states[actual][1]==states[baseline][1]
                step(a); journal.append(a)
                if not first[states[baseline][1]]:
                    step(ai); journal.pop(); result='abort'
                else:
                    step(a); journal.append(a)
                    if second[states[baseline][1]]: result='commit'
                    else:
                        step(ai); journal.pop(); step(ai); journal.pop(); result='abort'
                abstract=applyword(journal,12)[baseline]
                assert actual==abstract
                if result=='abort': assert actual==baseline
                checks+=1
    count['adaptive_controller_environment_state_histories']=checks
    reset=table(lambda q,h:(0,h)); reflect=table(lambda q,h:((-q)%4,h))
    x=idx[(0,0)]
    assert states[ai[reset[a[x]]]]==(3,0) and states[reset[x]]==(0,0)
    assert ai[reflect[a[x]]]!=reflect[x]
    assert states[a[x]][0]!=states[x][0] and ai[a[x]]==x
    # Two local failures can cancel: p=swap, e=f=constant zero on two states.
    p=(1,0); e=(0,0)
    # Instead use noncommuting permutations on three states, inverses as events.
    p=(1,0,2); e=(1,2,0); f=inv(e)
    assert comp(e,p)!=comp(p,e)
    assert comp(comp(inv(p),comp(f,p)),comp(inv(p),comp(e,p)))==comp(f,e)
    # Individually commuting choices do not justify a pose-dependent scheduler.
    plus=es[3] # displacement +1, clock +0
    choose=lambda y: es[0] if states[y][0]==0 else plus
    actual=a[x]; actual=choose(actual)[actual]; actual=ai[actual]
    baseline=choose(x)[x]
    assert actual!=baseline
    count['negative_and_scope_examples']=5
    print(json.dumps({'status':'passed','checks':count,'scope':'finite model checks; no Lean replay or physical validation'},indent=2))
if __name__=='__main__': main()

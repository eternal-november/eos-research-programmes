#!/usr/bin/env python3
"""Finite consistency tests; proofs are in Safe_Discovery_Mission_Theorem.md."""
from itertools import product, combinations
from random import Random
from collections import defaultdict
import json
from pathlib import Path


def catalogue(n, L):
    H = [('c', 0), ('c', 1)]
    H += [('u', j, k, sign) for j in range(n) for k in range(1,L+1) for sign in (0,1)]
    essential=[]
    for tab in range(16):
        f=lambda x,y:(tab>>(2*x+y))&1
        if any(f(0,y)!=f(1,y) for y in (0,1)) and any(f(x,0)!=f(x,1) for x in (0,1)):
            essential.append(tab)
    assert len(essential)==10
    H += [('b',i,j,k,l,t) for i,j in combinations(range(n),2) for k in range(1,L+1) for l in range(1,L+1) for t in essential]
    assert len(H)==2+2*n*L+10*(n*(n-1)//2)*L*L
    return H


def ev(h,c):
    if h[0]=='c': return h[1]
    if h[0]=='u': return int(c[h[1]]>=h[2]) ^ h[3]
    _,i,j,k,l,t=h
    return (t>>(2*int(c[i]>=k)+int(c[j]>=l)))&1


def scope(h):
    if h[0]=='c': return {}
    if h[0]=='u': return {h[1]:h[2]}
    return {h[1]:h[3],h[2]:h[4]}


def forest_projection(H, edges):
    """Exact signature messages with linear-degree exclusion and cycle rejection."""
    n=len(H); adj=[[] for _ in H]
    for i,j in edges:
        assert i<j
        adj[i].append(j); adj[j].append(i)
    parent=[None]*n; order=[]
    def visit(i,p):
        if parent[i] is not None:
            raise ValueError('cyclic diagnostic graph requires a different exact solver')
        parent[i]=p; order.append(i)
        for j in adj[i]:
            if j!=p: visit(j,i)
    for i in range(n):
        if parent[i] is None: visit(i,-1)
    messages={}; signatures={}; lookups=0
    def sig(i,j,h):
        k=(i,j,h)
        if k not in signatures:
            edge=edges[tuple(sorted((i,j)))]
            endpoint=0 if i<j else 1
            signatures[k]=tuple(ev(h,row[endpoint]) for row in edge)
        return signatures[k]
    def send(i,j,live):
        nonlocal lookups
        keys={sig(i,j,h) for h in live}
        sums=tuple(r[2] for r in edges[tuple(sorted((i,j)))])
        allowed=set()
        for h in H[j]:
            complement=tuple(s-x for s,x in zip(sums,sig(j,i,h)))
            lookups+=1
            if all(x in (0,1) for x in complement) and complement in keys:
                allowed.add(h)
        messages[i,j]=allowed
    # Inward pass: every subtree is processed once.
    for i in reversed(order):
        p=parent[i]
        if p!=-1:
            children=[j for j in adj[i] if parent[j]==i]
            live=[h for h in H[i] if all(h in messages[j,i] for j in children)]
            send(i,p,live)
    projections=[set() for _ in H]
    # Outward pass: exclusion uses one failure count per local function,
    # rather than intersecting degree-1 messages anew for every child.
    for i in order:
        failure={h:sum(h not in messages[j,i] for j in adj[i]) for h in H[i]}
        projections[i]={h for h in H[i] if failure[h]==0}
        for j in adj[i]:
            if parent[j]==i:
                live=[h for h in H[i] if failure[h] - int(h not in messages[j,i])==0]
                send(i,j,live)
    # Inconsistent disconnected components invalidate the whole joint relation.
    if any(not P for P in projections): projections=[set() for _ in H]
    return projections,lookups


def compatible(theta,edges):
    return all(all(ev(theta[i],ci)+ev(theta[j],cj)==s for ci,cj,s in rows) for (i,j),rows in edges.items())


def brute(H,edges):
    worlds=[t for t in product(*H) if compatible(t,edges)]
    return worlds,[{t[i] for t in worlds} for i in range(len(H))]


def main():
    rng=Random(20261029)
    nports,L=4,2
    C=list(product(range(L+1),repeat=nports)); A=list(product((0,1),repeat=nports))
    full=catalogue(nports,L)
    signatures={tuple(ev(h,c) for c in C) for h in full}
    assert len(signatures)==len(full), 'canonical catalogue has duplicate functions'
    trials=450; world_checks=0; lookup_total=0; inconsistent=0; nonproduct=0
    for trial in range(trials):
        m=rng.randint(2,6)
        H=[rng.sample(full,rng.randint(2,5)) for _ in range(m)]
        truth=[rng.choice(x) for x in H]
        edges={}
        for j in range(1,m):
            if rng.random()<0.85:
                i=rng.randrange(j)
                rows=[]
                for _ in range(rng.randint(1,4)):
                    ci=rng.choice(C); cj=rng.choice(C)
                    s=ev(truth[i],ci)+ev(truth[j],cj)
                    if trial%7==0 and rng.random()<0.3: s=rng.randrange(3)
                    rows.append((ci,cj,s))
                edges[(i,j)]=rows
        exact,P=brute(H,edges)
        Q,nlook=forest_projection(H,edges)
        assert P==Q,(trial,P,Q)
        world_checks+=__import__('math').prod(map(len,H)); lookup_total+=nlook
        inconsistent+=not bool(exact)
        if exact and __import__('math').prod(map(len,P))>len(exact): nonproduct+=1
        # Retaining all edges after global projection preserves the exact worlds.
        assert set(exact)==set(t for t in product(*P) if compatible(t,edges))
        # All observation branches on an existing edge partition persistent worlds.
        if exact and edges:
            i,j=rng.choice(list(edges)); ci=rng.choice(C); cj=rng.choice(C)
            reconstructed=[]
            for value in (0,1,2):
                E={e:list(rows) for e,rows in edges.items()}
                E[(i,j)].append((ci,cj,value))
                child,CP=brute(H,E)
                MP,_=forest_projection(H,E)
                assert CP==MP
                assert all(t in exact for t in child)
                reconstructed.extend(child)
            assert len(reconstructed)==len(exact) and set(reconstructed)==set(exact)
    # Correlation must survive projection: exactly one viable exit.
    H=[[('c',0),('c',1)],[('c',0),('c',1)]]
    E={(0,1):[((0,0,0,0),(0,0,0,0),1)]}
    worlds,P=brute(H,E)
    assert len(worlds)==2 and len(list(product(*P)))==4
    assert all(ev(t[0],C[0]) or ev(t[1],C[0]) for t in worlds)
    assert not all(ev(t[0],C[0]) or ev(t[1],C[0]) for t in product(*P))
    # Guard against silently running forest messages around a cycle.
    cyclic={(0,1):E[(0,1)],(1,2):E[(0,1)],(0,2):E[(0,1)]}
    try: forest_projection([H[0]]*3,cyclic)
    except ValueError: pass
    else: raise AssertionError('cycle accepted')
    # Recursive capped observer commutes with all permitted history updates.
    observer_cases=0
    for h in full:
        caps=scope(h)
        for c in C:
            q={j:min(c[j],ell) for j,ell in caps.items()}
            small=list(c)
            for j,x in q.items(): small[j]=x
            assert ev(h,c)==ev(h,small)
            for a in A:
                cp=tuple(min(L,x+1) if u else 0 for x,u in zip(c,a))
                qp={j:(min(ell,q[j]+1) if a[j] else 0) for j,ell in caps.items()}
                assert qp=={j:min(cp[j],ell) for j,ell in caps.items()}
                observer_cases+=1
    result={
        'status':'PASS', 'seed':20261029, 'canonical_functions':len(full),
        'forest_instances':trials,'global_assignments_checked':world_checks,
        'signature_message_lookups':lookup_total,'inconsistent_instances':inconsistent,
        'strictly_nonproduct_instances':nonproduct,
        'observer_update_cases':observer_cases,
        'exact_projection_and_retained_relation':True,
        'persistent_successor_partition':True,
        'joint_viability_marginal_counterexample':True,
        'cycle_rejected':True,
        'limitation':'Finite tests supplement, not replace, the proofs. No hardware or mission performance claim.'}
    out=Path(__file__).with_name('relational_discovery_checks.json')
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__': main()

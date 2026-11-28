#!/usr/bin/env python3
"""Exact transport-robust admission; standard library only."""
from collections import deque
from fractions import Fraction as Q
from itertools import product, combinations
import json, random

def flow(p,q,h,S):
    # Max harmful partial mass supported on observed rows S.
    n,m=len(p),len(q)
    src,sink=n+m,n+m+1
    cap=[[0]*(sink+1) for _ in range(sink+1)]
    for i in S:
        cap[src][i]=p[i]
    for j,z in enumerate(q):
        cap[n+j][sink]=z
    for i,j in h:
        cap[i][n+j]=sum(p)
    total=0
    while True:
        par={src:None}; queue=deque([src])
        while queue and sink not in par:
            u=queue.popleft()
            for v,c in enumerate(cap[u]):
                if c>0 and v not in par:
                    par[v]=u;queue.append(v)
        if sink not in par:
            return total
        path=[];v=sink
        while v!=src:
            u=par[v];path.append((u,v));v=u
        inc=min(cap[u][v] for u,v in path)
        total+=inc
        for u,v in path:
            cap[u][v]-=inc;cap[v][u]+=inc

def bounded(n,upp):
    if not upp:
        if n==0:
            yield ()
    else:
        for x in range(min(n,upp[0])+1):
            for vs in bounded(n-x,upp[1:]):
                yield (x,)+vs

def transport(p,q,support=None):
    # Complete integer feasible flows, independent of the rank implementation.
    def rec(i,left):
        if i==len(p):
            if not any(left):
                yield ()
            return
        room=tuple(x if support is None or (i,j) in support else 0
                   for j,x in enumerate(left))
        for row in bounded(p[i],room):
            for tail in rec(i+1,tuple(x-y for x,y in zip(left,row))):
                yield (row,)+tail
    return tuple(rec(0,tuple(q)))

def losses(tab,h):
    return tuple(sum(w for j,w in enumerate(row) if (i,j) in h)
                 for i,row in enumerate(tab))

def greedy(a,F):
    order=sorted(range(len(a)),key=lambda i:(-a[i],i))
    x=0
    R=0
    for k,i in enumerate(order):
        x|=1<<i
        R+=(a[i]- (a[order[k+1]] if k+1<len(a) else 0))*F[x]
    return R

def menu(p,F,eps):
    vals=[sum(v for i,v in enumerate(p) if s&(1<<i)) for s in range(len(F))]
    best=max((Q(vals[s]),s,s,Q(0)) for s in range(len(F)) if F[s]<=eps)
    for s,t in product(range(len(F)),repeat=2):
        if F[s]<eps<F[t]:
            w=Q(eps-F[s],F[t]-F[s])
            best=max(best,((1-w)*vals[s]+w*vals[t],s,t,w))
    gain,s,t,w=best
    a=tuple((1-w)*bool(s&(1<<i))+w*bool(t&(1<<i)) for i in range(len(p)))
    assert sum(c*x for c,x in zip(p,a))==gain and greedy(a,F)<=eps
    return gain,a

def vertex_max(p,ws,eps):
    """Independent exact robust LP arranged by all complete couplings."""
    n=len(p)
    inequalities=[(z,Q(eps)) for z in set(ws)]
    for i in range(n):
        a=tuple(int(j==i) for j in range(n))
        inequalities.extend(((a,Q(1)),(tuple(-x for x in a),Q(0))))
    best=Q(0)
    for chosen in combinations(inequalities,n):
        a=[[Q(x) for x in v]+[c] for v,c in chosen]
        for i in range(n):
            k=next((k for k in range(i,n) if a[k][i]),None)
            if k is None:
                break
            a[k],a[i]=a[i],a[k]
            d=a[i][i];a[i]=[x/d for x in a[i]]
            for j in range(n):
                if j!=i:
                    d=a[j][i];a[j]=[x-d*y for x,y in zip(a[j],a[i])]
        else:
            x=[v[-1] for v in a]
            if all(sum(b*c for b,c in zip(v,x))<=z for v,z in inequalities):
                best=max(best,sum(b*c for b,c in zip(p,x)))
    return best

def check(p,q,h,compare_lp=False):
    n=len(p)
    F=[flow(p,q,h,{i for i in range(n) if s&(1<<i)}) for s in range(1<<n)]
    ws=tuple(losses(x,h) for x in transport(p,q))
    assert ws
    for s,t in product(range(1<<n),repeat=2):
        assert F[s]+F[t]>=F[s|t]+F[s&t]
    for s in range(1<<n):
        assert F[s]==max(sum(w[i] for i in range(n) if s&(1<<i)) for w in ws)
    agrid=tuple(product(range(4),repeat=n))
    for a in agrid:
        assert greedy(a,F)==max(sum(x*y for x,y in zip(a,w)) for w in ws)
    # Menu supplies feasible witnesses; every discretized policy is bounded
    # by the exact menu at the same risk. General upper bound in the proof.
    service=[menu(p,F,Q(z,3))[0] for z in range(3*sum(p)+1)]
    for a in agrid:
        assert service[greedy(a,F)]>=Q(sum(x*y for x,y in zip(p,a)),3)
    if compare_lp:
        for cap in (Q(0),Q(1,2),Q(3,2),Q(sum(p))):
            assert menu(p,F,cap)[0]==vertex_max(p,ws,cap)
    return len(agrid)

def extension_checks():
    # Every partial harmful choice can be extended iff it cannot eat
    # the Hall slack of any admissible set of complete-source rows.
    n=3
    P=(1,)*n
    full=[(i,j) for i,j in product(range(n),repeat=2)]
    checks=positive=0
    for code in range(1<<(n*n)):
        E={v for i,v in enumerate(full) if code&(1<<i)}
        feasible=transport(P,P,E)
        if not feasible:
            continue
        for hint in (0o517,0o273,0o777):
            H={v for i,v in enumerate(full) if hint&(1<<i) and v in E}
            good=True
            for s in range(1<<n):
                S={i for i in range(n) if s&(1<<i)}
                N={j for i,j in E if i in S}
                cross={(i,j) for i,j in H if i not in S and j in N}
                good &= flow(P,P,cross,set(range(n))-S)<=len(N)-len(S)
            choices=[(-1,)+tuple(j for a,j in sorted(H) if a==i) for i in range(n)]
            all_partial=True
            for plan in product(*choices):
                used=[j for j in plan if j>=0]
                if len(set(used))!=len(used):
                    continue
                all_partial &= any(all(j<0 or t[i][j]==1 for i,j in enumerate(plan))
                                  for t in feasible)
            assert good==all_partial
            checks+=1
            positive+=good
    return checks,positive

def main():
    fixtures=queries=0
    for n,m in ((2,2),(3,3)):
        p,q=(1,)*n,(1,)*m
        for code in range(1<<(n*m)):
            h={(i,j) for i in range(n) for j in range(m) if code&(1<<(i*m+j))}
            queries+=check(p,q,h);fixtures+=1
    rnd=random.Random(842)
    for case in range(180):
        p,q=(1,2,3),tuple(rnd.sample([1,2,3],3))
        h={(i,j) for i,j in product(range(3),repeat=2) if rnd.randrange(2)}
        queries+=check(p,q,h,case<24);fixtures+=1

    # In a six-edge compatibility cycle the two full pairings support
    # different maxima. The prefix maximizers are not interchangeable.
    p=q=(1,1,1)
    E={(0,0),(1,1),(2,2),(0,1),(1,2),(2,0)}
    h={(0,0),(1,2),(2,0)}
    vec={losses(x,h) for x in transport(p,q,E)}
    assert vec=={(1,0,0),(0,1,1)}
    exact=[max(sum(w[i] for i in range(3) if s&(1<<i)) for w in vec) for s in range(8)]
    a=(Q(1),Q(1,2),Q(1,2))
    sharp=max(sum(x*y for x,y in zip(a,w)) for w in vec)/3
    wrongly_nested=greedy(a,exact)/3
    assert (sharp,wrongly_nested)==(Q(1,3),Q(1,2))
    assert exact[3]+exact[5]<exact[7]+exact[1]
    u=(Q(1,2),Q(1,2),Q(0));v=(Q(1,2),Q(-1,2),Q(0))
    assert all(u[i]+v[j]>=(a[i] if (i,j) in h else 0) for i,j in E)
    assert (sum(u)+sum(v))/3==sharp
    assert u[2]+v[1]<0
    new=E|{(2,1)}
    assert max(sum(x*y for x,y in zip(a,losses(t,h))) for t in transport(p,q,new))/3==Q(1,2)

    # Simple shared-risk improvement compared with independent row caps:
    # both rows share the same single uncovered-failure column.
    p,q=(2,2),(1,1,2)
    h={(0,0),(1,0)}
    Fs=[flow(p,q,h,{i for i in range(2) if s&(1<<i)}) for s in range(4)]
    optimum,policy=menu(p,Fs,Q(1,2))
    assert optimum/4==Q(1,2) and policy==(Q(1,2),Q(1,2))
    # r=1/4 comes from the carried old column. New total cap=3/8.
    assert Q(1,4)+Q(greedy(policy,Fs),4)==Q(3,8)
    assert Q(1,4)+Q(1,16)>Q(1,4)
    extension,extendable=extension_checks()
    out=dict(extension_scope_checks=extension,extension_universal_positive=extendable,fixtures=fixtures,exact_policy_queries=queries,exact_service_lp_comparisons=96,
             restricted_true=str(sharp),restricted_bad_prefix=str(wrongly_nested),
             shared_service="1/2",independent_row_service="1/4")
    print(json.dumps(out,sort_keys=True))
if __name__=="__main__":
    main()

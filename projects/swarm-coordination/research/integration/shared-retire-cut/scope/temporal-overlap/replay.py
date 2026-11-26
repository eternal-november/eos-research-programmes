#!/usr/bin/env python3
"""Integer STN load envelopes: interval antichain, event closure, full schedules."""
from random import Random
from itertools import combinations
from collections import deque
import json

INF=10**12


def close(n,edges):
    d=[[INF]*n for _ in range(n)]
    for i in range(n): d[i][i]=0
    for i,j,w in edges: d[i][j]=min(d[i][j],w)
    for k in range(n):
        for i in range(n):
            if d[i][k]==INF: continue
            for j in range(n):
                if d[k][j]!=INF: d[i][j]=min(d[i][j],d[i][k]+d[k][j])
    return d


def sat(d):
    return all(d[i][i]>=0 for i in range(len(d)))


def schedule(n,edges):
    a=[0]*n
    for _ in range(n):
        b=a.copy()
        for i,j,w in edges: b[j]=min(b[j],a[i]+w)
        if a==b:
            ans=[v-a[0] for v in a]
            assert all(ans[j]-ans[i]<=w for i,j,w in edges)
            return ans
        a=b
    return None


def flow(n,arcs,s,t):
    cap=[{} for _ in range(n)]
    for i,j,w in arcs:
        cap[i][j]=cap[i].get(j,0)+w
        cap[j].setdefault(i,0)
    total=0
    while True:
        seen={s:s}
        q=deque([s])
        while q and t not in seen:
            i=q.popleft()
            for j,w in cap[i].items():
                if w>0 and j not in seen:
                    seen[j]=i
                    q.append(j)
        if t not in seen:
            return total,set(seen)
        v=t
        c=INF
        while v!=s:
            u=seen[v]
            c=min(c,cap[u][v])
            v=u
        v=t
        while v!=s:
            u=seen[v]
            cap[u][v]-=c
            cap[v][u]+=c
            v=u
        total+=c


def eligible(d,job,t):
    e,x,_=job
    return t+d[e][0]>=0 and d[0][x]>=t+1


def before(d,a,b):
    return d[b[0]][a[1]]<=0


def bounds(jobs,S,t):
    return [(0,jobs[i][0],t) for i in S]+[(jobs[i][1],0,-t-1) for i in S]


def interval_method(d,jobs,t):
    I=[i for i,j in enumerate(jobs) if eligible(d,j,t)]
    m=len(I)
    amount=sum(jobs[i][2] for i in I)
    src,sink=2*m,2*m+1
    ed=[(src,r,jobs[i][2]) for r,i in enumerate(I)]
    ed += [(r+m,sink,jobs[i][2]) for r,i in enumerate(I)]
    ed += [(r,s+m,amount+1) for r,i in enumerate(I) for s,j in enumerate(I)
           if i!=j and before(d,jobs[i],jobs[j])]
    f,reach=flow(2*m+2,ed,src,sink)
    selected=[i for r,i in enumerate(I) if r in reach and m+r not in reach]
    assert sum(jobs[i][2] for i in selected)==amount-f
    return amount-f,selected


def event_method(d,jobs,t):
    # Maximum-weight closed set of events that may have occurred by t.
    n=len(d)
    co=[0]*n
    for e,x,w in jobs: co[e]+=w;co[x]-=w
    total=sum(max(0,w) for w in co)
    prohibit=sum(map(abs,co))+1
    A=[]
    for i in range(n):
        if co[i]>=0: A.append((n,i,co[i]))
        else: A.append((i,n+1,-co[i]))
        if d[0][i]<=t: A.append((n,i,prohibit))
        if -d[i][0]>t: A.append((i,n+1,prohibit))
        for j in range(n):
            if i!=j and d[i][j]<=0: A.append((i,j,prohibit))
    f,_=flow(n+2,A,n,n+1)
    return total-f


def exhaustive(n,edges,jobs,t):
    best=0
    J=range(len(jobs))
    count=0
    for k in range(len(jobs)+1):
        for S in combinations(J,k):
            ok=sat(close(n,edges+bounds(jobs,S,t)))
            if ok: best=max(best,sum(jobs[i][2] for i in S))
            count+=1
    return best,count


def actual(a,jobs,t):
    return sum(w for e,x,w in jobs if a[e]<=t<a[x])


def replay():
    R=Random(526)
    cases=subsets=ex=joint=updates=0
    for trial in range(200):
        m=R.randrange(2,9)
        n=2*m+1
        clocks=[0]+sum(([v,v+R.randrange(1,5)] for v in (R.randrange(9) for _ in range(m))),[])
        jobs=[(2*i+1,2*i+2,R.randrange(1,9)) for i in range(m)]
        if trial%9==0: jobs.append(jobs[0])
        es=[(x,e,-1) for e,x,_ in jobs]
        es.extend((i,j,clocks[j]-clocks[i]+R.randrange(7)) for i in range(n) for j in range(n)
                  if i!=j and R.random()<.21)
        d=close(n,es)
        assert sat(d)
        rel=[edge for edge in es if 0 not in edge[:2]]
        dr=close(n,rel)
        # Replacing absolute bounds never modifies the compiled relative graph;
        # update only the earliest/latest time vectors.
        for _ in range(3):
            new=[edge for edge in rel]
            for i in range(1,n):
                if R.random()<.55:
                    new.append((0,i,clocks[i]+R.randrange(5)))
                if R.random()<.55:
                    new.append((i,0,-clocks[i]+R.randrange(5)))
            dnew=close(n,new)
            hybrid=[row.copy() for row in dr]
            for i in range(1,n):
                up=min((w+dr[j][i] for a,j,w in new if a==0 and dr[j][i]!=INF),default=INF)
                down=min((w+dr[i][j] for j,b,w in new if b==0 and dr[i][j]!=INF),default=INF)
                assert up==dnew[0][i] and down==dnew[i][0]
                hybrid[0][i]=up
                hybrid[i][0]=down
            for t in (-3,0,3,6,9,12):
                assert interval_method(hybrid,jobs,t)[0]==interval_method(dnew,jobs,t)[0]
                updates+=1
        for t in range(-2,14):
            val,S=interval_method(d,jobs,t)
            assert val==event_method(d,jobs,t)
            wit=schedule(n,es+bounds(jobs,S,t))
            assert wit is not None and actual(wit,jobs,t)==val
            assert all(not before(d,jobs[i],jobs[j]) for i in S for j in S if i!=j)
            cases+=1
            joint+=val<sum(w for j in jobs if eligible(d,j,t) for w in [j[2]])
            if trial<75 and 1<=t<=4:
                other,c=exhaustive(n,es,jobs,t)
                assert val==other
                subsets+=c
                ex+=1
    # Two individually possible holds cannot peak together in one history.
    j=[(1,2,1),(3,4,1)]
    e=[(2,1,-1),(4,3,-1),(3,2,0)]
    assert interval_method(close(5,e),j,3)[0]==1
    # In a disjunction, every pair may occupy but the triple is impossible.
    masks=[{0,1},{0,2},{1,2}]
    assert all(any(set(s)<=w for w in masks) for s in combinations(range(3),2))
    assert max(map(len,masks))==2
    quotient=set()
    jobs=[(2*i+1,2*i+2,1) for i in range(6)]
    edges=[(x,e,-1) for e,x,_ in jobs]
    pairs=[(i,j) for i in range(3) for j in range(3,6)]
    for flags in range(1<<len(pairs)):
        more=[(jobs[j][0],jobs[i][1],0) for k,(i,j) in enumerate(pairs) if flags>>k&1]
        disc=close(13,edges+more)
        assert sat(disc) and all(eligible(disc,j,0) for j in jobs)
        signature=tuple(interval_method(disc,[jobs[i],jobs[j]],0)[0] for i,j in pairs)
        assert signature==tuple(1 if flags>>k&1 else 2 for k in range(len(pairs)))
        quotient.add(signature)
    assert len(quotient)==512
    return dict(pointwise_flow_comparisons=cases,weighted_schedule_witnesses=cases,
                absolute_window_update_comparisons=updates,
                full_constraint_subsets=subsets,exhaustive_tick_comparisons=ex,
                sum_of_individual_loads_too_high=joint,
                disjunctive_pairs_pass_triple_fails=True,
                distinct_six_job_query_signatures=len(quotient))


if __name__=="__main__":
    print(json.dumps(replay(),indent=2))

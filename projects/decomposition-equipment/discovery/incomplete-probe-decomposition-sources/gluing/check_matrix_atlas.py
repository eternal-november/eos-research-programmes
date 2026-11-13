#!/usr/bin/env python3
import numpy as np
import json
from pathlib import Path

def classify(n, edges, data):
    adj=[[] for _ in range(n)]
    for i,j in edges:adj[i].append(j);adj[j].append(i)
    d=next(iter(data.values())).shape[0]
    L={0:np.eye(d)};parity={0:0};queue=[0]
    for i in queue:
        for j in adj[i]:
            if j not in L:
                L[j]=data[i,j].T @ np.linalg.inv(L[i]).T
                parity[j]=1-parity[i];queue.append(j)
    assert len(L)==n
    S=None
    for i,j in edges:
        if parity[i]!=parity[j]:
            if not np.allclose(data[i,j],L[i]@L[j].T,atol=1e-10):return {'feasible':False,'reason':'opposite-parity cycle'},L,parity,None
        else:
            D=np.linalg.inv(L[i])@data[i,j]@np.linalg.inv(L[j]).T
            cand=D if parity[i]==0 else np.linalg.inv(D)
            if not np.allclose(cand,cand.T,atol=1e-10) or np.min(np.linalg.eigvalsh((cand+cand.T)/2))<=0:
                return {'feasible':False,'reason':'non-SPD cycle'},L,parity,None
            if S is not None and not np.allclose(S,cand,atol=1e-10):return {'feasible':False,'reason':'inconsistent SPD cycles'},L,parity,None
            S=cand
    return {'feasible':True,'gauge':'GL' if S is None else 'orthogonal'},L,parity,S

def datum(A,edges):
    out={}
    for i,j in edges:out[i,j]=A[i]@A[j].T;out[j,i]=out[i,j].T
    return out
A=[np.array([[1.2+.1*i,.12-.02*i],[.05*i,.9+.08*i]]) for i in range(6)]
cases={}
for name,n,edges in [('bipartite',4,[(0,1),(1,2),(2,3),(3,0)]),('triangle',3,[(0,1),(0,2),(1,2)]),('mixed',6,[(0,1),(1,2),(2,3),(3,4),(4,5),(0,2),(1,4),(2,5)])]:
    D=datum(A,edges);status,L,p,S=classify(n,edges,D);assert status['feasible']
    if S is not None:assert np.allclose(S,A[0]@A[0].T)
    H=A[0]
    recovered=[L[i]@(H if p[i]==0 else np.linalg.inv(H).T) for i in range(n)]
    assert all(np.allclose(recovered[i],A[i]) for i in range(n))
    # Independent local contrast bases do not affect feasibility.
    T=[np.array([[1+.03*i,.2],[.1,.8+.02*i]]) for i in range(n)]
    transformed={(i,j):T[i]@v@T[j].T for (i,j),v in D.items()}
    status2,*_=classify(n,edges,transformed);assert status2==status
    cases[name]=status
edges=[(0,1),(1,2),(2,3),(3,0)];D=datum(A,edges);D[3,0]*=2;D[0,3]=D[3,0].T
status,*_=classify(4,edges,D);assert not status['feasible'];cases['bad_four_cycle']=status
edges=[(0,1),(0,2),(1,2)];D={}
for i,j in edges:D[i,j]=np.array([[-1. if (i,j)==(1,2) else 1.]]);D[j,i]=D[i,j].T
status,*_=classify(3,edges,D);assert not status['feasible'];cases['bad_triangle_spd']=status
result={'status':'PASS','arithmetic':'floating point numpy; tolerance 1e-10','cases':cases,'scope':'matrix atlas classification and chart covariance; positivity checked by stress-family script separately'}
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

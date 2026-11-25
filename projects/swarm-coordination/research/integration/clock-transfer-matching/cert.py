"""Integer proof objects for each clock cell and cardinality."""
from fractions import Fraction as F
from itertools import product
from collections import deque
import json
from partial import *

def hall(n,G):
    adj=[[] for i in range(n)]
    for i,j in G:adj[i].append(j)
    right={}
    for u in range(n):
        seen=set()
        def aug(i):
            for j in adj[i]:
                if j not in seen:
                    seen.add(j)
                    if j not in right or aug(right[j]):
                        right[j]=i;return True
            return False
        aug(u)
    assert len(right)<n
    S=set(range(n))-set(right.values()); todo=deque(S)
    R=set()
    while todo:
        i=todo.popleft()
        for j in adj[i]:
            if j in R:continue
            R.add(j);assert j in right # maximal matching
            if right[j] not in S:S.add(right[j]);todo.append(right[j])
    assert len(R)<len(S)
    return sorted(S)

def dual(n,G,P):
    js=dict(P);v=[0]*n
    for _ in range(n):
        changed=False
        for (i,j),c in G.items():
            k=js[i];o=c-G[i,k]
            if v[j]>v[k]+o:
                v[j]=v[k]+o;changed=True
        if not changed:break
    u=[G[i,js[i]]-v[js[i]] for i in range(n)]
    assert all(u[i]+v[j]<=z for (i,j),z in G.items())
    return [u,v]

def make(n,m,A,h,k,w,a,b):
    C=[];ds=[]
    for x in cells(A):
        E={ij for ij,(l,u) in A.items() if l<=x<=u}
        for need in range(h,k+1):
            z,G=extension(n,m,need,E,w,a,b,1)
            P=assignment(z,G)
            d=dict(x=str(x),k=need)
            if P is None:d['hall']=hall(z,G)
            else:
                z,J=extension(n,m,need,E,w,a,b,-1)
                Q=assignment(z,J); assert Q is not None
                d['bounds']=[(P,dual(z,G,P)),(Q,dual(z,J,Q))]
            C.append(d)
    return dict(n=n,m=m,edges=[(i,j,str(u),str(v)) for (i,j),(u,v) in sorted(A.items())],
                h=h,k=k,w=w,a=a,b=b,claims=C)

if __name__=='__main__':
    A=intervals([0,2],[0,2],[[0,0],[0,0]],[[1,1],[1,1]],(-3,3))
    w=[[0,1],[0,0]]; a,b=[1,0],[0,0]
    V=[make(2,2,A,2,2,w,a,b),make(2,2,A,1,2,w,a,b)]
    with open('cert.json','w') as f:f.write(json.dumps(V,separators=(',',':'),sort_keys=True)+'\n')

from pathlib import Path
import sys, json, math
from itertools import pairwise
import numpy as np
from scipy.optimize import minimize
import lower,proof
Q=10**7

def bound(boxes):
    X=np.asarray(boxes,dtype=np.int64)
    a,b=X[:,0,:],X[:,1,:]
    M=(a+b)/4
    spans=list(zip(a.ravel()/2,b.ravel()/2))
    def f(z,grad=True):
        x=z.reshape(-1,3);diff=x[1:]-x[:-1]
        norm=np.sqrt(np.sum(diff**2,axis=1)+1e-9)
        uv=diff/norm[:,None]
        if not grad:return uv
        c=np.vstack(([-1.,-1.,-1.]*uv[0],uv[:-1]-uv[1:],uv[-1]))
        return norm.sum(),c.ravel()
    r=minimize(f,M.ravel(),jac=True,bounds=spans,method="L-BFGS-B",
               options=dict(maxiter=800,ftol=1.e-12))
    u=np.trunc(Q*f(r.x,False)).astype(np.int64)
    for row in u:
        while sum(int(x)**2 for x in row)>Q**2:
            i=np.argmax(abs(row));row[i]-=np.sign(row[i])
        assert sum(int(x)**2 for x in row)<=Q**2
    co=np.vstack((-u[0],u[:-1]-u[1:],u[-1]))
    n=int((co*np.where(co>=0,a,b)).sum())
    return n,u.tolist()

def paths(vertices,allowed,s,g,halt=()):
    out={i:[] for i in vertices}
    for a,b in allowed:out[a].append(b);out[b].append(a)
    def rec(prefix):
        v=prefix[-1]
        if v==g:yield prefix
        elif v not in halt:
            for n in out[v]:
                if n not in prefix:yield from rec(prefix+(n,))
    return rec((s,))


def main():
    A,lo,n=lower.bulk();_,P=lower.adjacent(A,lo)
    tasks,known,local=proof.tasks(P)
    store={}
    for key,boxes in tasks.items():
        value,vec=bound(boxes)
        assert proof.valid(boxes,vec)==value
        store[key]=vec
    print(json.dumps(store,sort_keys=True))
if __name__=="__main__":main()

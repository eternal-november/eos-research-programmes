"""Exact population-law numerical QA; not finite-data or formal verification."""
import itertools,json
import numpy as np
from pathlib import Path
rng=np.random.default_rng(27028)
states=list(itertools.product(range(2),repeat=3)); n=len(states); U=2

def partitions(seq):
    if not seq: yield []; return
    x,*rest=seq
    for p in partitions(rest):
        yield [[x]]+[b[:] for b in p]
        for j in range(len(p)):
            q=[b[:] for b in p];q[j].append(x);yield q

def canon(p):return tuple(sorted(tuple(sorted(b)) for b in p))
def refines(p,q):return all(any(set(b)<=set(c) for c in q) for b in p)
def rows(B,F,p,x):
    return np.concatenate([np.array([B[x,u,list(b)].sum() for b in p]) for u in range(U)]+[np.array([F[x,u,list(b),:].sum(axis=0) for b in p]).ravel() for u in range(U)])
def refine(B,F,p):
    while True:
        nxt=[]
        for block in p:
            groups=[]
            for x in block:
                for g in groups:
                    if np.max(abs(rows(B,F,p,x)-rows(B,F,p,g[0])))<1e-10:g.append(x);break
                else:groups.append([x])
            nxt.extend(groups)
        nxt=canon(nxt)
        if nxt==canon(p):return nxt
        p=nxt

def valid(B,F,p):return all(np.max(abs(rows(B,F,p,x)-rows(B,F,p,b[0])))<1e-10 for b in p for x in b)
def autonomous(F,p):return max(np.max(abs(F[:,:,list(b),:].sum(axis=2))) for b in p)<1e-10

def family(kind):
    B=np.zeros((n,U,n));F=np.zeros((n,U,n,2))
    for x,(a,b,y) in enumerate(states):
      for u in range(U):
        pa=.18+.13*a+.17*b+.09*a*b+.08*u
        pb=.22+.11*b+.12*a*u
        py=.25+.12*y+.06*a
        for xp,(ap,bp,yp) in enumerate(states):
          core=(pa if ap else 1-pa)*(pb if bp else 1-pb)
          B[x,u,xp]=core*(py if yp else 1-py)
          if kind=='autonomous':
            F[x,u,xp,0]=.0024*(1+.2*a*b)*(1 if yp else -1)*(1 if ap==bp else 0)
            F[x,u,xp,1]=.0018*(1+.2*b*u)*(1 if yp else -1)*(1 if ap!=bp else 0)
          else:
            F[x,u,xp,0]=.0018*(1+.2*a*b)*(1 if bp else -1)/2
            F[x,u,xp,1]=.0014*(1+.2*b*u)*(1 if ap else -1)/2
    assert np.max(abs(F.sum(axis=2)))<1e-12
    for z in itertools.product([-1,1],repeat=2): assert np.min(B+F@np.array(z))>0
    return B,F

p0=canon([[j for j,s in enumerate(states) if s[0]==a]for a in range(2)])
allp=[canon(p+q) for p in partitions(list(p0[0])) for q in partitions(list(p0[1]))]
assert len(allp)==225
out={}
for kind in ['autonomous','conditional']:
    B,F=family(kind)
    # Recover a gauge-free column space from an observed pair residual, not F itself.
    flat=F.reshape(-1,2); neighbor=rng.normal(size=(12,2))*.01
    D=flat@neighbor.T
    UU,SS,VV=np.linalg.svd(D,full_matrices=False);basis=UU[:,:2].reshape(n,U,n,2)
    p=refine(B,basis,p0)
    truths=[q for q in allp if valid(B,F,q)]
    assert p in truths and all(refines(q,p)for q in truths)
    assert p==canon([[j for j,s in enumerate(states) if s[:2]==ab]for ab in itertools.product(range(2),repeat=2)])
    auto=autonomous(basis,p)
    assert auto==(kind=='autonomous')
    if not auto:assert not any(autonomous(F,q)for q in truths)
    # Nonorthogonal gauge must leave discovery unchanged.
    T=np.array([[1.3,.2],[-.1,.8]])
    assert refine(B,F@T,p0)==p
    out[kind]={'partition':[list(b)for b in p],'valid_partitions':len(truths),'autonomy':bool(auto),'rank':int(np.sum(SS>1e-10)),'all_225_checked':True}
# Bipartite gauge preserves pair moments, independent choices do not.
A=[np.array([[.07,.01],[.00,.06]]),np.array([[.05,-.01],[.01,.08]]),np.array([[.06,.00],[.01,.05]]),np.array([[.08,.01],[-.01,.04]])]
T=np.array([[1.2,.1],[.0,.9]]); Ag=[A[i]@(T if i%2==0 else np.linalg.inv(T).T)for i in range(4)]
edges=[(0,1),(1,2),(2,3),(3,0)]
assert all(np.allclose(A[i]@A[j].T,Ag[i]@Ag[j].T)for i,j in edges)
bad=Ag.copy();bad[0]=A[0]
assert any(not np.allclose(A[i]@A[j].T,bad[i]@bad[j].T)for i,j in edges)
out['global_gauge']={'common_gauge_preserves_edges':True,'mixed_local_choices_fail':True}
print(json.dumps(out,indent=2));Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')

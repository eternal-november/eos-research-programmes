#!/usr/bin/env python3
"""Exact rational FinVect regression: genuine aggregation, dependence and Fubini.
General theorem is proved in the bundled TeX dossier, not inferred from finite tests.
"""
from fractions import Fraction as F
from itertools import product
import json
from pathlib import Path

def zero(r,c): return [[F(0) for _ in range(c)] for _ in range(r)]
def eye(n): return [[F(i==j) for j in range(n)] for i in range(n)]
def mul(a,b):
    assert len(a[0])==len(b)
    return [[sum((a[i][k]*b[k][j] for k in range(len(b))),F(0)) for j in range(len(b[0]))] for i in range(len(a))]
def kron(a,b):
    return [[x*y for x in ra for y in rb] for ra in a for rb in b]
def prod(xs):
    z=1
    for x in xs:z*=x
    return z

def offsets(ds):
    out={};n=0
    for x,d in ds.items():out[x]=n;n+=d
    return out,n

class Fam:
    def __init__(self,ds,aug=None):
        self.ds=ds;self.off,self.n=offsets(ds)
        self.aug=aug if aug is not None else [[F(1)]*self.n]

class Cell:
    def __init__(self,src,tgt,f,m):
        self.src,self.tgt,self.f,self.m=src,tgt,f,m
        assert len(m)==tgt.n and len(m[0])==src.n
        assert mul(tgt.aug,m)==src.aug
        # Coefficients outside the carrier-selected target summand vanish.
        for x,dx in src.ds.items():
            for y,dy in tgt.ds.items():
                if y!=f[x]:
                    assert all(m[tgt.off[y]+i][src.off[x]+j]==0 for i in range(dy) for j in range(dx))
    def block(self,y,x):
        return [r[self.src.off[x]:self.src.off[x]+self.src.ds[x]] for r in self.m[self.tgt.off[y]:self.tgt.off[y]+self.tgt.ds[y]]]

def put(m,b,i,j):
    for u,row in enumerate(b):
        for v,x in enumerate(row):m[i+u][j+v]=x

def compose(g,f):
    return Cell(f.src,g.tgt,{x:g.f[f.f[x]] for x in f.src.ds},mul(g.m,f.m))

def tensor(fs):
    ds={xs:prod(f.ds[x] for f,x in zip(fs,xs)) for xs in product(*(f.ds for f in fs))}
    # Augmentation on each resource tensor summand.
    out=Fam(ds);aug=[]
    for xs in ds:
        a=[[F(1)]]
        for f,x in zip(fs,xs):a=kron(a,[f.aug[0][f.off[x]:f.off[x]+f.ds[x]]])
        aug+=a[0]
    out.aug=[aug];return out

def tensorcell(cs):
    s=tensor([c.src for c in cs]);t=tensor([c.tgt for c in cs]);m=zero(t.n,s.n);f={}
    for xs in s.ds:
        ys=tuple(c.f[x] for c,x in zip(cs,xs));f[xs]=ys;b=[[F(1)]]
        for c,x,y in zip(cs,xs,ys):b=kron(b,c.block(y,x))
        put(m,b,t.off[ys],s.off[xs])
    return Cell(s,t,f,m)

def accum(p,qs):
    ds={(x,y):dx*dy for x,dx in p.ds.items() for y,dy in qs[x].ds.items()}
    out=Fam(ds);aug=[]
    for x,y in ds:
        av=[p.aug[0][p.off[x]:p.off[x]+p.ds[x]]]
        q=qs[x];aw=[q.aug[0][q.off[y]:q.off[y]+q.ds[y]]]
        aug+=kron(av,aw)[0]
    out.aug=[aug];return out

def accumcell(c,ks):
    s=accum(c.src,{x:k.src for x,k in ks.items()})
    tq={}
    for x,k in ks.items():tq[c.f[x]]=k.tgt
    t=accum(c.tgt,tq);m=zero(t.n,s.n);f={}
    for x,y in s.ds:
        z,w=c.f[x],ks[x].f[y];f[x,y]=(z,w)
        # Apply inner beta first, then the outer alpha block: two matrices.
        inner=kron(eye(c.src.ds[x]),ks[x].block(w,y))
        outer=kron(c.block(z,x),eye(ks[x].tgt.ds[w]))
        put(m,mul(outer,inner),t.off[z,w],s.off[x,y])
    return Cell(s,t,f,m)

def flatindex(coords,dims):
    z=0
    for c,d in zip(coords,dims):z=z*d+c
    return z

def fubini(ps,qs):
    s=tensor([accum(p,q) for p,q in zip(ps,qs)])
    po=tensor(ps)
    qo={xs:tensor([q[x] for q,x in zip(qs,xs)]) for xs in po.ds}
    t=accum(po,qo);m=zero(t.n,s.n);f={}
    for history in s.ds:
        xs=tuple(h[0] for h in history);ys=tuple(h[1] for h in history);f[history]=(xs,ys)
        vd=[p.ds[x] for p,x in zip(ps,xs)];wd=[q[x].ds[y] for q,x,y in zip(qs,xs,ys)]
        interleaved=[d for pair in zip(vd,wd) for d in pair]
        for coord in product(*(range(d) for d in interleaved)):
            srcindex=flatindex(coord,interleaved)
            reordered=coord[::2]+coord[1::2]
            tgtindex=flatindex(reordered,vd+wd)
            m[t.off[xs,ys]+tgtindex][s.off[history]+srcindex]=F(1)
    return Cell(s,t,f,m)

I=eye(2);P=[[F(1),F(1)],[F(0),F(0)]]
R=[[F(1,2),F(1,3)],[F(1,2),F(2,3)]]
source=Fam({'x':2,'z':2});target=Fam({'t':2})
alpha=Cell(source,target,{'x':'t','z':'t'},[I[i]+P[i] for i in range(2)])
qsource=Fam({'u':1,'v':1});qtarget=Fam({'w':2})
def beta(m):return Cell(qsource,qtarget,{'u':'w','v':'w'},m)
ks1={'x':beta(I),'z':beta(P)}
ks2={'x':beta(R),'z':beta(P)}
cs=[alpha,alpha];ks=[ks1,ks2]
ps=[c.src for c in cs];qs=[{x:k.src for x,k in kk.items()} for kk in ks]
pt=[c.tgt for c in cs];qt=[{'t':qtarget},{'t':qtarget}]
source_phi=fubini(ps,qs);target_phi=fubini(pt,qt)
# Route 1: independently accumulate each cell, tensor them, then shuffle.
left=compose(target_phi,tensorcell([accumcell(c,k) for c,k in zip(cs,ks)]))
# Route 2: shuffle source, then accumulate tensor outer and dependent tensor inner.
outer_tensor=tensorcell(cs)
inner_tensors={xs:tensorcell([kk[x] for kk,x in zip(ks,xs)]) for xs in outer_tensor.src.ds}
right=compose(accumcell(outer_tensor,inner_tensors),source_phi)
assert left.f==right.f and left.m==right.m
assert any(v.denominator>1 for row in left.m for v in row)
assert left.src.n==64 and left.tgt.n==16
# A genuinely different parallel arrow invisible on the carrier.
identity=Cell(target,target,{'t':'t'},I)
projection=Cell(target,target,{'t':'t'},P)
assert identity.f==projection.f and identity.m!=projection.m
assert mul(P,P)==P
# Native accumulation is functorial through a later noninvertible outer cell,
# with a later continuation map independent of pre-merge x as required.
qparallel=Cell(qtarget,qtarget,{'w':'w'},R)
a1=accumcell(alpha,ks1)
a2=accumcell(projection,{'t':qparallel})
composite_outer=compose(projection,alpha)
composite_inner={x:compose(qparallel,k) for x,k in ks1.items()}
direct=accumcell(composite_outer,composite_inner)
via=compose(a2,a1)
assert direct.f==via.f and direct.m==via.m
# Retained p really acts after accumulation, not just before forgetting.
p_acc=accumcell(projection,{'t':Cell(qtarget,qtarget,{'w':'w'},I)})
id_acc=accumcell(identity,{'t':Cell(qtarget,qtarget,{'w':'w'},I)})
assert p_acc.f==id_acc.f and p_acc.m!=id_acc.m
out={'status':'passed','field':'rational','fubini_matrix_shape':[16,64],
     'fubini_equal_entries':16*64,'fubini_nonzero_entries':sum(v!=0 for row in left.m for v in row),
     'fubini_contains_nonintegral_entries':True,'augmentations_checked':'every constructed cell',
     'native_accumulation_composition_shape':[direct.tgt.n,direct.src.n],
     'parallel_noninvertible_cell_retained':True,
     'fubini_matrix':[[str(v) for v in row] for row in left.m],
     'composition_matrix':[[str(v) for v in row] for row in direct.m]}
p=Path(__file__).with_suffix('.json');p.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if not k.endswith('matrix')},indent=2))

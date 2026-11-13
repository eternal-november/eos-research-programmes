#!/usr/bin/env python3
"""Exact finite regressions; all-family proof is in nonthin_categorical_test.md."""
from fractions import Fraction as F
from itertools import product
from collections import defaultdict, Counter
import json
counts = Counter()
def eq(a,b,tag):
    if a != b: raise RuntimeError((tag,a,b))
    counts[tag] += 1
def uniform(n): return {i:F(1,n) for i in range(n)}
def prod(ds):
    ans = {}
    for xs in product(*(d.keys() for d in ds)):
        p=F(1)
        for x,d in zip(xs,ds): p*=d[x]
        ans[xs]=p
    return ans
def push(d,fn):
    r=defaultdict(F)
    for x,p in d.items(): r[fn(x)]+=p
    return dict(r)
class Arrow:
    def __init__(self,inputs,context,out):
        self.inputs=tuple(inputs); self.p=context; self.o=out
        for a in self.inputs:
            eq(sum(context[a].values()),F(1),'normalized_fibre')
            if any(w<=0 for w in context[a].values()): raise RuntimeError('support')
    def labels(self):
        return sorted(set(b for a in self.inputs for x in self.p[a] for b in self.o(a,x)),key=repr)
def comp(g,f):
    ps={}; outs={}
    for a in f.inputs:
        ps[a]={}
        for x,px in f.p[a].items():
            bs=f.o(a,x)
            for ys,py in prod([g.p[b] for b in bs]).items():
                s=(x,ys); ps[a][s]=px*py
                outs[a,s]=tuple(c for b,y in zip(bs,ys) for c in g.o(b,y))
    return Arrow(f.inputs,ps,lambda a,s:outs[a,s])
def ident(xs):return Arrow(xs,{a:{None:F(1)} for a in xs},lambda a,s:(a,))
def checkcell(f,ff,u,v,alpha,tag):
    for a in f.inputs:
        eq(push(f.p[a],lambda x:alpha(a,x)),ff.p[u(a)],tag+'_mass')
        for x in f.p[a]:
            eq(tuple(map(v,f.o(a,x))),ff.o(u(a),alpha(a,x)),tag+'_output')
def hcell(f,alpha,beta):
    return lambda a,s:(alpha(a,s[0]),tuple(beta(b,y) for b,y in zip(f.o(a,s[0]),s[1])))
def associator(f,g):
    def fn(a,s):
        (x,ys),zs=s; pos=0; blocks=[]
        for b,y in zip(f.o(a,x),ys):
            n=len(g.o(b,y)); blocks.append((y,zs[pos:pos+n])); pos+=n
        eq(pos,len(zs),'assoc_consumes_all_positions')
        return (x,tuple(blocks))
    return fn
# Nonconstant fixture: base collapse, distinct fibre cardinalities, varying lengths.
A=(0,1); P={a:uniform(4+2*a) for a in A}
f=Arrow(A,P,lambda a,x:() if x%2==0 else ((a,0),(a,1),(a,0)))
fp=Arrow((0,),{0:uniform(2)},lambda a,x:() if x==0 else (0,1,0))
u=lambda a:0; v=lambda b:b[1]; alpha=lambda a,x:x%2
B=f.labels(); Q={b:uniform((b[0]+1)*(2+b[1])) for b in B}
g=Arrow(B,Q,lambda b,y:() if y%(2+b[1])==0 else ((b[0],b[1],y%(2+b[1])),))
gp=Arrow((0,1),{b:uniform(2+b) for b in (0,1)},lambda b,y:() if y==0 else ((b,y),))
w=lambda c:c[1:]; beta=lambda b,y:y%(2+b[1])
C=g.labels(); R={c:uniform((c[0]+1)*(2+c[2]%2)) for c in C}
h=Arrow(C,R,lambda c,z:((c[0],c[1],c[2],z%(2+c[2]%2)),))
Cp=gp.labels(); hp=Arrow(Cp,{c:uniform(2+c[1]%2) for c in Cp},lambda c,z:((c[0],c[1],z),))
t=lambda d:d[1:]; gamma=lambda c,z:z%(2+c[2]%2)
checkcell(f,fp,u,v,alpha,'first_cell')
checkcell(g,gp,v,w,beta,'second_cell')
checkcell(h,hp,w,t,gamma,'third_cell')
gf=comp(g,f); gpfp=comp(gp,fp); hg=comp(h,g); hpgp=comp(hp,gp)
a_b=hcell(f,alpha,beta); b_c=hcell(g,beta,gamma)
checkcell(gf,gpfp,u,w,a_b,'horizontal_cell')
l=comp(h,gf); r=comp(hg,f); lp=comp(hp,gpfp); rp=comp(hpgp,fp)
asoc=associator(f,g); asocp=associator(fp,gp)
checkcell(l,r,lambda a:a,lambda z:z,asoc,'associator')
leftcell=hcell(gf,a_b,gamma); rightcell=hcell(f,alpha,b_c)
checkcell(l,lp,u,t,leftcell,'three_stage_cell_left')
checkcell(r,rp,u,t,rightcell,'three_stage_cell_right')
for a in A:
    for s in l.p[a]:
        eq(asocp(u(a),leftcell(a,s)),rightcell(a,asoc(a,s)),'associator_naturality')
# Both units, including the empty output branches.
lf=comp(f,ident(A)); rf=comp(ident(B),f)
checkcell(lf,f,lambda a:a,lambda b:b,lambda a,s:s[1][0],'left_unit')
checkcell(rf,f,lambda a:a,lambda b:b,lambda a,s:s[0],'right_unit')
# Genuinely parallel noninvertible maps with nonconstant body and an automorphism.
X=tuple(product(range(2),repeat=3)); Y=tuple(product(range(2),repeat=2))
pf=Arrow((0,),{0:{x:F(1,8) for x in X}},lambda a,x:() if x[0]==0 else (0,1,0))
qf=Arrow((0,),{0:{x:F(1,4) for x in Y}},lambda a,x:() if x[0]==0 else (0,1,0))
pi=lambda a,x:(x[0],x[1]); rho=lambda a,x:(x[0],x[2]); flip=lambda a,x:(x[0],1-x[1])
checkcell(pf,qf,lambda a:a,lambda b:b,pi,'parallel_pi')
checkcell(pf,qf,lambda a:a,lambda b:b,rho,'parallel_rho')
checkcell(qf,qf,lambda a:a,lambda b:b,flip,'automorphism')
eq(pi(0,(1,0,1))!=rho(0,(1,0,1)),True,'parallel_distinct')
pg=comp(gp,pf); qg=comp(gp,qf)
idcell=lambda b,y:y
pic=hcell(pf,pi,idcell); rhoc=hcell(pf,rho,idcell)
checkcell(pg,qg,lambda a:a,lambda z:z,pic,'parallel_whisker_pi')
checkcell(pg,qg,lambda a:a,lambda z:z,rhoc,'parallel_whisker_rho')
eq(any(pic(0,s)!=rhoc(0,s) for s in pg.p[0]),True,'parallel_whiskers_distinct')
# Simultaneous noninvertible product and dependent-sum changes.
for n in range(5):
    spaces=[uniform(2*(i%2+2)) for i in range(n)]
    targets=[uniform(i%2+2) for i in range(n)]
    eq(push(prod(spaces),lambda xs:tuple(x%(i%2+2) for i,x in enumerate(xs))),prod(targets),'product_noninvertible')
# Flatten products for every list of block lengths <=2, number of blocks <=3.
for k in range(4):
    for lengths in product(range(3),repeat=k):
        blocks=[[uniform(2+(i+j)%2) for j in range(n)] for i,n in enumerate(lengths)]
        nested=prod([prod(b) for b in blocks]); flat=prod([d for b in blocks for d in b])
        eq(push(nested,lambda x:tuple(z for b in x for z in b)),flat,'flatten_product')
# Source-only sharing failures, stated through output distributions.
fresh=prod([uniform(2),uniform(2)])
shared=push(uniform(2),lambda x:(x,x))
def disagree(d):return sum(p for x,p in d.items() if x[0]!=x[1])
eq(disagree(fresh),F(1,2),'label_basechange_fresh_disagreement')
eq(disagree(shared),F(0),'label_basechange_shared_disagreement')
eq(fresh!=shared,True,'label_basechange_failure')
eq(fresh!=shared,True,'label_flatten_failure')
print(json.dumps({'status':'PASS','counts':dict(sorted(counts.items())), 'total_checks':sum(counts.values()),'largest_three_stage_fibre':max(map(len,l.p.values())),'shared_policy_disagreement':{'separate_labels_or_blocks':'1/2','merged_label_or_flattened_block':'0'}},indent=2))

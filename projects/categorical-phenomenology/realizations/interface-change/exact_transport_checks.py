#!/usr/bin/env python3
"""Dependency-free exact regression checks for native transport/resource claims.

Fractions throughout; failures use explicit exceptions so python -O is safe.
These finite checks supplement, rather than replace, the accompanying proofs.
"""
from fractions import Fraction as F
from itertools import product, combinations
from collections import Counter
from dataclasses import dataclass

checks = 0

def ck(ok, msg):
    global checks
    checks += 1
    if not ok:
        raise RuntimeError(msg)

def q(x): return F(x)
def mat(rows): return [[F(x) for x in row] for row in rows]
def eye(n): return [[F(i == j) for j in range(n)] for i in range(n)]
def ones(n): return [[F(1)] for _ in range(n)]
def tr(A): return list(map(list, zip(*A)))
def mm(A, B): return [[sum(a*b for a,b in zip(row,col)) for col in zip(*B)] for row in A]
def projection(items, i, n): return [[F(item[i] == j) for j in range(n)] for item in items]
def rank(A):
    B=[row[:] for row in A]; r=0
    for c in range(len(B[0])):
        p=next((j for j in range(r,len(B)) if B[j][c]),None)
        if p is None: continue
        B[r],B[p]=B[p],B[r]; a=B[r][c]; B[r]=[x/a for x in B[r]]
        for j in range(len(B)):
            if j != r:
                a=B[j][c]; B[j]=[x-a*y for x,y in zip(B[j],B[r])]
        r+=1
    return r

def stochastic(A): return all(all(x>=0 for x in row) and sum(row)==1 for row in A)

@dataclass
class Module:
    A: list
    B: list

@dataclass
class Data:
    E: list
    S: list
    modules: list
    w: list
    Q: list
    R: list
    @property
    def J(self): return len(self.R)

def data_ok(D):
    p=[sum(row) for row in D.R]
    ck(sum(p)==1, 'R mass')
    ck(stochastic(D.Q), 'Q stochastic')
    ck(mm([D.w], D.Q)[0]==[sum(col) for col in zip(*D.R)], 'global marginal')
    for i,M in enumerate(D.modules):
        ck(stochastic(M.B),'local B stochastic')
        ck([sum(row) for row in M.A]==p,'local announcement mass')
        pi=projection(D.S,i,len(M.B[0]))
        ck(mm([D.w],pi)[0]==[sum(col) for col in zip(*mm(M.A,M.B))], 'local retained marginal')

def lawful(D,T,U,L,G,e,select,C,Lk):
    for A in (U,L,G): ck(stochastic(A),'transport channel stochastic')
    ck(mm(D.Q,G)==mm(L,T.Q),'QG=LQprime')
    ck(mm([D.w],L)[0]==T.w,'w transport')
    ck(mm(mm(tr(U),D.R),G)==T.R,'R transport')
    for k,i in enumerate(select):
        Mi=D.modules[i]; Mk=T.modules[k]
        ck(all(sum(row)==1 and set(row)<= {F(0),F(1)} for row in C[k]),'C deterministic')
        for h,hs in enumerate(D.E):
            ck(C[k][hs[i]][T.E[e[h]][k]]==1,'tuple square')
        pi=projection(D.S,i,len(Mi.B[0])); pip=projection(T.S,k,len(Mk.B[0]))
        ck(mm(pi,Lk[k])==mm(L,pip),'retained projection square')
        ck(mm(Mi.B,Lk[k])==mm(C[k],Mk.B),'local row square')
        ck(mm(mm(tr(U),Mi.A),C[k])==Mk.A,'local root square')

def native(D,A,B,f):
    ck(stochastic(B),'implementation B stochastic')
    ck(all(x>=0 for row in A for x in row),'implementation A nonnegative')
    for i,M in enumerate(D.modules):
        fi=[[F(D.E[h][i]==u) for u in range(len(M.B))] for h in f]
        ck(mm(A,fi)==M.A,'native local roots')
        ck(mm(B,projection(D.S,i,len(M.B[0])))==mm(fi,M.B),'native local rows')
    AB=mm(A,B)
    ck([sum(col) for col in zip(*AB)]==D.w,'native w')
    ck(mm(AB,D.Q)==D.R,'native R')

def arrow(D,X,Y,C):
    A,B,f=X; Ap,Bp,fp=Y
    return stochastic(C) and mm(A,C)==Ap and mm(C,Bp)==B and all(not C[v][vp] or f[v]==fp[vp] for v in range(len(f)) for vp in range(len(fp)))

def tensor(D,X):
    A,B,f=X
    return [[[sum(A[j][v]*B[v][s] for v in range(len(f)) if f[v]==h) for s in range(len(D.S))] for h in range(len(D.E))] for j in range(D.J)]

# Sparse exact polynomials. Monomials are sorted tuples of variable names.
class P:
    def __init__(self, x=0):
        self.t=dict(x) if isinstance(x,dict) else ({():F(x)} if x else {})
        self.t={m:F(c) for m,c in self.t.items() if c}
    def __add__(self,o):
        o=o if isinstance(o,P) else P(o); z=self.t.copy()
        for m,c in o.t.items(): z[m]=z.get(m,F(0))+c
        return P(z)
    __radd__=__add__
    def __neg__(self): return P({m:-c for m,c in self.t.items()})
    def __sub__(self,o): return self+-P(o) if not isinstance(o,P) else self+-o
    def __rsub__(self,o): return P(o)+-self
    def __mul__(self,o):
        o=o if isinstance(o,P) else P(o); z={}
        for m,c in self.t.items():
            for n,d in o.t.items():
                k=tuple(sorted(m+n)); z[k]=z.get(k,F(0))+c*d
        return P(z)
    __rmul__=__mul__
    def __pow__(self,n):
        z=P(1)
        for _ in range(n): z=z*self
        return z
    def derivative(self,x):
        z={}
        for m,c in self.t.items():
            n=m.count(x)
            if n:
                k=list(m); k.remove(x); k=tuple(k); z[k]=z.get(k,F(0))+n*c
        return P(z)
    def at(self,x):
        ans=F(0)
        for m,c in self.t.items():
            for name in m: c*=x[name]
            ans+=c
        return ans
    def subst(self,subst):
        ans=P()
        for m,c in self.t.items():
            term=P(c)
            for name in m: term=term*subst.get(name,var(name))
            ans+=term
        return ans
    def __eq__(self,o): return self.t==(o.t if isinstance(o,P) else P(o).t)

def var(name): return P({(name,):F(1)})

def objective(D,K):
    names=[]; res=[]
    def V(name):
        if name not in names: names.append(name)
        return var(name)
    d={(v,h):V(f'd_{v}_{h}') for v in range(K) for h in range(len(D.E))}
    eta={v:V(f'eta_{v}') for v in range(K)}
    a={(j,v):V(f'a_{j}_{v}') for j in range(D.J) for v in range(K)}
    rho={(j,v):V(f'rho_{j}_{v}') for j in range(D.J) for v in range(K)}
    sigma={(j,v):V(f'sigma_{j}_{v}') for j in range(D.J) for v in range(K)}
    b={(v,s):V(f'b_{v}_{s}') for v in range(K) for s in range(len(D.S))}
    tau={(v,s):V(f'tau_{v}_{s}') for v in range(K) for s in range(len(D.S))}
    e={v:sum(d[v,h] for h in range(len(D.E))) for v in range(K)}
    def add(label,p): res.append((label,p if isinstance(p,P) else P(p)))
    for v in range(K):
        for h in range(len(D.E)): add(('D',v,h),d[v,h]**2-d[v,h])
        add(('H',v),1-e[v]-eta[v]**2)
        for j in range(D.J):
            add(('P',j,v),a[j,v]-rho[j,v]**2)
            add(('G',j,v),e[v]-a[j,v]-sigma[j,v]**2)
        for s in range(len(D.S)): add(('T',v,s),b[v,s]-tau[v,s]**2)
        add(('N',v),sum(b[v,s] for s in range(len(D.S)))-e[v])
        for i,M in enumerate(D.modules):
            for x in range(len(M.B[0])):
                add(('C',v,i,x),sum(b[v,s] for s in range(len(D.S)) if D.S[s][i]==x)-sum(d[v,h]*M.B[D.E[h][i]][x] for h in range(len(D.E))))
    for i,M in enumerate(D.modules):
        for j in range(D.J):
            for u in range(len(M.B)):
                add(('L',i,j,u),sum(a[j,v]*sum(d[v,h] for h in range(len(D.E)) if D.E[h][i]==u) for v in range(K))-M.A[j][u])
    for s in range(len(D.S)):
        add(('W',s),sum(a[j,v]*b[v,s] for j in range(D.J) for v in range(K))-D.w[s])
    for j in range(D.J):
        for u in range(len(D.Q[0])):
            add(('O',j,u),sum(a[j,v]*b[v,s]*D.Q[s][u] for v in range(K) for s in range(len(D.S)))-D.R[j][u])
    return sum((r*r for _,r in res),P()),res,names

def singleton(H=1):
    return Data([(h,) for h in range(H)],[(0,)],[Module(mat([[F(1,H)]*H]),mat([[1]]*H))],[F(1)],mat([[1]]),mat([[1]]))

# 1. The smallest strict drop: two required occurrences -> one.
D=singleton(2); T=singleton(1)
for Z in (D,T): data_ok(Z)
lawful(D,T,eye(1),eye(1),eye(1),[0,0],[0],[ones(2)],[eye(1)])
X=(mat([[F(1,2),F(1,2)]]),ones(2),[0,1]); Y=(mat([[1]]),mat([[1]]),[0])
native(D,*X); native(T,*Y)
FX=(X[0],X[1],[0,0]); native(T,*FX)
ck(arrow(T,FX,Y,ones(2)),'collapse arrow')
ck(arrow(T,Y,FX,mat([[F(1,2),F(1,2)]])),'split posterior arrow')
ck(mm(ones(2),mat([[F(1,2),F(1,2)]]))!=eye(2),'not an isomorphism')
print('PASS smallest occurrence-erasure strict drop: kappa 2 -> 1')

# 2-4. Correlation-memory examples, with and without full support.
for eps in (F(0),F(1,2)):
    S=list(product(range(2),repeat=2))
    beta=[[((1-eps)/2 if y==(x+j)%2 else 0)+eps/4 for x,y in S] for j in range(2)]
    R=[[x/2 for x in row] for row in beta]
    M=Module(mat([[F(1,2)],[F(1,2)]]),mat([[F(1,2),F(1,2)]]))
    D=Data([(0,0)],S,[M,M],[F(1,4)]*4,eye(4),R); data_ok(D)
    X=(mat([[F(1,2),0],[0,F(1,2)]]),beta,[0,0]); native(D,*X)
    ck(rank(R)==2,'source rank2')
    ck(R[0][0]*R[1][1]-R[0][1]*R[1][0]==(1-eps)/16,'exact 2x2 minor')
    L=projection(S,0,2)
    T=Data([(0,)],[(0,),(1,)],[M],[F(1,2)]*2,eye(2),mat([[F(1,4)]*2]*2)); data_ok(T)
    lawful(D,T,eye(2),L,L,[0],[0],[eye(1)],[eye(2)])
    FX=(X[0],mm(X[1],L),[0,0]); native(T,*FX)
    Y=(mat([[F(1,2)],[F(1,2)]]),mat([[F(1,2),F(1,2)]]),[0]); native(T,*Y)
    chi=[[F(j==jp) for j in range(2)] for jp in range(2)]
    ck(chi==eye(2),'chi is identity')
    ck(arrow(T,FX,FX,chi),'chi valid native arrow')
    ck(rank(T.R)==1,'restricted rank1')
    # Erase announcement but retain the entire retained law.
    Mt=Module(mat([[1]]),M.B)
    Ta=Data(D.E,D.S,[Mt,Mt],D.w,D.Q,[D.w]); data_ok(Ta)
    lawful(D,Ta,ones(2),eye(4),eye(4),[0],[0,1],[eye(1),eye(1)],[eye(2),eye(2)])
    FXa=(mm(tr(ones(2)),X[0]),X[1],X[2]); native(Ta,*FXa)
    Ya=(mat([[1]]),[D.w],[0]); native(Ta,*Ya)
    ck(arrow(Ta,Ya,FXa,mat([[F(1,2),F(1,2)]])),'announcement posterior valid')
    ck(not arrow(Ta,FXa,Ya,ones(2)),'no forward collapse under announcement erasure')
    # Erase output only: target optimum lies in another tensor fibre.
    To=Data(D.E,D.S,D.modules,D.w,ones(4),mat([[F(1,2)],[F(1,2)]])); data_ok(To)
    lawful(D,To,eye(2),eye(4),ones(4),[0],[0,1],[eye(1),eye(1)],[eye(2),eye(2)])
    Yo=(mat([[F(1,2)],[F(1,2)]]),[D.w],[0]); native(To,*Yo); native(To,*X)
    ck(tensor(To,X)!=tensor(To,Yo),'distinct target tensor fibres')
print('PASS correlation restriction, chi isomorphism, and two failed optimizer comparisons')

# 5. Lossy retained interface with lawful recovery and no resource drop.
D=Data([(0,),(1,)],[(0,),(1,)],[Module(mat([[F(1,2),F(1,2)]]),mat([[F(1,2),F(1,2)]]*2))],[F(1,2)]*2,eye(2),mat([[F(1,2),F(1,2)]]))
T=singleton(2)
for Z in (D,T): data_ok(Z)
lawful(D,T,eye(1),ones(2),ones(2),[0,1],[0],[eye(2)],[ones(2)])
addfair=mat([[F(1,2),F(1,2)]])
lawful(T,D,eye(1),addfair,addfair,[0,1],[0],[eye(2)],[addfair])
ck(mm(ones(2),addfair)!=eye(2),'retained channels not inverses on entire simplex')
ck(mm(mm(D.modules[0].B,ones(2)),addfair)==D.modules[0].B,'recovery on all allowed continuation rows')
print('PASS lawful recovery through a noninvertible retained channel: kappa 2 = 2')

# 6. No comparison-natural optimum selection even under a datum automorphism.
H=list(product(range(2),repeat=2))
M=Module(mat([[F(1,2),F(1,2)]]),ones(2))
D=Data(H,[(0,0)],[M,M],[F(1)],mat([[1]]),mat([[1]])); data_ok(D)
swap=mat([[0,1],[1,0]]); e=[H.index((u,1-v)) for u,v in H]
lawful(D,D,eye(1),eye(1),eye(1),e,[0,1],[eye(2),swap],[eye(1),eye(1)])
valid=[]
for pair in combinations(range(4),2):
    if all({H[h][i] for h in pair}=={0,1} for i in range(2)): valid.append(pair)
ck(valid==[(0,3),(1,2)],'only minimum supports are diagonal and antidiagonal')
Xd=(mat([[F(1,2),F(1,2)]]),ones(2),[0,3]); Xa=(Xd[0],Xd[1],[1,2])
native(D,*Xd); native(D,*Xa)
FX=(Xd[0],Xd[1],[e[h] for h in Xd[2]]); native(D,*FX)
ck(FX==Xa,'automorphism exchanges optimal implementations')
ck(tensor(D,Xd)!=tensor(D,FX),'no comparison because tensors differ')
for t in (F(0),F(1,4),F(1,2)):
    alpha=[t,F(1,2)-t,F(1,2)-t,t]
    pushed=[F(0)]*4
    for h,a in enumerate(alpha): pushed[e[h]]=a
    tp=F(1,2)-t
    ck(pushed==[tp,F(1,2)-tp,F(1,2)-tp,tp],'automorphism t -> 1/2-t')
    ck(sum(a>0 for a in alpha)==(4 if t==F(1,4) else 2),'cost of endpoint/invariant tensor')
ck(F(1,4)==F(1,2)-F(1,4),'unique invariant parameter')
print('PASS exact symmetry obstruction to comparison-natural optimum selection')

# 7. Entire unweighted quartic fails gradient equivariance under output erasure.
D=singleton(); D.Q=mat([[F(1,2),F(1,2)]]); D.R=mat([[F(1,2),F(1,2)]])
T=singleton()
for Z in (D,T): data_ok(Z)
lawful(D,T,eye(1),eye(1),ones(2),[0],[0],[eye(1)],[eye(1)])
phi,rs,names=objective(D,1); phip,rsp,namesp=objective(T,1)
ck(names==namesp,'identity coordinate interface')
ab=var('a_0_0')*var('b_0_0')-1
ck(phip-phi==F(1,2)*ab**2,'exact objective discrepancy polynomial')
x={name:F(0) for name in names}; x.update(d_0_0=F(1),b_0_0=F(1),sigma_0_0=F(1),tau_0_0=F(1))
ck(phi.at(x)==F(5,2) and phip.at(x)==3,'exact offzero losses')
g={name:phi.derivative(name).at(x) for name in names}; gp={name:phip.derivative(name).at(x) for name in names}
ck({k:v for k,v in g.items() if v}=={'a_0_0':F(-5)},'source gradient')
ck({k:v for k,v in gp.items() if v}=={'a_0_0':F(-6)},'target gradient')
xzero={name:F(0) for name in names}; xzero.update(d_0_0=F(1),a_0_0=F(1),rho_0_0=F(1),b_0_0=F(1),tau_0_0=F(1))
ck(phi.at(xzero)==0 and phip.at(xzero)==0,'both K1 problems feasible')
print('PASS actual K=1 quartic gradient non-equivariance: losses 5/2,3; gradients -5,-6')

# 8. Selector-merging lift preserves zeros but not fields (both K2 budgets feasible).
D=singleton(2); T=singleton(1)
phi,rs,names=objective(D,2); phip,rsp,namesp=objective(T,2)
x={name:F(0) for name in names}; x.update(d_0_0=F(1),a_0_0=F(1),rho_0_0=F(1),b_0_0=F(1),tau_0_0=F(1),eta_1=F(1))
y={name:x[name] for name in namesp}
for v in range(2): y[f'd_{v}_0']=x[f'd_{v}_0']+x[f'd_{v}_1']
ck(phi.at(x)==F(1,2) and phip.at(y)==0,'selector-merging loss discrepancy')
g={name:phi.derivative(name).at(x) for name in names}
ck({k:v for k,v in g.items() if v}=={'d_0_0':F(1),'d_0_1':F(-1),'a_0_0':F(1)},'source selector gradient')
pushed={name:-g[name] for name in namesp}
for v in range(2): pushed[f'd_{v}_0']=-g[f'd_{v}_0']-g[f'd_{v}_1']
ck({k:v for k,v in pushed.items() if v}=={'a_0_0':F(-1)},'pushforward field nonzero')
ck(all(phip.derivative(name).at(y)==0 for name in namesp),'target field zero')
print('PASS zero-preserving selector lift need not intertwine gradient fields')

# 9. Positive residual minima are not resource invariants, including K>=1.
D=singleton(); D.modules[0].A=mat([[F(1,2)],[F(1,2)]]); D.R=mat([[F(1,2)],[F(1,2)]])
T=singleton(); data_ok(D);data_ok(T)
lawful(D,T,ones(2),eye(1),eye(1),[0],[0],[eye(1)],[eye(1)])
ck(objective(D,0)[0]==2 and objective(T,0)[0]==3,'K0 minima 2 -> 3')
# Excluding a positive occurrence is permitted input and passes cheap checks.
D=singleton(2);D.E=[(0,)]
T=Data([(0,0)],[(0,0)],D.modules*2,D.w,D.Q,D.R)
for Z in (D,T): data_ok(Z)
lawful(D,T,eye(1),eye(1),eye(1),[0],[0,0],[eye(2),eye(2)],[eye(1),eye(1)])
lawful(T,D,eye(1),eye(1),eye(1),[0],[0],[eye(2)],[eye(1)])
for K in (1,2,3):
    phi,rs,names=objective(D,K); phip,rsp,namesp=objective(T,K)
    ck(names==namesp,'module duplication keeps variables')
    extra=sum((r*r for lab,r in rs if lab[0] in ('C','L')),P())
    ck(phip-phi==extra,'module duplication adds local residual squares')
    missing=[r for lab,r in rs if lab==('L',0,0,1)]
    ck(missing==[P(F(-1,2))],'excluded occurrence residual is constant')
    rest=sum((r*r for lab,r in rs if lab[0] in ('C','L') and lab!=('L',0,0,1)),P())
    ck(phip-phi==rest+F(1,4),'pointwise lower bound difference at least 1/4')
print('PASS exact minimum-loss increase: K0 2 -> 3; every K>=1 duplication gap >= 1/4')

# 10. Signed-zero family used in the no-C1 core-lift obstruction.
# Evaluate radicals exactly from their squares. Every monomial involving an
# auxiliary in the residuals/loss has even auxiliary exponent, so this is exact
# evaluation in the corresponding real algebraic extension, not approximation.
def at_squared_aux(poly,core,squared):
    ans=F(0)
    for mon,c in poly.t.items():
        for name,n in Counter(mon).items():
            if name in squared:
                ck(n%2==0,'only even auxiliary exponents in zero checks')
                c*=squared[name]**(n//2)
            else: c*=core[name]**n
        ans+=c
    return ans
D=singleton(); D.modules[0].A=mat([[F(1,2)],[F(1,2)]]); D.R=mat([[F(1,2)],[F(1,2)]])
T=singleton(); data_ok(D);data_ok(T)
lawful(D,T,ones(2),eye(1),eye(1),[0],[0],[eye(1)],[eye(1)])
phi,rs,names=objective(D,2);phip,rsp,namesp=objective(T,2)
for r1,r2 in ((F(0),F(0)),(F(1,10),F(0)),(F(0),F(-1,10)),(F(1,10),F(-1,5)),(F(1,4),F(1,3))):
    core={};sq={}
    for v in range(2):
        core[f'd_{v}_0']=F(1);core[f'b_{v}_0']=F(1)
        sq[f'eta_{v}']=F(0);sq[f'tau_{v}_0']=F(1)
    for j,r in enumerate((r1,r2)):
        for v,a in enumerate((r*r,F(1,2)-r*r)):
            core[f'a_{j}_{v}']=a;sq[f'rho_{j}_{v}']=a;sq[f'sigma_{j}_{v}']=1-a
    ck(all(a>=0 for a in sq.values()),'source radical squares nonnegative')
    ck(all(at_squared_aux(r,core,sq)==0 for _,r in rs),'all signed-family source residuals zero')
    corep={k:v for k,v in core.items() if not k.startswith('a_')};sqp={}
    for v in range(2):
        ap=core[f'a_0_{v}']+core[f'a_1_{v}'];corep[f'a_0_{v}']=ap
        sqp[f'eta_{v}']=0;sqp[f'tau_{v}_0']=1;sqp[f'rho_0_{v}']=ap;sqp[f'sigma_0_{v}']=1-ap
    ck(sqp['rho_0_0']==r1*r1+r2*r2,'target root square is squared Euclidean norm')
    ck(all(a>=0 for a in sqp.values()),'target radical squares nonnegative')
    ck(all(at_squared_aux(r,corep,sqp)==0 for _,r in rsp),'all target family residuals zero')
print('PASS no-C1-lift signed-zero family at five exact radical samples')

# 11. K1 positive minimum increases under genuine announcement erasure.
# The all-real inequality is proved analytically in the notes/report; these
# exact evaluations regress the elimination formula and branch arithmetic.
def pos(x): return max(F(0),x)
def neg(x): return min(F(0),x)
def reduced_at(D,K,core):
    phi,rs,names=objective(D,K);sq={}
    for v in range(K):
        e=sum(core[f'd_{v}_{h}'] for h in range(len(D.E)))
        sq[f'eta_{v}']=pos(1-e)
        for j in range(D.J):
            a=core[f'a_{j}_{v}'];sq[f'rho_{j}_{v}']=pos(a);sq[f'sigma_{j}_{v}']=pos(e-a)
        for s in range(len(D.S)):sq[f'tau_{v}_{s}']=pos(core[f'b_{v}_{s}'])
    return at_squared_aux(phi,core,sq)
def target_reduced(d,a,b):
    return (d*d-d)**2+pos(d-1)**2+neg(a)**2+pos(a-d)**2+neg(b)**2+2*(b-d)**2+(a*d-F(1,2))**2+F(1,4)+2*(a*b-1)**2
D=singleton(2);D.E=[(0,)];D.modules[0].A=mat([[F(1,4),F(1,4)]]*2);D.R=mat([[F(1,2)]]*2)
T=singleton(2);T.E=[(0,)]
for Z in (D,T):data_ok(Z)
lawful(D,T,ones(2),eye(1),eye(1),[0],[0],[eye(2)],[eye(1)])
points=[(-2,1,1),(F(-1,2),-2,-1),(1,-2,F(1,2)),(F(-1,2),2,-1),(F(1,2),F(-1,4),2),(2,3,-1),(-2,-3,-2),(0,-1,-1),(0,0,0),(F(1,2),F(3,4),1)]
for d,a,b in points:
    d,a,b=map(F,(d,a,b));core={'d_0_0':d,'a_0_0':a,'b_0_0':b}
    ck(reduced_at(T,1,core)==target_reduced(d,a,b),'exact target slack elimination')
    ck(target_reduced(abs(d),abs(a),abs(b))<=target_reduced(d,a,b),'absolute value minimizer reduction samples')
    ck(pos(abs(a)-abs(d))**2<=neg(a)**2+pos(a-d)**2,'root positivity and gate grouped inequality')
for d,a,b in [(0,0,0),(0,1,1),(F(1,2),F(1,4),1),(F(1,2),F(3,4),1),(F(1,2),1,1),(F(1,2),2,1),(1,3,2),(2,5,F(1,4))]:
    d,a,b=map(F,(d,a,b));sourcecore={'d_0_0':d,'a_0_0':a/2,'a_1_0':a/2,'b_0_0':b}
    source=reduced_at(D,1,sourcecore);target=target_reduced(d,a,b)
    gap=pos(a-d)**2-2*pos(a/2-d)**2+F(1,2)*(a*d-F(1,2))**2+F(1,8)+F(1,2)*(a*b-1)**2
    ck(target-source==gap,'exact reduced announcement-erasure gap formula')
    ck(pos(a-d)**2>=2*pos(a/2-d)**2,'nonnegative core gate inequality')
    ck(gap>=F(1,8),'minimum gap certificate samples')
print('PASS K=1 announcement-erasure reduced objective and analytic-gap regression identities')
print(f'ALL {checks} EXACT CHECKS PASSED')



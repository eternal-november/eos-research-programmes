"""Exact rational cut-kernel and reconstruction checks."""
from __future__ import annotations
from fractions import Fraction as F
from itertools import product
from hashlib import sha256
from pathlib import Path
import argparse,json,sys

HERE=Path(__file__).resolve().parent
if sys.flags.optimize:raise RuntimeError('Unoptimized Python required')
def need(x,m):
    if not x:raise AssertionError(m)
def mat(a):return [[F(x) for x in row] for row in a]
def transpose(a):return [list(c) for c in zip(*a)]
def mul(a,b):
    bt=transpose(b)
    return [[sum((x*y for x,y in zip(row,col)),F(0)) for col in bt] for row in a]
def add(a,b):return [[x+y for x,y in zip(r,s)] for r,s in zip(a,b)]
def neg(a):return [[-x for x in r] for r in a]
def mv(a,v):return [sum((x*y for x,y in zip(row,v)),F(0)) for row in a]
def norm1(v):return sum(map(abs,v),F(0))
def operator1(a):return max((norm1(col) for col in transpose(a)),default=F(0))

def rref(a):
    a=mat(a);cols=len(a[0]);pivot=[];row=0
    for col in range(cols):
        selected=next((i for i in range(row,len(a)) if a[i][col]),None)
        if selected is None:continue
        a[row],a[selected]=a[selected],a[row]
        divisor=a[row][col];a[row]=[x/divisor for x in a[row]]
        for i in range(len(a)):
            if i!=row:
                scale=a[i][col];a[i]=[x-scale*y for x,y in zip(a[i],a[row])]
        pivot.append(col);row+=1
        if row==len(a):break
    return a,pivot

def nullspace(a):
    rr,piv=rref(a);n=len(a[0]);out=[]
    for free in range(n):
        if free in piv:continue
        v=[F(0)]*n;v[free]=1
        for row,col in enumerate(piv):v[col]=-rr[row][free]
        need(all(x==0 for x in mv(a,v)),'Computed vector is not in kernel')
        out.append(v)
    return out

def solve(a,b):
    n=len(a[0]);rr,piv=rref([list(row)+[v] for row,v in zip(a,b)])
    if n in piv:return None
    x=[F(0)]*n
    for row,col in enumerate(piv):x[col]=rr[row][-1]
    need(mv(a,x)==list(b),'Linear reconstruction failed')
    return x

def factor(Au,Tu):
    rows=[]
    for t in Tu:
        d=solve(transpose(Au),t)
        if d is None:return None
        rows.append(d)
    need(mul(rows,Au)==mat(Tu),'Factor does not compose')
    return rows

def envelope(Ar,Au,Tr,Tu,Tj=None):
    Ar,Au,Tr,Tu=map(mat,(Ar,Au,Tr,Tu))
    if Tj is None:Tj=[[F(0)]*len(Au) for _ in Tu]
    D=factor(Au,Tu)
    if D is None:
        witness=next(v for v in nullspace(Au) if any(mv(Tu,v)))
        return dict(factorable=False,hidden_kernel=witness,harm=mv(Tu,witness))
    B=add(Tr,neg(mul(D,Ar)));C=add(mat(Tj),D)
    return dict(factorable=True,D=D,B=B,C=C,kappa=operator1(B),residual_kappa=operator1(C))

def theorem_checks():
    count=0;positive=0;negative=0
    for entries in product((-1,0,1),repeat=4):
        A=mat([entries[:2],entries[2:]])
        for t in product((-1,0,1),repeat=2):
            T=mat([t]);D=factor(A,T)
            kernels=nullspace(A)
            annihilates=all(not any(mv(T,v)) for v in kernels)
            need((D is not None)==annihilates,'Row factor and kernel criterion disagree')
            if D is not None:positive+=1
            else:negative+=1
            count+=1
    return dict(exhaustive_two_by_two_pairs=count,factorable=positive,obstructed=negative)

def concrete_cases():
    cases={}
    cases['single_reference']=envelope([[1]],[[1]],[[1],[0]],[[0],[1]])
    need(cases['single_reference']['kappa']==2,'Single-electrode exposure factor changed')
    cases['reference_short']=envelope([[1,1]],[[1]],[[1,0],[0,1],[0,0]],[[0],[0],[1]])
    need(cases['reference_short']['kappa']==2,'Short current was omitted')
    cases['explicit_external_charge']=envelope([[1]],[[1]],[[1],[0],[0]],[[0],[1],[0]],[[0],[0],[-1]])
    need(cases['explicit_external_charge']['residual_kappa']==2,'External charge exposure lost')
    cases['parallel_unmeasured_references']=envelope([[1]],[[1,1]],[[1],[0],[0]],[[0,0],[1,0],[0,1]])
    need(not cases['parallel_unmeasured_references']['factorable'],'Hidden capacitive circulation was accepted')
    cases['two_necks_from_net_only']=envelope([[-1]],[[1,1]],[[0],[0]],[[1,0],[0,1]])
    need(not cases['two_necks_from_net_only']['factorable'],'Net current erased actual contacts')
    # Unknown active final current u=n-g1-g2. Expose u,g1,g2.
    cases['one_active_final_port']=envelope([[-1,1,1]],[[1]],[[0,0,0],[0,1,0],[0,0,1]],[[1],[0],[0]])
    B=cases['one_active_final_port']['B']
    need([norm1(c) for c in transpose(B)]==[1,2,2],'DC active-port coefficient changed')
    cases['two_active_final_ports']=envelope([[-1]],[[1,1]],[[0],[0]],[[1,0],[0,1]])
    need(not cases['two_active_final_ports']['factorable'],'Two active ports were silently one')
    # Three actual strands, assigned one each to a distinct electrode except
    # the last two share electrode1. Cap current is reconstructed per electrode.
    A=[[1,0,0],[0,1,1]]
    Tr=A+[[0,0,0],[0,0,0]];Tu=[[0,0],[0,0],[1,0],[0,1]]
    cases['distinct_electrode_sum']=envelope(A,[[1,0],[0,1]],Tr,Tu)
    need(cases['distinct_electrode_sum']['kappa']==2,'Per-contact identities lost under aggregate bound')
    # A single counted route entering one Z and leaving another has two
    # incidences and needs a different physical weight, not the old factor2.
    cases['one_route_two_contacts']=envelope([[1],[-1]],[[1,0],[0,1]],[[1],[-1],[0],[0]],[[0,0],[0,0],[1,0],[0,1]])
    need(cases['one_route_two_contacts']['kappa']==4,'Co-reaching route multiplicity disappeared')
    checked=0
    for name,c in cases.items():
        if not c['factorable']:continue
        B,C=c['B'],c['C']
        for r in product((-1,0,1),repeat=len(B[0])):
            for j in product((-1,0,1),repeat=len(C[0])):
                e=[x+y for x,y in zip(mv(B,r),mv(C,j))]
                need(norm1(e)<=c['kappa']*norm1(r)+c['residual_kappa']*norm1(j),'Norm bound failed')
                checked+=1
        # Basis vectors attain the induced1 norm for each nonzero matrix.
        for matrix,key in ((B,'kappa'),(C,'residual_kappa')):
            actual=max((norm1(mv(matrix,[int(i==k) for i in range(len(matrix[0]))])) for k in range(len(matrix[0]))),default=F(0))
            need(actual==c[key],'Induced norm is not the sharp unrestricted coefficient')
    return dict(cases=cases,norm_cases=checked)

def bounded_kernel_case():
    # r+u1+u2=0; represent d=u1-u2 instead of silently discarding it.
    count=0
    for r,d in product((F(i,4) for i in range(-12,13)),repeat=2):
        u1=(-r+d)/2;u2=(-r-d)/2
        exposure=abs(r)+abs(u1)+abs(u2)
        need(exposure==abs(r)+max(abs(r),abs(d)),'Retained circulation identity failed')
        need(exposure<=2*abs(r)+abs(d),'Bounded-mode residual failed')
        count+=1
    return dict(cases=count,retained_mode='d=u1-u2',exact='E=abs(r)+max(abs(r),abs(d))',bound='E<=2*abs(r)+abs(d)',
                physical_d_bound_not_assumed=True)

def serial(x):
    if isinstance(x,F):return str(x)
    if isinstance(x,dict):return {k:serial(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)):return [serial(v) for v in x]
    return x

def main():
    p=argparse.ArgumentParser();g=p.add_mutually_exclusive_group(required=True)
    g.add_argument('--write',action='store_true');g.add_argument('--check',action='store_true');a=p.parse_args()
    names=('BOUNDARY-FACTORIZATION.md','boundary_factorization_model.py')
    sources={n:sha256((HERE/n).read_text(encoding='utf-8-sig').replace('\r\n','\n').encode()).hexdigest() for n in names}
    result=serial(dict(status='proved finite-dimensional factorization theorem with exact rational checks',sources=sources,
                       theorem=theorem_checks(),examples=concrete_cases(),bounded_kernel=bounded_kernel_case(),
                       physical_source_realization_or_return_certified=False))
    dest=HERE/'boundary_factorization_results.json'
    if a.write:dest.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n',encoding='utf-8')
    else:need(json.loads(dest.read_text(encoding='utf-8'))==result,'Record differs')
    print(json.dumps({'status':'passed','matrix_pairs':result['theorem']['exhaustive_two_by_two_pairs'],
                      'physical_realization':False}))

if __name__=='__main__':main()

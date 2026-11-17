"""Exact finite linear repair witnesses, not a proof of the general theorems."""
from fractions import Fraction as Q
import json

def mat(rows): return [[Q(x) for x in row] for row in rows]
def ident(n): return mat([[i == j for j in range(n)] for i in range(n)])
def mul(a,b): return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]
def kron(a,b): return [[x*y for x in ar for y in br] for ar in a for br in b]
def rank(a):
    a=[r[:] for r in a]; k=0
    for j in range(len(a[0])):
        i=next((i for i in range(k,len(a)) if a[i][j]),None)
        if i is None: continue
        a[k],a[i]=a[i],a[k]; d=a[k][j]; a[k]=[x/d for x in a[k]]
        for i in range(len(a)):
            if i!=k:
                d=a[i][j]; a[i]=[x-d*y for x,y in zip(a[i],a[k])]
        k+=1
        if k==len(a): break
    return k
def zero(m,n): return mat([[0]*n for _ in range(m)])

# X=Q2 tensor Q2, basis 00,01,10,11. C records shared scalar and margins.
A=mat([[1,0,0,0],[0,0,1,0],[0,1,0,0]])
B=mat([[1,0,0,0],[0,1,0,0],[0,0,1,0]])
assert rank(A)==rank(B)==3
# P coordinates (x00,x01,x10,x11,k). Its Z readout has one free joint coordinate.
r=mat([[int(i==j) for j in range(5)] for i in range(4)])
z=mat([[1,0,0,0,0],[0,0,1,0,0],[0,1,0,0,0],[0,0,0,0,1]])
assert mul(A,r)==mul(B,z)
# R coordinates (t,s00,s01,s10,s11), BS=tA. Evaluation X tensor R -> P.
ev=zero(5,20)
for i in range(4):
    ev[i][i*5]=Q(1)
    ev[4][i*5+i+1]=Q(1)
epsR=mat([[1,0,0,0,0]])
assert mul(r,ev)==kron(ident(4),epsR)
assert rank(ev)==5
# The normalized zero-kernel section preserves the old tensor-kernel coordinate x11.
unit=mat([[1],[0],[0],[0],[0]])
c=mul(ev,kron(ident(4),unit))
assert mul(r,c)==ident(4)
old_kernel=mat([[0],[0],[0],[1]])
assert mul(z,mul(c,old_kernel))==mat([[0],[0],[0],[0]])
assert mul(r,mul(c,old_kernel))==old_kernel
# Quotient forgetting x11: a repair depending on s11 cannot descend.
badS=mat([[1,0,0,0],[0,0,1,0],[0,1,0,0],[0,0,0,1]])
assert mul(B,badS)==A
assert mul(badS,old_kernel)!=mat([[0],[0],[0],[0]])
# The maximal descending operator subresource has s11=0: dimension 4 versus 5.
desc=mat([[int(i==j) for j in range(4)] for i in range(5)])
assert rank(desc)==4
# Strict equality of old A/B margins has no correcting variable and nonzero defect.
pA=kron(ident(2),mat([[1,0]])); pB=kron(mat([[1,0]]),ident(2))
defect=[[x-y for x,y in zip(a,b)] for a,b in zip(pA,pB)]
assert rank(defect)==1

# A second witness has first coordinate x11+k and one new free coordinate.
# H2 coordinates (x00,x01,x10,x11,k1,k2); R2=(t2,u0,...,u4).
ev2=zero(6,30)
for i in range(5):
    ev2[i][i*6]=Q(1)
    ev2[5][i*6+i+1]=Q(1)
# Combined resource R12=(t,a0..a3,b0..b3).
compose=zero(9,30)
compose[0][0]=Q(1)
for i in range(4):
    compose[1+i][(1+i)*6]=Q(1)       # a=t2*s
    compose[5+i][i+1]=Q(1)          # b=t1*u_old + u_k*s
    compose[5+i][(1+i)*6+5]=Q(1)
ev12=zero(6,36)
for i in range(4):
    ev12[i][i*9]=Q(1)
    ev12[4][i*9+1+i]=Q(1)
    ev12[5][i*9+5+i]=Q(1)
assert mul(ev2,kron(ev,ident(6)))==mul(ev12,kron(ident(4),compose))
r2=mat([[int(i==j) for j in range(6)] for i in range(5)])
assert mul(r2,ev2)==kron(ident(5),mat([[1,0,0,0,0,0]]))
assert rank(compose)==9

report={
 'status':'PASS','field':'Q; exact Fraction arithmetic',
 'old_history_dimension':4,'joint_boundary_dimension':3,
 'history_retaining_pullback_dimension':5,'universal_resource_dimension':5,
 'evaluation_source_dimension':20,'evaluation_rank':5,
 'evaluation_kernel_dimension':15,
 'old_joint_invisible_kernel_retained':True,
 'quotient_descending_resource_dimension':4,
 'strict_old_relation_totality':'obstructed by rank-one defect',
 'two_stage_resource_composition_rank':9,
 'two_stage_evaluation_and_prefix_squares':'passed',
 'scope':'finite linear witnesses only; no probability, general naturality, or recurrent proof'
}
print(json.dumps(report,indent=2))

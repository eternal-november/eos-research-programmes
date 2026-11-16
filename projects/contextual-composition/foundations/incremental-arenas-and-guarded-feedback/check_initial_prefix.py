from fractions import Fraction as F
import json
nu={0:F(1,2),1:F(1,2),2:F(0)}
r0={0:'t',1:'a',2:'a'};nt={'t':F(1,2),'a':F(1,2)}
mu={0:F(1,2),1:F(1,2),2:F(0)}
H0={(z,):p for z,p in nu.items()};T0={('t',):F(1,2),('a',):F(1,2)}
H1={};T1={}
for z,p in nu.items():
 if z==0:H1[(z,)]=p
 else:
  for w,q in mu.items():H1[(z,w)]=p*q
T1[('t',)]=F(1,2)
for w,q in mu.items():T1[('a',w)]=F(1,2)*q
def mp(h):return (r0[h[0]],)+h[1:]
for src,tgt in ((H0,T0),(H1,T1)):
 assert sum(src.values())==sum(tgt.values())==1
 for k,p in tgt.items():assert sum(v for h,v in src.items() if mp(h)==k)==p
for z,p in nu.items():assert sum(v for h,v in H1.items() if h[0]==z)==p
assert {h for h in H0 if mp(h)==('t',)}=={(0,)}
assert (2,) in H0 and (2,2) in H1 # neither rawzero seed nor rawzero outcome deleted
# Actual augmentation-compatible initial coefficient square.
def kron(A,B):return [[a*b for a in ar for b in br] for ar in A for br in B]
def mm(A,B):return [[sum(a*b for a,b in zip(row,col)) for col in zip(*B)] for row in A]
def eye(n):return [[int(i==j) for j in range(n)] for i in range(n)]
alpha=[[1,0,0],[2,3,4]];beta=[[1,0],[5,6]];eps=[[1,0]]
assert mm(alpha,kron(eye(3),eps))==mm(kron(eye(2),eps),kron(alpha,beta))
# Same-state initial seeds can distinguish controls. A state quotient isn't enough.
diag={(0,0):F(1,2),(1,1):F(1,2)};anti={(0,1):F(1,2),(1,0):F(1,2)}
assert diag!=anti
print(json.dumps({'status':'passed','source_H0':len(H0),'target_H0':len(T0),'source_H1':len(H1),'target_H1':len(T1),
'checks':['noninjective-initial-exact-pushforward','initial-zero-retention','T0-strict-domain','normalized-prefix-truncation','actual-initial-tensor-augmentation-square','state-only-controller-obstruction']},indent=2))

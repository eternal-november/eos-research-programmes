"""Finite regression checks, not formal proof or a data-learning certificate."""
from itertools import product
import json
import numpy as np
from scipy.optimize import linprog

results = {}
def vertices(nx, ny=2):
    out=[]
    for f in product(range(ny), repeat=nx):
        d=np.zeros((nx,ny)); d[np.arange(nx), f]=1
        out.append(d.reshape(-1))
    return np.array(out).T

def feasible(H,A,B):
    cols=np.column_stack([np.outer(A[:,i],B[:,j]).reshape(-1)
                         for i in range(A.shape[1]) for j in range(B.shape[1])])
    r=linprog(np.zeros(cols.shape[1]),A_eq=cols,b_eq=H.reshape(-1),bounds=(0,None),method='highs')
    if r.success:
        assert np.max(np.abs(cols@r.x-H.reshape(-1)))<1e-9
        assert abs(r.x.sum()-1)<1e-9
    return bool(r.success)

def outside_classes(H,nx1,nx2):
    T=H.reshape(nx1,2,nx2,2)
    ans=[]
    for side in (0,1):
        profiles=T.sum(axis=1) if side==0 else T.sum(axis=3).transpose(2,0,1)
        classes=[]
        for x,p in enumerate(profiles):
            for block in classes:
                if np.array_equal(p,profiles[block[0]]): block.append(x);break
            else: classes.append([x])
        ans.append(classes)
    return ans

D=vertices(2)
PR=np.zeros((4,4))
for x,a,z,b in product(range(2),repeat=4):
    PR[2*x+a,2*z+b]=0.5 if a^b==x*z else 0
assert outside_classes(PR,2,2)==[[[0,1]],[[0,1]]]
assert not feasible(PR,D,D)
for x in range(2): assert feasible(PR[2*x:2*x+2,:],vertices(1),D)
for z in range(2): assert feasible(PR[:,2*z:2*z+2],D,vertices(1))
results['PR_constant_messages_rejected_both_incomparable_one_input_refinements_accepted']=True

RF=D@D.T/4
assert np.linalg.matrix_rank(RF)==3
assert feasible(RF,D,D)
assert outside_classes(RF,2,2)==[[[0,1]],[[0,1]]]
results['random_function_rank3_four_ray_realization']=True

# Shared random identity/flip, a simplicial rank-two channel cone.
E=D[:,[1,2]]
CF=E@E.T/2
assert np.linalg.matrix_rank(CF)==2
assert feasible(CF,E,E)
assert outside_classes(CF,2,2)==[[[0,1]],[[0,1]]]
results['correlated_flip_positive_core']=True

# Proper nonsimplicial retract: duplicate first effective input row.
J=np.eye(4)[[0,1,0,1,2,3],:]
A=J@D
H=J@RF@J.T
P=np.zeros((6,6))
for y in range(2):
    for x in (0,1): P[2*x+y,y]=P[2*x+y,2+y]=.5
P[4,4]=P[5,5]=1
assert np.array_equal(P@P,P)
assert np.array_equal(P@H,H) and np.array_equal(H@P.T,H)
assert np.linalg.matrix_rank(H)==3
assert feasible(H,A,A)
for d in vertices(3).T:
    q=(P@d).reshape(3,2)
    assert np.min(q)>=0 and np.array_equal(q.sum(axis=1),np.ones(3))
    assert np.array_equal(q[0],q[1])
PR3=J@PR@J.T
assert np.array_equal(P@PR3,PR3) and np.linalg.matrix_rank(PR3)==3
assert not feasible(PR3,A,A)
results['proper_mass_preserving_positive_retraction_accepts_RF_rejects_PR']=True

# Biased parity boundary: each source bit must be communicated to the core.
def parity_kernel(p):
    K=np.zeros((2,2,2,2,2)) # a,b,cnext,anext,bnext; c=0
    for a,b,n0,n1,n2 in product(range(2),repeat=5):
        c=a^b^n0; aa=a^c^n1; bb=b^c^n2
        weight=(p if n0 else 1-p)*(.125 if n1 else .875)*(.25 if n2 else .75)
        K[a,b,c,aa,bb]+=weight
    return K
K=parity_kernel(.25)
assert np.allclose(K.sum(axis=(2,3,4)),1)
assert not np.array_equal(K[0].sum(axis=2),K[1].sum(axis=2))
assert not np.array_equal(K[:,0].sum(axis=3),K[:,1].sum(axis=3))
Q=K.sum(axis=(3,4))
assert not np.array_equal(Q[0],Q[1])
Qfair=parity_kernel(.5).sum(axis=(3,4))
assert np.array_equal(Qfair[0],Qfair[1])
results['biased_parity_requires_bits_fair_noise_regression_detects_lost_lower_bound']=True
print(json.dumps({'status':'PASS','checks':results},indent=2))

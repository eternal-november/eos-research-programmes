from fractions import Fraction as F
from itertools import product
import numpy as np
import json
P1=np.array([[1,0,0],[0,1,0]],int)
P2=np.array([[1,0,0],[0,0,1]],int)
Theta=np.vstack([np.kron(P1,P1),np.kron(P2,P2)[1:]])
assert Theta.shape==(7,9)
# Exact identity minor proves rank seven; no floating-rank inference.
assert np.array_equal(Theta[:,[0,1,3,4,2,6,8]],np.eye(7,dtype=int))
assert all(Theta[:,j].tolist()==[0]*7 for j in (5,7))
assert np.array_equal(np.array([[1]+[0]*6])@Theta,np.array([[1]+[0]*8]))
# Native paid observer retained through the directed comparison.
paid_atomic=np.zeros((3,7),int);paid_atomic[0,0]=paid_atomic[1,2]=paid_atomic[2,5]=1
paid_staged=np.zeros((3,9),int);paid_staged[0,0]=paid_staged[1,3]=paid_staged[2,6]=1
assert np.array_equal(paid_atomic@Theta,paid_staged)
# Naturality on actual augmented maps including shears, not only dimensions.
K1=np.array([[1,0],[2,3]],int);K2=np.array([[1,0],[-1,2]],int)
L1=np.array([[1,0],[1,2]],int);L2=np.array([[1,0],[3,-1]],int)
K=np.array([[1,0,0],[2,3,0],[-1,0,2]],int)
L=np.array([[1,0,0],[1,2,0],[3,0,-1]],int)
E=np.zeros((8,7),int)
for i in range(4):E[i,i]=1
E[4,0]=1
for i in range(5,8):E[i,i-1]=1
R=np.vstack([np.eye(8,dtype=int)[:4],np.eye(8,dtype=int)[5:]])
blocks=np.zeros((8,8),int);blocks[:4,:4]=np.kron(K1,L1);blocks[4:,4:]=np.kron(K2,L2)
atomic_map=R@blocks@E
assert np.array_equal(atomic_map@Theta,Theta@np.kron(K,L))
# Actual paid->broadcast->initializer row, including all zero paid atoms.
bits=list(product((0,1),repeat=2))
paid={z:(F(1,2) if z[0]==z[1] else F(0)) for z in bits}
def k(z,g,y):return F(1,2) if (y[0]!=y[1])==bool(g) else F(0)
B=lambda z:(z[0]+z[1])%2
Q={(z,y):paid[z]*k(z,B(z),y) for z,y in product(bits,repeat=2)}
assert len(Q)==16 and sum(Q.values())==1
# Changing only conditional table at zero paid branch changes the plan, not Q.
Q2={(z,y):paid[z]*(k(z,1-B(z),y) if z==(0,1) else k(z,B(z),y)) for z,y in Q}
assert Q==Q2
assert any(k((0,1),0,y)!=k((0,1),1,y) for y in bits)
# Zero/offdriver outputs remain selected-state inputs; no circular B(y).
posts={(z,y):(B(z),y) for z,y in Q}
assert len(posts)==16
print(json.dumps({'actual_stage_to_atomic_arrow':'PASS','staged_dimension':9,'atomic_dimension':7,'alternative_tensor_init_dimension':12,'rank':int(np.linalg.matrix_rank(Theta)),'cross_owner_kernel_dimension':2,'augmentation_and_paid_observer_squares':'PASS','naturality_with_augmented_shears':'PASS','closed_stage_raw_atoms_including_zeros':16,'zero_branch_plan_not_recoverable_from_Q':'PASS','scope':'finite exact integer/rational diagnostics, not recursive feedback theorem'},indent=2))

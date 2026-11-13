"""Finite rank-two Euler-cocycle smoke test on tangent-plane response samples.

Uses a declared covariance modulus ||G(x)-G(y)|| <= beta^2 ||x-y||.
This is floating-point validation, not a certified interval-arithmetic proof.
"""
import itertools
import json
from collections import deque
import numpy as np
from scipy.spatial import ConvexHull

phi=(1+np.sqrt(5))/2
vertices=[]
for s,t in itertools.product([-1.,1.], repeat=2):
    vertices.extend([[0,s,t*phi],[s,t*phi,0],[t*phi,0,s]])
vertices=np.array(vertices)
vertices/=np.linalg.norm(vertices,axis=1)[:,None]
faces=ConvexHull(vertices).simplices.copy()
for f in faces:
    a,b,c=vertices[f]
    if np.dot(np.cross(b-a,c-a),a+b+c)<0:
        f[1],f[2]=f[2],f[1]
for _ in range(5):
    vert=list(vertices)
    cache={}
    def midpoint(a,b):
        key=tuple(sorted((int(a),int(b))))
        if key not in cache:
            z=vertices[a]+vertices[b]
            z/=np.linalg.norm(z)
            cache[key]=len(vert)
            vert.append(z)
        return cache[key]
    new=[]
    for a,b,c in faces:
        ab,bc,ca=midpoint(a,b),midpoint(b,c),midpoint(c,a)
        new.extend([[a,ab,ca],[ab,b,bc],[ca,bc,c],[ab,bc,ca]])
    vertices=np.array(vert)
    faces=np.array(new,dtype=int)
edges=np.array(sorted({tuple(sorted((int(a),int(b))))
    for f in faces for a,b in zip(f,np.roll(f,-1))}),dtype=int)
h=float(np.linalg.norm(vertices[edges[:,0]]-vertices[edges[:,1]],axis=1).max())

beta=0.02
A=np.array([[1,1,1],[-1,1,1],[0,-2,1],[0,0,-3]],dtype=float)
A/=np.array([np.sqrt(2),np.sqrt(6),np.sqrt(12)])[None,:]
T=np.eye(3)[None,:,:]-vertices[:,:,None]*vertices[:,None,:]
# Only the next experimental-generation block uses the tangent formula.
tables=np.empty((len(vertices),4,4))
tables[:,0,:]=0.25
tables[:,1:,:]=0.25+beta*(T@A.T)
C=np.hstack([-np.ones((3,1)),np.eye(3)])
B=C[None,:,:]@tables
G=B.transpose(0,2,1)@B
vals,vecs=np.linalg.eigh(G)
Q=vecs[:,:,-2:].copy()
gaps=vals[:,-2]-vals[:,-3]
q=beta**2*h
projector_error=float(np.max(q/(gaps-q)))
assert np.all(q<gaps/21)

# Resolve orientations from observed overlaps, not the sphere normal vectors.
overlap=np.einsum('nki,nkj->nij',Q[edges[:,0]],Q[edges[:,1]])
negative=np.linalg.det(overlap)<0
adj=[[] for _ in vertices]
for (v,w),sgn in zip(edges,negative):
    adj[v].append((w,int(sgn)))
    adj[w].append((v,int(sgn)))
orient=-np.ones(len(vertices),dtype=int)
orient[0]=0
queue=deque([0])
while queue:
    v=queue.popleft()
    for w,sgn in adj[v]:
        expected=orient[v]^sgn
        if orient[w]<0:
            orient[w]=expected
            queue.append(w)
        else:
            assert orient[w]==expected
Q[:,:,0]*=(1-2*orient)[:,None]
overlap=np.einsum('nki,nkj->nij',Q[edges[:,0]],Q[edges[:,1]])
assert np.all(np.linalg.det(overlap)>0)
u,s,vh=np.linalg.svd(overlap)
rot=u@vh
angles=np.arctan2(rot[:,1,0],rot[:,0,0])
lookup={tuple(edge):theta for edge,theta in zip(edges,angles)}
def angle(a,b):
    return lookup[(a,b)] if a<b else -lookup[(b,a)]
angle_sums=np.array([angle(a,b)+angle(b,c)+angle(c,a) for a,b,c in faces])
integer_cochain=np.rint(angle_sums/(2*np.pi)).astype(int)
euler=int(integer_cochain.sum())
assert abs(euler)==2
rounding_distance=float(np.max(np.abs(angle_sums-2*np.pi*integer_cochain)))
signal=float(np.sqrt(np.min(vals[:,-2]-q)))
Lp=0.05
candidate_error=2*(beta+Lp)*h
assert candidate_error<signal
print(json.dumps({
    'vertices':len(vertices),'edges':len(edges),'triangles':len(faces),
    'mesh_chordal':h,'beta':beta,'projector_error_bound':projector_error,
    'orientation_cocycle_is_coboundary':True,
    'integer_Euler_cycle_evaluation':euler,
    'max_triangle_rounding_residual_radians':rounding_distance,
    'signal_lower_bound':signal,
    'candidate_Lipschitz_bound':Lp,
    'candidate_centered_error_upper_bound':candidate_error,
    'certified_normalized_state_lower_bound':4,
    'warning':'Floating-point smoke test, not an interval-arithmetic proof.'
},indent=2))

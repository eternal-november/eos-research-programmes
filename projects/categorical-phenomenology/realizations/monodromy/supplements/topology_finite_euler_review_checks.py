#!/usr/bin/env python3
"""Independent sphere Euler-cocycle regression, not interval certification.
Build a subdivided octahedral sphere, orient tangent frames, compute polar
transitions and rounded integer cocycle, and check all theorem margins for
the barycentric sampled-response reference. Requires NumPy. Fixed seed.
"""
import json, math
from pathlib import Path
import numpy as np

# Outward oriented octahedron, refined seven times: 131072 faces.
vertices=[np.array(v,dtype=float) for v in [(1,0,0),(-1,0,0),(0,1,0),(0,-1,0),(0,0,1),(0,0,-1)]]
faces=[]
for a in [0,1]:
    for b in [2,3]:
        for c in [4,5]:
            f=(a,b,c)
            if np.linalg.det(np.array([vertices[x] for x in f]))<0:f=(a,c,b)
            faces.append(f)
for _ in range(7):
    cache={};out=[]
    def mid(i,j):
        key=tuple(sorted((i,j)))
        if key not in cache:
            v=vertices[i]+vertices[j];v/=np.linalg.norm(v)
            cache[key]=len(vertices);vertices.append(v)
        return cache[key]
    for a,b,c in faces:
        ab,bc,ca=mid(a,b),mid(b,c),mid(c,a)
        out.extend([(a,ab,ca),(ab,b,bc),(ca,bc,c),(ab,bc,ca)])
    faces=out
V=np.array(vertices);F=np.array(faces,dtype=int)
E=np.unique(np.sort(np.vstack([F[:,[0,1]],F[:,[1,2]],F[:,[2,0]]]),axis=1),axis=0)
assert len(V)-len(E)+len(F)==2
# An oriented integral fundamental cycle: each directed edge cancels.
boundary={}
for a,b,c in faces:
    for i,j in [(a,b),(b,c),(c,a)]:
        key=(min(i,j),max(i,j));boundary[key]=boundary.get(key,0)+(1 if i<j else -1)
assert all(v==0 for v in boundary.values())

# Frames with t1 cross t2 = outward normal. The target tangent projector is I-vvT.
axis=np.zeros_like(V);axis[:,2]=1
axis[np.abs(V[:,2])>.9]=[1,0,0]
t1=np.cross(axis,V);t1/=np.linalg.norm(t1,axis=1)[:,None]
t2=np.cross(V,t1)
Q=np.stack([t1,t2],axis=-1)
P=np.eye(3)[None,:,:]-V[:,:,None]*V[:,None,:]
assert np.max(abs(Q@Q.transpose(0,2,1)-P))<1e-12

# For H_v=[c; c+beta P_v rows in fixed zero-sum coordinates], B_v is beta P_v.
# The beta cancels in qbar/gamma; adjacent projector distance is sin(angle).
cos=np.sum(V[E[:,0]]*V[E[:,1]],axis=1)
dist=np.sqrt(np.maximum(0.,1-cos*cos))
dv=np.zeros(len(V));np.maximum.at(dv,E[:,0],dist);np.maximum.at(dv,E[:,1],dist)
qratio=(2+dv)*dv
assert np.max(qratio)<1/21
projector_error=qratio/(1-qratio)
zeta=2*np.arcsin(2*np.sqrt(2)*projector_error.max())
assert projector_error.max()<1/20 and 3*zeta<math.pi

# Deliberately random local orientation flips, then recover gauge by w1.
rng=np.random.default_rng(2026110321)
flips=rng.integers(0,2,len(V));Q[:,:,0]*=(1-2*flips)[:,None]
A=Q[E[:,0]].transpose(0,2,1)@Q[E[:,1]]
w1=(np.linalg.det(A)<0).astype(int)
assert np.array_equal(w1,flips[E[:,0]]^flips[E[:,1]])
# Solve a=db directly by traversal, with b(root)=0.
adj=[[] for _ in V]
for (i,j),s in zip(E,w1):adj[i].append((j,int(s)));adj[j].append((i,int(s)))
b=np.full(len(V),-1,dtype=int);b[0]=0;stack=[0]
while stack:
    i=stack.pop()
    for j,s in adj[i]:
        wanted=b[i]^s
        if b[j]<0:b[j]=wanted;stack.append(j)
        else:assert b[j]==wanted
assert np.min(b)>=0
Q[:,:,0]*=(1-2*b)[:,None]
A=Q[E[:,0]].transpose(0,2,1)@Q[E[:,1]]
assert np.min(np.linalg.det(A))>0
# Closed polar SO2 angle formula, valid for positive determinant matrices.
angles=np.arctan2(A[:,1,0]-A[:,0,1],A[:,0,0]+A[:,1,1])
angle_map={tuple(e):float(a) for e,a in zip(E,angles)}
def edge_angle(i,j):return angle_map[(i,j)] if i<j else -angle_map[(j,i)]
values=[];pairing=0;rounding_margin=1.
for a,b,c in faces:
    value=(edge_angle(a,b)+edge_angle(b,c)+edge_angle(c,a))/(2*math.pi)
    n=round(value);pairing+=n;values.append(n)
    rounding_margin=min(rounding_margin,.5-abs(value-n))
assert abs(pairing)==2 and rounding_margin>0

# Gauge by full SO2 rotations; integer lifts may change but paired class does not.
phases=rng.uniform(-math.pi,math.pi,len(V))
perturbed=angles+phases[E[:,1]]-phases[E[:,0]]
perturbed=(perturbed+math.pi)%(2*math.pi)-math.pi
angle_map={tuple(e):float(a) for e,a in zip(E,perturbed)}
pairing2=sum(round((edge_angle(a,b)+edge_angle(b,c)+edge_angle(c,a))/(2*math.pi)) for a,b,c in faces)
assert pairing2==pairing

out={
 'vertices':len(V),'edges':len(E),'triangles':len(F),
 'max_reference_q_over_gap':float(np.max(qratio)),
 'max_projector_error_bound':float(projector_error.max()),
 'max_three_edge_angle_error_bound':float(3*zeta),
 'minimum_rounding_margin_in_turns':rounding_margin,
 'euler_fundamental_cycle_pairing':pairing,
 'pairing_after_arbitrary_vertex_rotation_gauge':pairing2,
 'status':'all passed',
 'qualification':'Floating-point regression, not certified interval arithmetic.'}
Path(__file__).with_name('topology_finite_euler_review_checks_results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))

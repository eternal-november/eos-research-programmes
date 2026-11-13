#!/usr/bin/env python3
"""Independent mixed-output inverse-filter check with a product amplitude-damping channel."""
import numpy as np
import json
from itertools import product
n=3; d=1<<n
S=np.zeros((d,d))
for x in range(d): S[((x<<1)|(x>>(n-1)))&(d-1),x]=1
A=np.eye(d)+2*S; B=A.T; U=A@np.linalg.inv(B)
def ket(M): return M.T.reshape(-1)
def projector(v): return np.outer(v,v.conj())
def kron_all(ms):
    z=np.array([[1.]])
    for m in ms: z=np.kron(z,m)
    return z
p=.37
ks=[np.diag([1.,np.sqrt(1-p)]),np.array([[0.,np.sqrt(p)],[0.,0.]])]
Kraus=[kron_all(ms) for ms in product(ks,repeat=n)]
def choi_channel_input(M):
    return sum(projector(ket(k@M)) for k in Kraus)
sigma=choi_channel_input(B/np.linalg.norm(B,'fro'))
tau=projector(ket(A/np.linalg.norm(A,'fro')))
J=choi_channel_input(np.eye(d)/np.sqrt(d))
JU=projector(ket(U/np.sqrt(d)))
K=np.kron(np.linalg.inv(B).T,np.eye(d)); scale=np.linalg.norm(B,'fro')**2/d
filtered=scale*K@(sigma-tau)@K.conj().T
def T(x,y): return float(np.abs(np.linalg.eigvalsh(x-y)).sum()/2)
out=dict(n=n,traces=[float(np.trace(x)) for x in [sigma,tau,J,JU]],inverse_filter_identity_max_abs=float(np.max(np.abs(filtered-(J-JU)))),trace_distance_input=T(sigma,tau),trace_distance_choi=T(J,JU),factor_bound=scale,inequality_passes=bool(T(J,JU)<=scale*T(sigma,tau)+1e-12),note='N=3 checks only the filter identity and norm comparison; the stated spatial-radius theorem is vacuous at N=3.')
print(json.dumps(out,indent=2))

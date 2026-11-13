#!/usr/bin/env python3
"""Bounded exact-law and sampled-regression QA for the nonlinear parity family.
No whole-kernel enumeration is required by the symbolic growing construction;
this small n=8 oracle is used only to verify assertions independently.
"""
import itertools, json, math
from pathlib import Path
import numpy as np

ETA=.17; C=1-2*ETA; M=4; N=2*M; PZ=.25
rng=np.random.default_rng(20261029)
perm=rng.permutation(N)
states=((np.arange(1<<N)[:,None]>>np.arange(N))&1).astype(np.int8)
pairs=[tuple(map(int,perm[2*i:2*i+2])) for i in range(M)]
q=np.array([states[:,a]^states[:,b] for a,b in pairs]).T
r=states[:,perm[::2]]
f=np.column_stack([q[:,1:],q[:,0]^(q[:,1]&q[:,-1])])
off=np.column_stack([q[:,i]&q[:,(i+1)%M] for i in range(M)])
noise=np.prod(np.where(states,ETA,1-ETA),axis=1)

def encode(qq,rr):
 out=np.zeros((len(qq),N),np.int8)
 for i,(a,b) in enumerate(pairs):out[:,a]=rr[:,i];out[:,b]=rr[:,i]^qq[:,i]
 return (out*(1<<np.arange(N))).sum(axis=1)

def kernel(world,delta=0):
 ans=np.zeros((1<<N,1<<N))
 for z,p in [(0,1-PZ),(1,PZ)]:
  rr=r.copy()
  if world=='B':rr[:,0]^=r[:,1]
  rr^=off;rr^=z
  pre=encode(f,rr)
  ans+=(1-delta)*p*noise[np.arange(1<<N)[None,:]^pre[:,None]]
  ff=f.copy();ff[:,0]^=r[:,0]
  pre2=encode(ff,rr)
  ans+=delta*p*noise[np.arange(1<<N)[None,:]^pre2[:,None]]
 return ans
A=kernel('A');B=kernel('B');DELTA=.03;L=kernel('A',DELTA)
assert min(A.min(),B.min(),L.min())>0
assert np.max(abs(A.sum(1)-1))<1e-12
assert np.max(abs(A.sum(0)-1))<1e-12
assert np.max(abs(B.sum(0)-1))<1e-12
qid=(q*(1<<np.arange(M))).sum(1)
H=np.eye(1<<M)[qid]
KA=A@H;KB=B@H;KL=L@H
qstates=((np.arange(1<<M)[:,None]>>np.arange(M))&1).astype(np.int8)
fq=np.column_stack([qstates[:,1:],qstates[:,0]^(qstates[:,1]&qstates[:,-1])])
rho=2*ETA*(1-ETA)
expected=np.prod(np.where(qstates[None,:,:]^fq[:,None,:],rho,1-rho),axis=2)
assert np.max(abs(KA-expected[qid]))<1e-12
assert np.max(abs(KB-KA))<1e-12

def span_contains(s, generators):
 basis={}
 for g in generators:
  v=sum(1<<j for j in g)
  while v:
   k=v.bit_length()-1
   if k in basis:v^=basis[k]
   else:basis[k]=v;break
 v=sum(1<<j for j in s)
 while v:
  k=v.bit_length()-1
  if k not in basis:return False
  v^=basis[k]
 return True

# Learner gets next-parity moment responses only; no true pair grouping input.
D=min(12,N)
subsets=[s for k in range(D+1) for s in itertools.combinations(range(N),k)]
phi=np.array([(-1.)**states[:,s].sum(1) for s in subsets]).T
G=phi.T@phi/len(states)
learned=[tuple(sorted(pairs[0]))]
response_polys=[]
while True:
 s=learned[-1]
 chi=(-1.)**states[:,s].sum(1)
 b=phi.T@(A@chi)/len(states)
 coeff=np.linalg.solve(G,b)/(C**len(s))
 nz=np.flatnonzero(abs(coeff)>1e-9)
 response_polys.append({str(subsets[j]):float(coeff[j]) for j in nz})
 response=phi@coeff
 assert np.max(abs(response**2-1))<1e-10
 if len(nz)==1 and abs(coeff[nz[0]]-1)<1e-10 and len(subsets[nz[0]])==2:
  target=subsets[nz[0]]
  assert target not in learned
  learned.append(target)
 else:
  # Every last-response monomial belongs to XOR span of learned parities.
  assert all(span_contains(subsets[j],learned) for j in nz)
  break
assert learned==[tuple(sorted(p)) for p in pairs]
assert len(learned)==M

# Counterexample: enlarged candidate (Q,R0) closes in A, not in B.
pid=qid+(1<<M)*r[:,0]
PH=np.eye(1<<(M+1))[pid]
PA=A@PH;PB=B@PH
closureA=max(np.max(abs(PA[pid==u]-PA[np.flatnonzero(pid==u)[0]])) for u in np.unique(pid))
closureB=max(np.max(abs(PB[pid==u]-PB[np.flatnonzero(pid==u)[0]])) for u in np.unique(pid))
assert closureA<1e-12 and closureB>1e-4

# Nonzero leakage rejects exact closure but has a uniform TV certificate.
leakTV=.5*np.abs(KL-KA).sum(1)
assert leakTV.max()<=DELTA+1e-12
leakClosure=max(np.max(abs(KL[qid==u]-KL[np.flatnonzero(qid==u)[0]])) for u in np.unique(qid))
assert leakClosure>1e-5
chi0=(-1.)**q[:,0]
resL=(L@chi0)/(C*C)
f0=(-1.)**f[:,0]
latent_error=(1-f0*resL)/2
assert abs(latent_error.max()-DELTA)<1e-12

# Check non-arbitrary Gram conditioning on a worst-biased product law.
dgram=3
sg=[s for k in range(dgram+1) for s in itertools.combinations(range(N),k)]
pg=np.array([(-1.)**states[:,s].sum(1) for s in sg]).T
biasedG=(pg.T*noise)@pg
Cg=sum(math.comb(N,k)*((1+C*C)/(4*ETA*(1-ETA)))**k for k in range(dgram+1))
lmin=float(np.linalg.eigvalsh(biasedG)[0])
assert lmin>=1/Cg-1e-12

# Independent stationary readout pairs: finite sampled learner, with oracle
# used only to generate samples and validate the resulting regression.
# This QA demonstrates empirical recovery, NOT a nonvacuous confidence claim.
sample_count=200000
xs=rng.integers(len(states),size=sample_count)
zs=(rng.random(sample_count)<PZ).astype(np.int8)
rr=r[xs]^off[xs]^zs[:,None]
yidx=encode(f[xs],rr)
enoise=(rng.random((sample_count,N))<ETA).astype(np.int8)
eidx=(enoise*(1<<np.arange(N))).sum(1)
ys=yidx^eidx
counts=np.bincount(xs,minlength=len(states))
Ghat=(phi.T*(counts/sample_count))@phi
sample_supports=[tuple(sorted(pairs[0]))];sample_max_errors=[]
for iteration in range(N):
 p=sample_supports[-1]  # selected by the preceding fitted response, not truth
 chi=(-1.)**states[:,p].sum(1)
 sums=np.bincount(xs,weights=chi[ys],minlength=len(states))
 bhat=phi.T@sums/sample_count
 coeff=np.linalg.solve(Ghat,bhat)
 # Oracle used here only to record regression error, never choose a query.
 sample_max_errors.append(float(np.max(abs(phi@coeff-A@chi))))
 j=int(np.argmax(abs(coeff)))
 if coeff[j]>.75*C*C and len(subsets[j])==2:
  assert subsets[j] not in sample_supports
  sample_supports.append(subsets[j])
 else:
  significant=np.flatnonzero(abs(coeff)>.25*C*C)
  assert all(span_contains(subsets[k],sample_supports) for k in significant)
  break
else:raise AssertionError('Sampled learner did not terminate')
# Ground truth grouping is consulted only for post-discovery validation.
assert sample_supports==[tuple(sorted(p)) for p in pairs]
# Conservative simultaneous finite-data confidence bound, honestly reported.
K=sum(math.comb(N,j) for j in range(3));dim=len(subsets);alpha=.05
stat_count=dim*dim+dim*K
t=math.sqrt(2*math.log(2*stat_count/alpha)/sample_count)
Cbound=sum(math.comb(N,k)*((1+C*C)/(4*ETA*(1-ETA)))**k for k in range(D+1))
lam=1/Cbound
finite_precondition=bool(dim*t<=lam/2)

result={
 'status':'PASS','seed':20261029,'m':M,'n':N,'eta':ETA,'shared_source_probability':PZ,
 'raw_states':1<<N,'discovered_component_states':1<<M,
 'task_pair_supplied':list(pairs[0]),'discovered_pairs':[list(p) for p in learned],
 'whole_min_probability':float(min(A.min(),B.min(),L.min())),
 'joint_quotient_kernel_error':float(np.max(abs(KA-expected[qid]))),
 'two_world_task_kernel_difference':float(np.max(abs(KB-KA))),
 'enlarged_candidate_closure_error_A':float(closureA),'enlarged_candidate_closure_error_B':float(closureB),
 'nonzero_leakage_probability':DELTA,'leakage_max_quotient_TV':float(leakTV.max()),
 'leakage_exact_closure_error':float(leakClosure),'deconvolved_max_latent_error':float(latent_error.max()),
 'gram_degree':dgram,'biased_gram_min_eigenvalue':lmin,'proved_gram_lower_bound':1/Cg,
 'sampled_records':sample_count,'sampled_max_response_error':max(sample_max_errors),
 'sampled_next_pair_supports_correct':True,
 'conservative_confidence_precondition_satisfied':finite_precondition,
 'finite_sample_claim':'Empirical support recovery only; conservative rigorous confidence bound is vacuous at this sample count.',
 'symbolic_growth':[{'m':m,'raw_states':str(4**m),'quotient_states':str(2**m),'queries':m,'degree12_features':sum(math.comb(2*m,k) for k in range(min(12,2*m)+1))} for m in [4,8,16,32]],
 'response_polynomials':response_polys,
}
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))

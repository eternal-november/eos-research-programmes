#!/usr/bin/env python3
"""Direct proposal/checking scores: no conditional-polynomial dictionary.
Data-selected parity supports and a bounded Boolean gate are checked by a
uniform finite-sample confidence bound over the entire admitted grammar.
"""
import itertools,json,math
from pathlib import Path
import numpy as np
rng=np.random.default_rng(20261029)
m=4;n=2*m;eta=.17;c=1-2*eta;pz=.25;records=200000
perm=rng.permutation(n);truth=[tuple(sorted(map(int,perm[2*i:2*i+2]))) for i in range(m)]
# Uniform is stationary for this nonlinear permutation + affine residual map
# followed by independent bit-noise. Independent stationary records generated.
x=rng.integers(0,2,size=(records,n),dtype=np.int8)
q=np.array([x[:,a]^x[:,b] for a,b in truth]).T
r=x[:,perm[::2]]
f=np.column_stack([q[:,1:],q[:,0]^(q[:,1]&q[:,-1])])
off=np.column_stack([q[:,i]&q[:,(i+1)%m] for i in range(m)])
z=(rng.random(records)<pz).astype(np.int8)
rr=r^off^z[:,None]
y=np.zeros_like(x)
for i,(a,b) in enumerate([tuple(perm[2*j:2*j+2]) for j in range(m)]):
 y[:,a]=rr[:,i];y[:,b]=rr[:,i]^f[:,i]
xnext=y^(rng.random((records,n))<eta).astype(np.int8)
pairs=list(itertools.combinations(range(n),2));P=len(pairs)
cur=np.array([1-2*(x[:,a]^x[:,b]) for a,b in pairs],dtype=float).T
nxt=np.array([1-2*(xnext[:,a]^xnext[:,b]) for a,b in pairs],dtype=float).T
learned=[truth[0]];chosen=[]
gates=1-2*((np.arange(256)[:,None]>>np.arange(8))&1)
for iteration in range(n):
 S=learned[-1];j=pairs.index(S);target=nxt[:,j]
 corr=cur.T@target/records
 k=int(np.argmax(corr));normalized=corr[k]/(c*c)
 if normalized>.9: # proposer heuristic only; validity checked separately
  T=pairs[k]
  if T in learned:raise AssertionError('Unexpected repeated shift candidate')
  chosen.append({'output':S,'kind':'copy','input':T,'correlation':float(corr[k])})
  learned.append(T)
 else:
  best=None
  for inds in itertools.combinations(range(len(learned)),3):
   qq=np.array([(1-cur[:,pairs.index(learned[i])])/2 for i in inds],dtype=np.int8).T
   pat=(qq*(1<<np.arange(3))).sum(1)
   sums=np.bincount(pat,weights=target,minlength=8)
   scores=gates@sums/records
   g=int(np.argmax(scores));val=float(scores[g])
   if best is None or val>best[0]:best=(val,inds,g)
  assert best is not None
  val,inds,g=best
  chosen.append({'output':S,'kind':'gate3','input_indices':inds,'truth_table_integer':g,'correlation':val})
  break
else:raise AssertionError('No closure proposal found')
# Ground truth used only after inference.
assert learned==truth
allx=((np.arange(1<<n)[:,None]>>np.arange(n))&1).astype(np.int8)
allq=np.array([allx[:,a]^allx[:,b] for a,b in learned]).T
last=chosen[-1];pattern=(allq[:,last['input_indices']]*(1<<np.arange(3))).sum(1)
pred=(last['truth_table_integer']>>pattern)&1
assert np.array_equal(pred,allq[:,0]^(allq[:,1]&allq[:,-1]))
# Union bound includes every output pair, every input pair, and every
# Boolean gate of three pair parities, not merely the queries finally chosen.
class_size=P*P+P*math.comb(P,3)*256
alpha=.05
t=math.sqrt(2*math.log(2*class_size/alpha)/records)
for choice in chosen:
 choice['latent_error_estimate']=(1-choice['correlation']/(c*c))/2
 choice['latent_error_upper']=min(1.,max(0.,(1-(choice['correlation']-t)/(c*c))/2))
budget=sum(a['latent_error_upper'] for a in chosen)
# Freeze the proposal, then validate on fresh independent records. This bound
# conditions on the training data and pays only for the m selected equations.
validation_records=200000
vx=rng.integers(0,2,size=(validation_records,n),dtype=np.int8)
vq=np.array([vx[:,a]^vx[:,b] for a,b in truth]).T
vr=vx[:,perm[::2]]
vf=np.column_stack([vq[:,1:],vq[:,0]^(vq[:,1]&vq[:,-1])])
voff=np.column_stack([vq[:,i]&vq[:,(i+1)%m] for i in range(m)])
vz=(rng.random(validation_records)<pz).astype(np.int8)
vrr=vr^voff^vz[:,None]
vy=np.zeros_like(vx)
for i,(a,b) in enumerate([tuple(perm[2*j:2*j+2]) for j in range(m)]):
 vy[:,a]=vrr[:,i];vy[:,b]=vrr[:,i]^vf[:,i]
vnext=vy^(rng.random((validation_records,n))<eta).astype(np.int8)
validation_margin=math.sqrt(math.log(2*len(chosen)/alpha)/(2*validation_records))/(c*c)
for choice in chosen:
 a,b=choice['output'];outsign=1-2*(vnext[:,a]^vnext[:,b])
 if choice['kind']=='copy':
  a,b=choice['input'];predsign=1-2*(vx[:,a]^vx[:,b])
 else:
  inputs=[learned[i] for i in choice['input_indices']]
  values=np.array([vx[:,a]^vx[:,b] for a,b in inputs]).T
  pat=(values*(1<<np.arange(3))).sum(1)
  predsign=1-2*((choice['truth_table_integer']>>pat)&1)
 mu=float(np.mean(outsign*predsign))
 dhat=(1-mu/(c*c))/2
 choice['holdout_correlation']=mu
 choice['holdout_latent_error_upper']=min(1.,max(0.,dhat+validation_margin))
validation_budget=sum(a['holdout_latent_error_upper'] for a in chosen)
result={'status':'PASS','seed':20261029,'records':records,'n':n,'m':m,
 'eta':eta,'confidence':1-alpha,'candidate_score_class_size':class_size,
 'correlation_tolerance':t,'discovered_pairs':[list(p) for p in learned],
 'unknown_pairs_recovered':True,'nonlinear_gate_recovered':True,
 'selected_witnesses':chosen,'one_step_stationary_failure_budget':budget,
 'ten_step_stationary_transcript_TV_upper':min(1.,10*budget),
 'fresh_validation_records':validation_records,'holdout_confidence':1-alpha,
 'holdout_one_step_stationary_failure_budget':validation_budget,
 'holdout_ten_step_stationary_transcript_TV_upper':min(1.,10*validation_budget),
 'scope':'Bound covers the stationary unchanged-physics deployment distribution; not a uniform conditional-on-x or hidden-mode guarantee. Exact support result needs exact moments; finite samples certify only approximation.',
 'degree_dictionary_used':False,'known_independent_process_noise_required':True,
 'grammar':'All next pair parities versus all input pair parities or all Boolean functions of three input pair parities.',
 'selection_rule':'Empirical pair score >0.9 proposes shift; otherwise maximum-score gate3. Confidence validity does not depend on this heuristic selecting the true structure.'}
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))

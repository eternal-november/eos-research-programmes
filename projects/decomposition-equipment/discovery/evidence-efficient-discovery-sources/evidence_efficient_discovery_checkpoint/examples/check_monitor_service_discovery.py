#!/usr/bin/env python3
"""Unknown recursive local scopes; independent finite-operational-family validation.
Synthetic generator used only to acquire data. Candidate probabilities are learned.
"""
from pathlib import Path
from itertools import product,combinations
from fractions import Fraction as F
from collections import defaultdict
import json,math
import numpy as np
OUT=Path(__file__).parent
H=8; NTRAIN=10000; NVALID=50000; SEED=202610291611
PAIRS=list(product((0,1),repeat=2)); TRIPLES=[tuple(c for t in times for c in (2*t,2*t+1)) for times in combinations(range(H+1),3)]
POLICIES=['clear','busy','crossed','remembered_change']
def actions(name,z,y,rng=None):
 if name=='exploration':return rng.integers(0,2,size=y.shape)
 if name=='clear':return 1-y
 if name=='busy':return y.copy()
 if name=='crossed':return np.stack((y[:,1],1-y[:,0]),axis=1)
 return np.bitwise_xor(z,y)
def acquire(n,policy,seed):
 rng=np.random.default_rng(seed);s=rng.integers(0,2,size=(n,H+2,2));aa=[]
 for t in range(H):
  z,y=s[:,t],s[:,t+1];a=actions(policy,z,y,rng);aa.append(a)
  p=(1+3*a[:,0]+2*z[:,0]+2*y[:,1])/10
  q=(1+3*a[:,1]+2*z[:,1]+2*y[:,0])/10
  common=rng.integers(0,2,n).astype(bool);u=rng.integers(0,10,n);v=rng.integers(0,10,n);v=np.where(common,u,v)
  s[:,t+2,0]=(u<10*p);s[:,t+2,1]=(v<10*q)
 return s,np.stack(aa,axis=1)
train,acts=acquire(NTRAIN,'exploration',SEED)
# Proposal: all64 coordinate masks per port, BIC, entirely observed transitions.
contexts=np.concatenate((train[:,1:-1],train[:,:-2],acts),axis=2).reshape(-1,6)
outs=train[:,2:].reshape(-1,2)
local=[];masks=[];bics=[]
for port in range(2):
 options=[]
 for k in range(7):
  for mask in combinations(range(6),k):
   idx=sum((contexts[:,j]<<(k-1-i) for i,j in enumerate(mask)),start=np.zeros(len(contexts),dtype=int))
   counts=np.bincount(idx,minlength=2**k);ones=np.bincount(idx,weights=outs[:,port],minlength=2**k)
   pp=np.clip(ones/np.maximum(counts,1),1e-12,1-1e-12)
   ll=float(np.sum(ones*np.log(pp)+(counts-ones)*np.log(1-pp)))
   bic=-2*ll+(2**k)*math.log(len(contexts));options.append((bic,mask,ones,counts))
 best=min(options,key=lambda a:a[0]);bic,mask,ones,counts=best;masks.append(mask)
 vals=[F(round(10*float(s/n)),10) for s,n in zip(ones,counts)];local.append(vals)
 bics.append({'selected':bic,'runner_up':sorted(x[0] for x in options)[1]})
# Estimate shared-source mixture via all training transitions; rounding is proposal only.
pred=[]
for port in range(2):
 mask=masks[port];idx=sum((contexts[:,j]<<(len(mask)-1-i) for i,j in enumerate(mask)),start=np.zeros(len(contexts),dtype=int))
 pred.append(np.array([float(x) for x in local[port]])[idx])
p,q=pred;d=np.minimum(p,q)-p*q
lam_raw=float(np.sum(d*(outs[:,0]*outs[:,1]-p*q))/np.sum(d*d));lam=F(round(10*lam_raw),10)
assert 0<=lam<=1
initial_counts=np.bincount((train[:,0,0]*8+train[:,0,1]*4+train[:,1,0]*2+train[:,1,1]),minlength=16)
# Rounded positive initial law is proposed, NOT assumed physically true.
nu=[F(round(16*int(n)/NTRAIN),16) for n in initial_counts];assert sum(nu)==1

def kernel(z,y,a,variant='learned'):
 c=y+z+a;pp=[]
 for i in range(2):
  mask=masks[i];ix=sum(c[j]<<(len(mask)-1-k) for k,j in enumerate(mask));pp.append(local[i][ix])
 p,q=pp
 if variant=='no_memory':
  p=(kernel_marg((0,z[1]),y,a,0)+kernel_marg((1,z[1]),y,a,0))/2
  q=(kernel_marg((z[0],0),y,a,1)+kernel_marg((z[0],1),y,a,1))/2
 if variant=='no_message':
  p=(kernel_marg(z,(y[0],0),a,0)+kernel_marg(z,(y[0],1),a,0))/2
  q=(kernel_marg(z,(0,y[1]),a,1)+kernel_marg(z,(1,y[1]),a,1))/2
 l=F(0) if variant=='independent' else lam
 both=(1-l)*p*q+l*min(p,q)
 return (1-p-q+both,q-both,p-both,both)
def kernel_marg(z,y,a,i):
 c=y+z+a;mask=masks[i];ix=sum(c[j]<<(len(mask)-1-k) for k,j in enumerate(mask));return local[i][ix]
def action_one(name,z,y):
 if name=='clear':return tuple(1-x for x in y)
 if name=='busy':return y
 if name=='crossed':return(y[1],1-y[0])
 return tuple(x^v for x,v in zip(z,y))

# Exact projection probabilities by integer DP (positive rational learned model).
# Each selected bit is from y_t; state=(z_t,y_t), recursive memory never fullhistory.
def exact_projection(policy,coords,variant='learned'):
 last=max(coords)//2;selected={c:k for k,c in enumerate(coords)}
 trans={};den=1
 for z,y in product(PAIRS,repeat=2):
  law=kernel(z,y,action_one(policy,z,y),variant);trans[(z,y)]=law
  for p in law:den=math.lcm(den,p.denominator)
 weights={k:[int(p*den) for p in v] for k,v in trans.items()}
 initden=math.lcm(*(p.denominator for p in nu));state={}
 for j,(z,y) in enumerate(product(PAIRS,repeat=2)):
  word=sum(y[c%2]<<(len(coords)-1-selected[c]) for c in coords if c//2==0)
  state[(z,y,word)]=int(nu[j]*initden)
 for t in range(last):
  nxt=defaultdict(int)
  for (z,y,word),mass in state.items():
   for u,w in zip(PAIRS,weights[(z,y)]):
    ww=word+sum(u[c%2]<<(len(coords)-1-selected[c]) for c in coords if c//2==t+1)
    nxt[(y,u,ww)]+=mass*w
  state=nxt
 result=[0]*(2**len(coords))
 for (_,_,word),mass in state.items():result[word]+=mass
 denominator=initden*den**last;assert sum(result)==denominator
 return result,denominator

# Freeze the training-selected candidate before examining held-out observations.
frozen={'masks':masks,'local':[[str(x) for x in row] for row in local],'shared_weight':str(lam),'initial':[str(x) for x in nu],'training_seed':SEED}
(OUT/'monitor_service_frozen_candidate.json').write_text(json.dumps(frozen,indent=2)+'\n')
# Additional grammar fixed before this fresh validation: full-run max run length
# of each of the four joint readout symbols. The predictor stays unchanged.
def exact_monitor(policy,symbol):
 den=200; state={}
 for j,(z,y) in enumerate(product(PAIRS,repeat=2)):
  r=int(y==symbol);state[(z,y,r,r)]=int(nu[j]*16)
 for t in range(H):
  nxt=defaultdict(int)
  for (z,y,run,mx),mass in state.items():
   for u,p in zip(PAIRS,kernel(z,y,action_one(policy,z,y))):
    w=p*den;assert w.denominator==1
    rr=run+1 if u==symbol else 0
    nxt[(y,u,rr,max(mx,rr))]+=mass*w.numerator
  state=nxt
 result=[0]*(H+2)
 for (_,_,_,mx),mass in state.items():result[mx]+=mass
 denominator=16*den**H;assert sum(result)==denominator
 return result,denominator
results={};all_max=F(0);all_hist=[]; predictions=[];monitors=[]
# Preregistered radius .0231: failure <=4*84*(2^64-2)*exp(-2*50000*.0231^2)<.05.
R=F(231,10000);exponent=2*NVALID*R*R
# Exact Taylor lower bound for exp(exponent), no floating confidence arithmetic.
exp_lower=sum((exponent**k/F(math.factorial(k)) for k in range(100)),F(0))
failure=F(len(POLICIES)*(len(TRIPLES)*(2**64-2)+4*(2**(H+2)-2)),1)/exp_lower;assert failure<F(1,20)
for pidx,policy in enumerate(POLICIES):
 held,held_actions=acquire(NVALID,policy,SEED+10000+pidx);np.savez_compressed(OUT/('monitor_service_holdout_'+policy+'.npz'),readouts=held,actions=held_actions);flat=held[:,1:].reshape(NVALID,-1)
 maxfit=F(0);worst=None;histrows=[];predrows=[]
 for coords in TRIPLES:
  word=sum((flat[:,c]<<(len(coords)-1-k) for k,c in enumerate(coords)),start=np.zeros(NVALID,dtype=int))
  hist=np.bincount(word,minlength=64);num,den=exact_projection(policy,coords)
  fit=sum(abs(F(int(n),NVALID)-F(q,den)) for n,q in zip(hist,num))/2
  if fit>maxfit:maxfit=fit;worst=coords
  histrows.append([list(coords),[int(x) for x in hist]])
  predrows.append([list(coords),num,den])
 monitorrows=[]
 for symbol in PAIRS:
  run=np.zeros(NVALID,dtype=int);mx=np.zeros(NVALID,dtype=int)
  for t in range(H+1):
   match=np.all(held[:,t+1]==np.array(symbol),axis=1)
   run=np.where(match,run+1,0);mx=np.maximum(mx,run)
  hist=np.bincount(mx,minlength=H+2);num,den=exact_monitor(policy,symbol)
  fit=sum(abs(F(int(n),NVALID)-F(q,den)) for n,q in zip(hist,num))/2
  maxfit=max(maxfit,fit)
  monitorrows.append({'symbol':symbol,'counts':[int(x) for x in hist],'prediction_numerators':num,'prediction_denominator':den,'TV_fit':str(fit),'TV_bound':str(fit+R)})
 monitors.append({'policy':policy,'max_run_monitors':monitorrows})
 all_max=max(all_max,maxfit);all_hist.append({'policy':policy,'histograms':histrows});predictions.append({'policy':policy,'probabilities':predrows})
 results[policy]={'maximum_projection_TV_fit':float(maxfit),'worst_coordinates':worst,'certified_bound':float(maxfit+R)}
 print(policy,results[policy],flush=True)
assert all_max+R<F(1,20)
assert masks==[(1,2,4),(0,3,5)]
# Exact simpler-model witnesses for practically important missing resources.
ablations={}
for variant in ['no_memory','no_message','independent']:
 best=(F(0),None,None)
 for policy in POLICIES:
  # First three joint readout times suffice for resource-ablation witnesses.
  for coords in [tuple(range(6))]:
   a,d=exact_projection(policy,coords);b,e=exact_projection(policy,coords,variant)
   tv=sum(abs(F(x,d)-F(y,e)) for x,y in zip(a,b))/2
   if tv>best[0]:best=(tv,policy,coords)
 policy,coords=best[1:];rows=all_hist[POLICIES.index(policy)]['histograms'];hist=next(h for cc,h in rows if tuple(cc)==coords);nums,dd=exact_projection(policy,coords,variant)
 empirical=sum(abs(F(n,NVALID)-F(q,dd)) for n,q in zip(hist,nums))/2
 lower=max(F(0),empirical-R);assert lower>F(1,20)
 ablations[variant]={'candidate_projection_TV_separation':float(best[0]),'exact':str(best[0]),'policy':policy,'coordinates':coords,'heldout_TV_lower_bound':float(lower),'exact_heldout_TV_lower_bound':str(lower)}
report={'status':'PASS','seed':SEED,'H':H,'training_episodes':NTRAIN,'heldout_episodes_per_controller':NVALID,'total_episodes':NTRAIN+len(POLICIES)*NVALID,'total_observed_transitions':H*(NTRAIN+len(POLICIES)*NVALID),'old_episodes':10240000,'old_H':2,'episode_reduction_factor':10240000/(NTRAIN+len(POLICIES)*NVALID),'transition_reduction_factor':20480000/(H*(NTRAIN+len(POLICIES)*NVALID)),'learned_masks':masks,'local_probabilities':[[str(p) for p in v] for v in local],'BIC':bics,'learned_shared_weight_raw':lam_raw,'learned_shared_weight':str(lam),'initial_law':[str(p) for p in nu],'projection_count':len(TRIPLES),'projection_alphabet':64,'confidence_radius':str(R),'confidence_failure_upper_bound':float(failure),'exact_confidence_failure_bound':str(failure),'uniform_certificate':float(all_max+R),'controllers':results,'ablations':ablations,'qualification':'Full trajectory TV and all adaptive controllers are NOT certified. Guarantee is TV for every three-time joint readout projection under each of four declared feedback controllers, hence every bounded function on any such projection; additionally every bounded function of the maximal run length of each joint readout symbol over the full run. No Markov or model-class assumption on physical law; repeated IID episodes and policy-invariant sampling conditions required. Learning scopes is heuristic; certificate is independent and exact on provided counts.'}
report['fresh_validation_seeds']=[SEED+10000+i for i in range(4)]
report['cumulative_study_episodes']=500000
report['fresh_validation_episodes']=200000
report['additional_monitor_count']=4
report['additional_monitor_alphabet']=10
(OUT/'monitor_service_monitor_results.json').write_text(json.dumps(monitors,indent=2)+'\n')
(OUT/'monitor_service_results.json').write_text(json.dumps(report,indent=2)+'\n')
(OUT/'monitor_service_holdout_histograms.json').write_text(json.dumps(all_hist,separators=(',',':'))+'\n')
(OUT/'monitor_service_exact_predictions.json').write_text(json.dumps(predictions,separators=(',',':'))+'\n')
np.savez_compressed(OUT/'monitor_service_training.npz',readouts=train,actions=acts)
print(json.dumps(report,indent=2))

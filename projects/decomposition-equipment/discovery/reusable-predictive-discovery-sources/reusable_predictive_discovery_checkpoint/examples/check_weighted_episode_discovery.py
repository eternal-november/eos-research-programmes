#!/usr/bin/env python3
"""Data-derived reusable predictor, prefix-weighted robust TV certificate."""
from pathlib import Path
from fractions import Fraction as F
import json,math
OUT=Path(__file__).parent
# Reuse the complete proposal/search code, stopping BEFORE its uniform validator.
source=(OUT/'check_sampled_episode_discovery.py').read_text().split('# Fixed confidence construction:')[0]
source=source.replace("N=base['N']; seed=202610291529","N=10240000; seed=202610291533")
exec(compile(source,str(OUT/'check_sampled_episode_discovery.py'),'exec'))
def tv(a,b):return sum(abs(x-y) for x,y in zip(a,b))/2
# Explicit common driver: uniform integer0..199, not uncharged sharedrandomness.
# R<100 gives a shared threshold, R>=100 gives independentthreshold pair.
for c in table:
 p,q=[local[i][tuple(c[j] for j in minimal[i][0])] for i in (0,1)]
 frequencies=[0]*4
 for r in range(200):
  u,v=(r//10,r//10) if r<100 else ((r-100)//10,(r-100)%10)
  frequencies[2*int(F(u,10)<p)+int(F(v,10)<q)]+=1
 assert tuple(F(n,200) for n in frequencies)==K(c[2:4],c[:2],c[4:6])
# Compile selected lag scopes to explicit two local 1-bit memories; currentneighbor messages.
# No runtime read of an archived history is allowed in this compiled predictor.
def compiled_tick(memory,current,own_actions):
 forecast=K(memory,current,own_actions)
 return forecast,current
for z,y,a,u,b,v,n in leaves:
 first,memory=compiled_tick(z,y,a)
 second,memory=compiled_tick(memory,u,b)
 assert first==K(z,y,a) and second==K(y,u,b) and memory==u
M=len(rows);den=10**6
# Fixed exact exponent thresholds, independent of the observed random rowcounts.
L=F(13);L0=F(16)
def radius(n,logbound):
 if n==0:return F(1)
 target=logbound*den*den/(2*n)
 k=math.isqrt(target.numerator//target.denominator)
 if k*k*target.denominator<target.numerator:k+=1
 r=min(F(1),F(k,den))
 assert r==1 or r*r>=logbound/(2*n)
 return r
radii={h:radius(sum(c),L) for h,c in rows.items()}
rinit=radius(N,L0)
# Exact maximization over a totalvariation ball by moving mass from low to high reward.
def robust_expectation(emp,r,values):
 p=list(emp);budget=r
 low=sorted(range(len(p)),key=lambda i:values[i]);high=list(reversed(low))
 lo=hi=0
 while budget>0 and lo<len(p) and hi<len(p):
  s,d=low[lo],high[hi]
  if values[d]<=values[s]:break
  if not p[s]:lo+=1;continue
  if p[d]==1:hi+=1;continue
  amount=min(budget,p[s],1-p[d]);p[s]-=amount;p[d]+=amount;budget-=amount
 assert sum(p)==1 and min(p)>=0 and tv(p,emp)<=r
 return sum(a*b for a,b in zip(p,values))
gamma={};fit={}
for (t,h,a),emp in rowlaws.items():
 z,y=h if not t else (h[1],h[3]);fit[(t,h,a)]=tv(emp,K(z,y,a))
 gamma[(t,h,a)]=min(F(1),fit[(t,h,a)]+radii[(t,h,a)])
# Robust history-by-history DP maximizes over ALL adaptive actions and all kernels in TVballs.
V1={}
for t,h,a in rows:
 if t==1:V1[h]=max(V1.get(h,F(0)),gamma[(t,h,a)])
V0={}
for z,y in product(PAIR,repeat=2):
 h=(z,y);options=[]
 for a in PAIR:
  values=[V1[h+(a,out)] for out in PAIR]
  options.append(gamma[(0,h,a)]+robust_expectation(rowlaws[(0,h,a)],radii[(0,h,a)],values))
 V0[h]=max(options)
initkeys=list(product(PAIR,repeat=2));empinit=[F(initial[k],N) for k in initkeys]
nominit=[F(1,16)]*16
initialgap=min(F(1),rinit+tv(empinit,nominit))
weighted=initialgap+robust_expectation(empinit,rinit,[V0[k] for k in initkeys])
uniform=initialgap+sum(max(gamma[r] for r in rows if r[0]==t) for t in (0,1))
# The nominal predictor law is a compatible witness for cheaper-class lowerbounds.
nominal_feasible=all(fit[r]<=radii[r] for r in rows) and tv(empinit,nominit)<=rinit
assert nominal_feasible
assert weighted<F(1,20)
rounded=F(math.ceil(weighted*den),den)
assert weighted<=rounded<F(1,20)
def exp_lower(t):
 return sum((F(t)**k)/math.factorial(k) for k in range(101))
# Taylor sums are exact LOWER bounds on exp(t), giving fixed unconditional union bound.
confidence_cond=F(14*M)/exp_lower(13)
confidence_init=F(65534)/exp_lower(16)
confidence_total=confidence_cond+confidence_init
assert confidence_total<F(41804218,10**9)<F(1,20)
# Exact expected first-step TV lowerbound for either omitted memory or omittedneighbor.
weighted_lower={}
for label,coord in [('no_previous_own_readout',0),('no_neighbor_current_readout',3)]:
 lower=F(0)
 for root in product((0,1),repeat=4):
  if root[coord]:continue
  other=list(root);other[coord]=1;other=tuple(other)
  z,y=root[:2],root[2:];zz,yy=other[:2],other[2:]
  p=marg(K(z,y,tuple(1-x for x in y)),0);q=marg(K(zz,yy,tuple(1-x for x in yy)),0)
  lower+=abs(p-q)/16
 assert lower==F(1,10)
 weighted_lower[label]=str(lower)
# Optional fixed-deadline source approximation:20 fair bits, s=floor(200U/2^20).
Lbits=1<<20
ceildiv=lambda a,b:(a+b-1)//b
source_counts=[ceildiv((j+1)*Lbits,200)-ceildiv(j*Lbits,200) for j in range(200)]
assert sum(source_counts)==Lbits
source_tv=sum(abs(F(n,Lbits)-F(1,200)) for n in source_counts)/2
assert source_tv==F(33,1638400)
for c in table:
 p,q=[local[i][tuple(c[j] for j in minimal[i][0])] for i in (0,1)]
 masses=[F(0)]*4
 for r,n in enumerate(source_counts):
  u,v=(r//10,r//10) if r<100 else ((r-100)//10,(r-100)%10)
  masses[2*int(F(u,10)<p)+int(F(v,10)<q)]+=F(n,Lbits)
 assert tv(masses,K(c[2:4],c[:2],c[4:6]))<=source_tv
bounded_source_J=weighted+2*source_tv
bounded_source_rounded=F(math.ceil(bounded_source_J*den),den)
assert bounded_source_rounded<F(44,1000)<F(1,20)
report={'status':'PASS','synthetic_iid_episodes':N,'seed':seed,'H':2,'full_history_rows':M,
 'minimum_row_count':min(sum(c) for c in rows.values()),'confidence_failure_bound':float(confidence_total),'confidence_failure_bound_exact':str(confidence_total),'confidence_exponent_thresholds':[13,16],
 'minimum_conditional_TV_radius':float(min(radii.values())),'maximum_conditional_TV_radius':float(max(radii.values())),
 'data_discovered_masks':minimal,'data_proposed_shared_weight':str(lam),'positive_response_atoms':110,'compiled_recurrent_memory_bits_per_port':1,'current_observation_message_bits_per_port':1,'shared_driver_alphabet':200,'driver_to_port_threshold_alphabet':10,'driver_to_port_fixed_binary_bits':4,'compiled_two_tick_traces_checked':len(leaves),
 'nominal_positive_law_inside_confidence_set':nominal_feasible,
 'initial_law_gap_bound':float(initialgap),'weighted_all_controller_J_upper_bound':float(weighted),'weighted_all_controller_path_TV_bound':float(weighted),
 'weighted_exact_rational':str(weighted),'uniform_worst_prefix_path_TV_bound':float(uniform),
 'cheaper_context_weighted_J_lowerbounds':weighted_lower,
 'acceptance_threshold':'1/20','weighted_accepted':weighted<=F(1,20),'uniform_accepted':uniform<=F(1,20),'outward_rounded_bound':str(rounded),
 'scope':'Two supplied readout ports; predictive scopes/memory/messages discovered, not physical partition identity',
 'bounded_source_fair_bits_per_tick':20,'bounded_source_TV':str(source_tv),'bounded_source_J_upper':float(bounded_source_J),'bounded_source_J_outward':str(bounded_source_rounded),
 'sampling':'Seeded compressed multinomial IID synthetic episodes; no physical data; all episode count charged',
 'confidence_universe':'All finite-horizon causal laws satisfying measured fullhistory conditionalTVballs; noMarkovpromise',
 'DP_scope':'Rectangular fullhistory uncertainty is justified by these specific evidence constraints; not general sharedparameterrectangularization'}
(OUT/'weighted_episode_discovery_checks.json').write_text(json.dumps(report,indent=2)+'\n')
data={'provenance':report['sampling'],'N':N,'seed':seed,'columns':base['columns'],'episodes':leaves}
(OUT/'weighted_sampled_service_histogram.json').write_text(json.dumps(data,separators=(',',':'))+'\n')
print(json.dumps(report,indent=2))

#!/usr/bin/env python3
"""Seeded IID synthetic episode sampling, compressed multinomial histogram.
Proposal search sees histogram only. Full-history validation assumes no Markov model.
"""
from fractions import Fraction as F
from itertools import product, combinations
from collections import defaultdict
from pathlib import Path
import json,math
import numpy as np
OUT=Path(__file__).parent
base=json.loads((OUT/'constructed_service_episode_histogram.json').read_text())
N=base['N']; seed=202610291529
# A multinomial count draw has EXACTLY the histogram distribution of N IID episodes.
# Floating arithmetic approximates the rational generating probabilities, as noted in report.
probs=np.array([row[-1]/N for row in base['episodes']],dtype=float)
probs/=probs.sum()
cts=np.random.default_rng(seed).multinomial(N,probs)
leaves=[tuple(tuple(v) for v in row[:-1])+(int(n),) for row,n in zip(base['episodes'],cts)]
PAIR=list(product((0,1),repeat=2))
initial=defaultdict(int);rows=defaultdict(lambda:[0]*4)
for z,y,a,u,b,v,n in leaves:
 initial[(z,y)]+=n;rows[(0,(z,y),a)][PAIR.index(u)]+=n;rows[(1,(z,y,a,u),b)][PAIR.index(v)]+=n
rowlaws={r:tuple(F(n,sum(c)) for n in c) for r,c in rows.items()}
table={};tablecounts={}
for (t,h,a),law in rowlaws.items():
 if not t:
  z,y=h;table[y+z+a]=law;tablecounts[y+z+a]=rows[(t,h,a)]
def marg(k,i):return k[2]+k[3] if not i else k[1]+k[3]
# Fixed proposal tolerance, not itself the confidence test.
tolerance=F(1,100);minimal=[]
for i in (0,1):
 feasible=[]
 for size in range(7):
  for mask in combinations(range(6),size):
   groups=defaultdict(list)
   for c,k in table.items():groups[tuple(c[j] for j in mask)].append(marg(k,i))
   if all(max(g)-min(g)<=tolerance for g in groups.values()):feasible.append(mask)
 minimal.append([m for m in feasible if not any(set(k)<set(m) for k in feasible)])
assert minimal==[[(1,2,4)],[(0,3,5)]]
local=[]
for i in (0,1):
 groups=defaultdict(lambda:[0,0])
 for c,counts in tablecounts.items():
  key=tuple(c[j] for j in minimal[i][0]); groups[key][0]+=counts[2]+counts[3] if not i else counts[1]+counts[3];groups[key][1]+=sum(counts)
 # Coarse rational rounding is only a proposal heuristic, not a model-class promise.
 local.append({key:F(round(10*F(s,n)),10) for key,(s,n) in groups.items()})
lams=[]
for c,k in table.items():
 p,q=[local[i][tuple(c[j] for j in minimal[i][0])] for i in (0,1)]
 lams.append(float((k[3]-p*q)/(min(p,q)-p*q)))
lam=F(round(10*float(np.median(lams))),10)
assert lam==F(1,2)
def K(z,y,a):
 c=y+z+a;p,q=[local[i][tuple(c[j] for j in minimal[i][0])] for i in (0,1)]
 out=[F(0)]*4
 for u in range(10):out[2*int(F(u,10)<p)+int(F(u,10)<q)]+=F(1,20)
 for u,v in product(range(10),repeat=2):out[2*int(F(u,10)<p)+int(F(v,10)<q)]+=F(1,200)
 assert sum(out)==1 and min(out)>0
 return tuple(out)
def tv(a,b):return sum(abs(x-y) for x,y in zip(a,b))/2
# Fixed confidence construction: 1088*4 conditional cells,16 initialcells.
eps=F(1,80);e0=F(1,4096);min_required=39000
minimum=min(sum(c) for c in rows.values());assert minimum>=min_required
# This is a preregistered minimum-count acceptance event, not plug-in confidence after selection.
failure_bound=8*1088*math.exp(-2*min_required*float(eps)**2)+32*math.exp(-2*N*float(e0)**2)
assert failure_bound<.05
max_tv=[F(0),F(0)];maxcell=F(0)
for (t,h,a),emp in rowlaws.items():
 z,y=h if not t else (h[1],h[3]);pred=K(z,y,a)
 max_tv[t]=max(max_tv[t],tv(emp,pred));maxcell=max(maxcell,max(abs(x-y) for x,y in zip(emp,pred)))
# Check nominal constructed candidate is an explicit member of the confidence law set.
assert maxcell<=eps
emp_initial=[F(initial[(z,y)],N) for z,y in product(PAIR,repeat=2)]
nominal_initial=[F(1,16)]*16
assert max(abs(x-y) for x,y in zip(emp_initial,nominal_initial))<=e0
initial_tv=tv(emp_initial,nominal_initial)+8*e0
certified_tv=initial_tv+sum(x+2*eps for x in max_tv)
assert certified_tv<F(1,10)
# Two feedback controllers: displayed candidate and evidence-derived comparison.
policies={'request_when_clear':lambda y:tuple(1-v for v in y),'request_when_busy':lambda y:y}
policy_stats={}
for name,policy in policies.items():
 nominal={(z,y):F(1,16) for z,y in product(PAIR,repeat=2)}
 empirical={(z,y):F(initial[(z,y)],N) for z,y in product(PAIR,repeat=2)}
 for t in range(2):
  nn={};ee={}
  for h,mass in nominal.items():
   z,y=h if not t else (h[1],h[3]);a=policy(y);pred=K(z,y,a);emp=rowlaws[(t,h,a)]
   for out,p,q in zip(PAIR,pred,emp):nn[h+(a,out)]=mass*p;ee[h+(a,out)]=empirical[h]*q
  nominal,empirical=nn,ee
 assert sum(nominal.values())==sum(empirical.values())==1
 policy_stats[name]={'terminal_histories':len(nominal),'empirical_law_vs_candidate_TV':float(tv(list(nominal.values()),list(empirical.values())))}
# Nominal confidence-compatible causal law rejects cheaper contexts by weighted pairing.
weighted={}
for label,coord in [('no_previous_own_readout',0),('no_neighbor_current_readout',3)]:
 lower=F(0)
 for root in product((0,1),repeat=4):
  if root[coord]:continue
  other=list(root);other[coord]=1;other=tuple(other)
  z,y=root[:2],root[2:];zz,yy=other[:2],other[2:]
  p=marg(K(z,y,policies['request_when_clear'](y)),0);q=marg(K(zz,yy,policies['request_when_clear'](yy)),0)
  lower+=abs(p-q)/16
 assert lower==F(1,10) and lower>certified_tv
 weighted[label]=str(lower)
data={'provenance':'Seeded NumPy multinomial synthetic IID-episode histogram; not physical data','seed':seed,'N':N,
 'columns':base['columns'],'episodes':leaves}
(OUT/'sampled_service_episode_histogram.json').write_text(json.dumps(data,separators=(',',':'))+'\n')
report={'status':'PASS','H':2,'seed':seed,'synthetic_iid_episodes':N,'histogram_leaves':len(leaves),
 'all_full_history_action_rows':len(rows),'minimum_actual_row_count':minimum,'minimum_preregistered_acceptance_count':min_required,
 'confidence_failure_bound':failure_bound,'scope_tolerance':str(tolerance),'discovered_minimal_masks':minimal,
 'positive_shared_response_atoms':110,'proposed_shared_weight':str(lam),'conditional_cell_radius':str(eps),'initial_cell_radius':str(e0),
 'maximum_cell_fit_residual':float(maxcell),'maximum_empirical_TV_per_time':[float(x) for x in max_tv],
 'all_adaptive_controller_path_TV_bound':float(certified_tv),'exact_rational_bound':str(certified_tv),
 'nominal_model_in_confidence_set':True,'weighted_cheaper_context_lower_bounds':weighted,
 'explicit_feedback_controllers':policy_stats,
 'scope':'Input scopes around two supplied readout ports, not unknown physical subsystem count/partition',
 'sampling_note':'Multinomial sampling produces the IID-episode histogram directly; floating arithmetic approximates rational source probabilities. Confidence certificate is based on histogram, not source parameters.'}
(OUT/'sampled_episode_discovery_checks.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))

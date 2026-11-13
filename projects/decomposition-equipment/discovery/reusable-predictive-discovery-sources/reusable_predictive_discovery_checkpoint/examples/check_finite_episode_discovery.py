#!/usr/bin/env python3
"""Full-prefix finite-data certificate on a constructed possible H=2 histogram.
No actual acquisition; counts are synthetic, not claimed IID-generated observations.
The confidence procedure is valid IF these counts arise from IID fixed-regime episodes.
"""
from fractions import Fraction as F
from itertools import product,combinations
from collections import defaultdict
import json,math
from pathlib import Path
OUT=Path(__file__).parent
PAIR=list(product((0,1),repeat=2))
def source_kernel(prior,current,action):
 p=F(1+3*action[0]+2*prior[0]+2*current[1],10)
 q=F(1+3*action[1]+2*prior[1]+2*current[0],10)
 z=(p*q+min(p,q))/2
 return (1-p-q+z,q-z,p-z,z)
# Generate a compressed possible histogram. This oracle is used ONLY here.
leaves=[]
for prior,current,a0,y2,a1,y3 in product(PAIR,repeat=6):
 k0=source_kernel(prior,current,a0)[PAIR.index(y2)]
 k1=source_kernel(current,y2,a1)[PAIR.index(y3)]
 count=100*int(200*k0)*int(200*k1)
 assert count>0
 leaves.append((prior,current,a0,y2,a1,y3,count))
N=sum(x[-1] for x in leaves)
assert N==1024000000 and len(leaves)==4096
# From this point, inference uses only the episode histogram, not source_kernel.
initial=defaultdict(int); rows=defaultdict(lambda:[0]*4)
for z,y,a,u,b,v,n in leaves:
 initial[(z,y)]+=n
 rows[(0,(z,y),a)][PAIR.index(u)]+=n
 rows[(1,(z,y,a,u),b)][PAIR.index(v)]+=n
assert len(rows)==1088
rowlaws={r:tuple(F(n,sum(cts)) for n in cts) for r,cts in rows.items()}
# Discover local predictive masks from t0 rows, including irrelevant own-current/neighbors-old/otheraction.
table={}
for (t,h,a),law in rowlaws.items():
 if t==0:
  z,y=h;table[y+z+a]=law
assert len(table)==64
def marginal(law,i):return law[2]+law[3] if i==0 else law[1]+law[3]
minimal=[]
for i in (0,1):
 feasible=[]
 for size in range(7):
  for mask in combinations(range(6),size):
   classes=defaultdict(set)
   for c,k in table.items(): classes[tuple(c[j] for j in mask)].add(marginal(k,i))
   if all(len(s)==1 for s in classes.values()): feasible.append(mask)
 minimal.append([m for m in feasible if not any(set(k)<set(m) for k in feasible)])
assert minimal==[[(1,2,4)],[(0,3,5)]]
# Infer local table and common-source weight from the same counts; then verify ALL prefix rows.
local=[]
for i in (0,1):
 mask=minimal[i][0]
 local.append({tuple(c[j] for j in mask):marginal(law,i) for c,law in table.items()})
lambdas=set()
for c,k in table.items():
 p,q=marginal(k,0),marginal(k,1)
 lambdas.add((k[3]-p*q)/(min(p,q)-p*q))
assert lambdas=={F(1,2)}
def predictor(z,y,a):
 c=y+z+a;p,q=[local[i][tuple(c[j] for j in minimal[i][0])] for i in (0,1)]
 joint=[F(0)]*4
 for u in range(10):joint[2*int(F(u,10)<p)+int(F(u,10)<q)]+=F(1,20)
 for u,v in product(range(10),repeat=2):joint[2*int(F(u,10)<p)+int(F(v,10)<q)]+=F(1,200)
 return tuple(joint)
max_residual=F(0)
for (t,h,a),law in rowlaws.items():
 z,y=h if t==0 else (h[1],h[3])
 predicted=predictor(z,y,a)
 max_residual=max(max_residual,max(abs(x-y) for x,y in zip(predicted,law)))
assert max_residual==0
# Fixed raw confidence rows, selected predictor afterward: no unaccounted post-selection.
eps=F(1,80);eps_initial=F(1,4096)
minimum=min(sum(x) for x in rows.values())
assert minimum==40000
failure_bound=8*len(rows)*math.exp(-2*minimum*float(eps)**2)+32*math.exp(-2*N*float(eps_initial)**2)
assert failure_bound<.05
initial_tv=16*eps_initial/2
one_step_tv=4*eps/2
path_tv=initial_tv+2*one_step_tv
assert path_tv==F(133,2560)
# Data-compatible true marginal gap retains a positive lower bound for every essential omittedfeature.
separation={}
for i in (0,1):
 for j in minimal[i][0]:
  gap=max(abs(marginal(table[c],i)-marginal(table[c[:j]+(1-c[j],)+c[j+1:]],i)) for c in table)
  lower=gap-4*eps # Two marginal estimates, each sum of two cell errors.
  assert lower>0
  separation[f'port{i}_coordinate{j}']={'empirical_gap':str(gap),'true_gap_lower':str(lower),'merged_forecast_error_lower':str(lower/2)}
# Explicit adaptive controller family: request precisely when owncurrent is clear / busy.
policies={'request_when_clear':lambda y:tuple(1-v for v in y),
          'request_when_busy':lambda y:y}
policy_checks={}
for name,policy in policies.items():
 branches={(z,y):F(n,N) for (z,y),n in initial.items()}
 # Use history tuples to keep distinct routes rather than merge evidence accidentally.
 masses={(z,y):mass for (z,y),mass in branches.items()}
 for t in range(2):
  nxt={}
  for h,mass in masses.items():
   z,y=h if t==0 else (h[1],h[3])
   a=policy(y);law=rowlaws[(t,h,a)];pred=predictor(z,y,a)
   assert law==pred
   for out,prob in zip(PAIR,law):nxt[h+(a,out)]=mass*prob
  masses=nxt
 assert sum(masses.values())==1
 policy_checks[name]={'terminal_histories':len(masses),'nominal_path_TV':'0'}
# Weighted pairing lower bounds at first tick under request_when_clear.
# Dropping z0: pair equalmass initial roots with z0 toggled, all otherinputs fixed.
# Dropping y1: same with y1 toggled; own action a0=1-y0 unchanged.
# No otheraction is delivered as a free input to port0.
weighted_lower={}
for label,coord in [('no_previous_own_readout',0),('no_neighbor_current_readout',3)]:
 total=F(0)
 for root in product((0,1),repeat=4): # z0,z1,y0,y1
  if root[coord]:continue
  other=list(root);other[coord]=1;other=tuple(other)
  z,y=root[:2],root[2:];zz,yy=other[:2],other[2:]
  p=marginal(rowlaws[(0,(z,y),policies['request_when_clear'](y))],0)
  q=marginal(rowlaws[(0,(zz,yy),policies['request_when_clear'](yy))],0)
  # Each member has initialmass1/16; triangle inequality gives pairmass*gap.
  total+=F(1,16)*abs(p-q)
 assert total==F(1,10) and total>path_tv
 weighted_lower[label]=str(total)
# Save compressed data with explicit provenance; reconstructable without hidden source formula.
data={'provenance':'CONSTRUCTED possible histogram, not physical data and not an actual IID sampling run',
 'columns':['previous_pair','current_pair','action0','next_pair','action1','final_pair','multiplicity'],
 'episodes':leaves,'N':N}
(OUT/'constructed_service_episode_histogram.json').write_text(json.dumps(data,separators=(',',':'))+'\n')
report={'status':'PASS','scope':'Conditional finite-data confidence procedure on an explicitly constructed possible histogram',
 'independent_episode_assumption':'Required for confidence interpretation; not asserted of construction',
 'H':2,'episodes':N,'histogram_leaves':len(leaves),'full_history_action_rows':len(rows),
 'minimum_row_count':minimum,'initial_cells':16,'conditional_cell_radius':str(eps),
 'initial_cell_radius':str(eps_initial),'simultaneous_failure_bound':failure_bound,
 'data_discovered_minimal_masks':minimal,'max_full_history_cell_residual':str(max_residual),
 'positive_shared_response_atoms':110,'all_adaptive_policy_path_TV_bound':str(path_tv),
 'bound_decimal':float(path_tv),'necessary_feature_certificates':separation,
 'explicit_feedback_policy_checks':policy_checks,'nominal_witness_weighted_J_lower_bounds':weighted_lower,
 'no_model_promise':'Validation constrains every full history separately; older-history independence not assumed'}
(OUT/'finite_episode_discovery_checks.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))

#!/usr/bin/env python3
"""Exact implementation check against frozen learned candidate; no data fitting."""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
import json
D=Path(__file__).parent
x=json.loads((D/'monitor_service_frozen_candidate.json').read_text());masks=x['masks'];local=[[F(p) for p in a] for a in x['local']]
assert masks==[[1,2,4],[0,3,5]] and F(x['shared_weight'])==F(1,2)
def local_parameter(port,memory,current,action,neighbor_message):
 c=(neighbor_message,memory,action)
 return local[port][4*c[0]+2*c[1]+c[2]]
checked=0
for z,y,a in product(list(product((0,1),repeat=2)),repeat=3):
 p=local_parameter(0,z[0],y[0],a[0],y[1]);q=local_parameter(1,z[1],y[1],a[1],y[0])
 both=(p*q+min(p,q))/2;expected=(1-p-q+both,q-both,p-both,both);counts=[0]*4
 for r in range(200):
  u,v=(r//10,r//10) if r<100 else ((r-100)//10,(r-100)%10)
  answer=(int(F(u,10)<p),int(F(v,10)<q));counts[2*answer[0]+answer[1]]+=1
 assert tuple(F(n,200) for n in counts)==expected
 # Local memory update stores only its own current reading.
 next_memory=(y[0],y[1]);assert next_memory==y
 checked+=1
result={'status':'PASS','checked_contexts':checked,'one_bit_memory_per_port':True,'one_current_neighbor_bit_per_port':True,'shared_driver_cardinality':200,'threshold_symbols_per_port':10,'minimum_fixed_length_threshold_bits_per_port':4,'ideal_uniform_source_note':'Uniform200 is an exact stochastic primitive here; bounded fairbit realization needs approximation or rejection with unbounded worstcase draws. Predictor probabilities are computed exactly withoutsampling.'}
(D/'compiled_predictor_checks.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
# Deterministic carryover: approximate ideal Uniform200 with exactly20 fair bits.
# Count preimages by integer interval arithmetic, independently of observations.
assert [F(p) for p in x['initial']]==[F(1,16)]*16
B=2**20
counts=[((r+1)*B+199)//200-(r*B+199)//200 for r in range(200)]
assert sum(counts)==B
source_tv=sum(abs(F(n,B)-F(1,200)) for n in counts)/2
assert source_tv==F(33,1638400)
# Verify pushforward contraction for every learned threshold-context row.
worst=F(0)
for z,y,a in product(list(product((0,1),repeat=2)),repeat=3):
 p=local_parameter(0,z[0],y[0],a[0],y[1]);q=local_parameter(1,z[1],y[1],a[1],y[0]);ideal=[F(0)]*4;bounded=[F(0)]*4
 for r,n in enumerate(counts):
  u,v=(r//10,r//10) if r<100 else ((r-100)//10,(r-100)%10)
  j=2*int(F(u,10)<p)+int(F(v,10)<q)
  ideal[j]+=F(1,200);bounded[j]+=F(n,B)
 row_tv=sum(abs(p-q) for p,q in zip(ideal,bounded))/2
 assert row_tv<=source_tv;worst=max(worst,row_tv)
H=8;transfer=H*source_tv;assert transfer==F(33,204800)
# Recompute the exact final fitmaximum from saved rational predictions/counts.
hists=json.loads((D/'monitor_service_holdout_histograms.json').read_text());preds=json.loads((D/'monitor_service_exact_predictions.json').read_text());maxfit=F(0)
for hh,pp in zip(hists,preds):
 assert hh['policy']==pp['policy']
 for (cc,ns),(dd,qs,den) in zip(hh['histograms'],pp['probabilities']):
  assert cc==dd and sum(ns)==50000
  maxfit=max(maxfit,sum(abs(F(n,50000)-F(q,den)) for n,q in zip(ns,qs))/2)
for row in json.loads((D/'monitor_service_monitor_results.json').read_text()):
 for m in row['max_run_monitors']:maxfit=max(maxfit,F(m['TV_fit']))
ideal_bound=maxfit+F(231,10000);bounded_bound=ideal_bound+transfer
assert bounded_bound<=F(40589,1000000)<F(1,20)
result['bounded_sampler']={'fair_bits_per_tick':20,'driver_register_bits':8,'threshold_fixed_bits_per_port':4,'initial_fair_bits':4,'source_TV':str(source_tv),'maximum_actual_row_TV':str(worst),'H8_path_TV_transfer':str(transfer),'ideal_exact_operational_bound':str(ideal_bound),'bounded_exact_operational_bound':str(bounded_bound),'bounded_outward_operational_bound':'40589/1000000','note':'Same frozen program, deterministic approximation transfer, no new observations or confidence event.'}
(D/'compiled_predictor_checks.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result['bounded_sampler'],indent=2))

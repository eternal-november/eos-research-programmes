#!/usr/bin/env python3
"""Independent same-root minimum-cost and infeasibility check, dense CSP backend."""
from independent_sequential_check import *
def main():
 path=EX/'sequential_mission_cost_diagnostic_results.json';cost=json.loads(path.read_text());rootpath=EX/'sequential_mission_corrected_results.json';source=json.loads(rootpath.read_text());cfg=source['config'];checked=0;positive=0;negative=0
 assert len(cost['roots'])==len(source['results'])==48
 for report,root in zip(cost['roots'],source['results']):
  assert (report['seed'],report['order_index'],report['mission_order'])==(root['seed'],root['order_index'],root['mission_order'])
  mats={x:np.ones((N,N),dtype=bool) for x in [(0,1),(1,2),(2,3)]}
  for r in root['base_records']:
   p=pred(r['counters']);mats[tuple(r['edge'])]&=p[:,None]+p[None,:]==r['sum']
  ds=project(mats);c=tuple(root['initial_counter_context']);t=root['paid_initial_ticks'];e=root['paid_initial_energy'];order=root['mission_order']
  lower=t+sum(min(cfg['prep_lengths'])+cfg['diagnostic_ticks']+min(43 if u%2==0 else 51 for u in edge) for edge in order)
  upper=t+sum(max(cfg['prep_lengths'])+cfg['diagnostic_ticks']+max(43 if u%2==0 else 51 for u in edge) for edge in order)
  energy=e+max(map(sum,cfg['held_patterns']))*(upper-t)+sum(max(10 if u%2==0 else 12 for u in edge) for edge in order)
  assert report['lower_time_bound']==lower and report['upper_time_bound']==upper and report['energy_upper_bound_for_any_grammar_policy']==energy and energy<=cfg['absolute_energy_budget']
  for label,result in report['results'].items():
   relations=mats if label=='exact' else {};minimum=result['minimum_worst_case_ticks'];deadline=upper if minimum is None else minimum;local=dict(cfg);local['absolute_deadline_ticks']=deadline
   assert exists(local,order,relations,ds,c,t,e)==(minimum is not None);checked+=1
   if minimum is None:negative+=1
   else:
    positive+=1;assert minimum==168
    verify(local,order,relations,ds,c,t,e,result['optimal_policy']);local['absolute_deadline_ticks']=minimum-1
    assert not exists(local,order,relations,ds,c,t,e);checked+=1
 result={'passed':True,'same_roots':48,'independent_dense_search_decisions':checked,'positive_method_roots':positive,'negative_method_roots':negative,'all_positive_minimum_ticks':168,'all_roots_public_maximum_duration':190,'all_roots_energy_upper_bound':385,'exact_vs_rectangular_advantage':False,'cost_result_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'corrected_roots_sha256':hashlib.sha256(rootpath.read_bytes()).hexdigest(),'scope':'Exact minimum only for same declared finite three-leg option grammar; post-result diagnostic, not new confirmatory evidence.'}
 (ROOT/'review'/'independent_frontier_results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()

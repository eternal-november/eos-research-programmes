#!/usr/bin/env python3
"""Exploratory exact minimum worst-case time in the frozen finite option grammar."""
import hashlib,json,time
from pathlib import Path
from relational_engine import Catalogue,ForestKnowledge
from sequential_mission_compiler import Solver,verify_policy,duration,distance
ROOT=Path(__file__).resolve().parent

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def main():
 spec=json.loads((ROOT/'sequential_mission_cost_diagnostic_config.json').read_text())
 assert sha(ROOT/spec['roots_source'])==spec['roots_source_sha256']
 roots=json.loads((ROOT/spec['roots_source']).read_text());cfg=roots['config'];cat=Catalogue(cfg['n_ports'],cfg['L'])
 output=[];summary={'roots':0,'both_feasible':0,'both_impossible_in_grammar':0,'exact_only_feasible':0,
                    'exact_lower_cost':0,'equal_cost':0,'rectangle_lower_cost':0,'energy_nonbinding_at_public_upper_bound':True}
 start=time.perf_counter()
 for root in roots['results']:
  order=root['mission_order'];k=ForestKnowledge(cat,cfg['n_outputs'])
  for record in root['base_records']:assert k.observe_sum(*record['edge'],record['counters'],record['sum'])
  c=tuple(root['initial_counter_context']);ticks=root['paid_initial_ticks'];energy=root['paid_initial_energy']
  lower=ticks+sum(min(cfg['prep_lengths'])+cfg['diagnostic_ticks']+min(duration(u) for u in edge) for edge in order)
  upper=ticks+sum(max(cfg['prep_lengths'])+cfg['diagnostic_ticks']+max(duration(u) for u in edge) for edge in order)
  energy_ceiling=energy+max(map(sum,cfg['held_patterns']))*(upper-ticks)+sum(max(distance(u) for u in edge) for edge in order)
  nonbinding=energy_ceiling<=cfg['absolute_energy_budget'];summary['energy_nonbinding_at_public_upper_bound'] &= nonbinding
  pair={}
  for label in ['exact','rectangular']:
   knowledge=k.copy()
   if label=='rectangular':knowledge.edges={}
   calls=[];cache={}
   def check(deadline):
    if deadline in cache:return cache[deadline]
    localcfg=dict(cfg);localcfg['absolute_deadline_ticks']=deadline
    solver=Solver(localcfg,order);policy=solver.search(knowledge.copy(),c,0,ticks,energy)
    calls.append({'deadline':deadline,'feasible':policy is not None,'search_counts':solver.counts})
    cache[deadline]=(policy,localcfg)
    return cache[deadline]
   top,_=check(upper)
   if top is None:
    pair[label]={'feasible_in_grammar':False,'minimum_worst_case_ticks':None,'status':'no policy in finite3leggrammar even at its publicmaximumduration','queries':calls}
   else:
    lo,hi=lower,upper
    while lo<hi:
     mid=(lo+hi)//2
     policy,_=check(mid)
     if policy is None:lo=mid+1
     else:hi=mid
    policy,localcfg=check(lo);assert policy is not None
    if lo>lower:assert check(lo-1)[0] is None
    replay=verify_policy(localcfg,order,knowledge,c,0,ticks,energy,policy)
    assert replay['max_ticks']==lo
    pair[label]={'feasible_in_grammar':True,'minimum_worst_case_ticks':lo,
                 'certificate_replay':replay,'optimal_policy':policy,'queries':calls}
  a,b=pair['exact']['minimum_worst_case_ticks'],pair['rectangular']['minimum_worst_case_ticks']
  assert b is None or (a is not None and a<=b)
  summary['roots']+=1
  if a is None and b is None:summary['both_impossible_in_grammar']+=1
  elif a is not None and b is None:summary['exact_only_feasible']+=1
  else:
   summary['both_feasible']+=1;summary['exact_lower_cost']+=a<b;summary['equal_cost']+=a==b;summary['rectangle_lower_cost']+=b<a
  output.append({'seed':root['seed'],'order_index':root['order_index'],'mission_order':order,
                 'paid_initial_ticks':ticks,'lower_time_bound':lower,'upper_time_bound':upper,
                 'energy_upper_bound_for_any_grammar_policy':energy_ceiling,'energy_nonbinding':nonbinding,
                 'results':pair})
 result={'spec_sha256':sha(ROOT/'sequential_mission_cost_diagnostic_config.json'),'source_sha256':sha(__file__),
         'compiler_sha256':sha(ROOT/'sequential_mission_compiler.py'),'summary':summary,
         'elapsed_seconds':time.perf_counter()-start,'roots':output,
         'interpretation':'Post-result diagnosis on same fixed roots. Any improvement is exploratory; none may be substituted for frozen primary deadline counts. Minimum is exact only for the declared3leg option grammar and coherent all-branch criterion.'}
 (ROOT/'sequential_mission_cost_diagnostic_results.json').write_text(json.dumps(result,indent=2)+'\n')
 (ROOT/'sequential_mission_cost_diagnostic_summary.json').write_text(json.dumps({k:v for k,v in result.items() if k!='roots'},indent=2)+'\n')
 print(json.dumps(result['summary'],indent=2))
if __name__=='__main__':main()

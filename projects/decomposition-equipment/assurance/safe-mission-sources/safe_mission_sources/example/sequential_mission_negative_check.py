#!/usr/bin/env python3
"""All-low world: safe acquisition does not promise useful completion."""
import hashlib,json
from pathlib import Path
from relational_engine import Catalogue,ForestKnowledge
from partial_acquisition_probe import advance
from sequential_mission_compiler import Solver
ROOT=Path(__file__).resolve().parent

def main():
 cfg=json.loads((ROOT/'sequential_mission_corrected_config.json').read_text())
 acq=json.loads((ROOT/'partial_acquisition_config.json').read_text())
 cat=Catalogue(cfg['n_ports'],cfg['L']);k=ForestKnowledge(cat,cfg['n_outputs'])
 c=(cfg['L'],)*cfg['n_ports'];ticks=0;energy=0;trace=[]
 for _ in range(cfg['initial_flush_ticks']):c=advance(c,(0,)*cfg['n_ports'],cfg['L']);ticks+=1
 for t,cmd in enumerate(acq['initial_command_vectors']):
  c=advance(c,cmd,cfg['L']);ticks+=1;energy+=sum(cmd)
  edge=acq['edges'][t%len(acq['edges'])]
  assert k.observe_sum(*edge,c,0)
  trace.append({'tick':ticks,'counter_context':list(c),'command':cmd,'sum_edge':edge,'sum_value':0,
                'execution_mode':'stationary protected acquisition bay'})
 for _ in range(cfg['initial_transfer_ticks']):
  c=advance(c,cfg['initial_transfer_command'],cfg['L']);ticks+=1;energy+=sum(cfg['initial_transfer_command'])
 energy+=cfg['initial_transfer_energy']
 zero=cat.find([],0)
 assert k.feasible(domain_restrictions={i:1<<zero for i in range(cfg['n_outputs'])})
 outcomes=[]
 for order in cfg['mission_orders']:
  solver=Solver(cfg,order);policy=solver.search(k.copy(),c,0,ticks,energy)
  assert policy is None
  outcomes.append({'mission_order':order,'certified':False,'controller_status':'safe_stopped_abstention',
                   'post_acquisition_motion_commands':0,'completed_mission_legs':0,
                   'reason':'constant-zero persistent world remains possible and has no admissible fast passage',
                   'search_counts':solver.counts})
 report={'passed':True,'world':'all four mechanisms constantzero',
         'safe_acquisition_is_conditional_on_declared_bay_and_coarse_transfer_contracts':True,
         'initial_class_unconditional_completion_claim':False,
         'elapsed_acquisition_and_transfer_ticks':ticks,'energy':energy,'trace':trace,'outcomes':outcomes,
         'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
         'compiler_sha256':hashlib.sha256((ROOT/'sequential_mission_compiler.py').read_bytes()).hexdigest()}
 (ROOT/'sequential_mission_negative_results.json').write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps({k:v for k,v in report.items() if k!='trace'},indent=2))
if __name__=='__main__':main()

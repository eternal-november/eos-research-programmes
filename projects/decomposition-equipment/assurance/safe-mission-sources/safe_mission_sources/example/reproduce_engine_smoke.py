#!/usr/bin/env python3
"""Reproduce relational_engine_qa.json (wall-clock time naturally varies)."""
import hashlib,json,random,subprocess,sys,time
from pathlib import Path
from relational_engine import Catalogue,ForestKnowledge
ROOT=Path(__file__).resolve().parent

def main():
 run=subprocess.run([sys.executable,str(ROOT/'test_relational_engine.py')],cwd=ROOT,
                    text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (ROOT/'relational_engine_tests.log').write_text(run.stdout)
 if run.returncode:raise SystemExit(run.returncode)
 rng=random.Random(202610292057);c=Catalogue(24,3);k=ForestKnowledge(c,12)
 truth=[rng.randrange(c.size) for _ in range(12)];started=time.perf_counter()
 for e in range(11):
  for rep in range(8):
   x=tuple(rng.randrange(4) for _ in range(24))
   s=c.evaluate(truth[e],x)+c.evaluate(truth[e+1],x)
   assert k.observe_sum(e,e+1,x,s)
   assert all((k.domains[i]>>h)&1 for i,h in enumerate(truth))
 assert k.feasible(domain_restrictions={i:1<<h for i,h in enumerate(truth)})
 report={'unit_tests':8,'unit_tests_passed':True,'unit_test_seed':20261029,
         'growing_engine_smoke_seed':202610292057,
         'growing_engine_smoke_seconds':time.perf_counter()-started,
         'synthetic_contexts_not_a_physical_acquisition_claim':True,
         'planted_coherent_world_retained':True,'metrics':k.metrics(),
         'source_sha256':{p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest()
             for p in ['relational_engine.py','test_relational_engine.py']}}
 (ROOT/'relational_engine_qa.json').write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps({'passed':True,'catalogue_size':c.size,
                   'domain_sizes':report['metrics']['local_domain_sizes']},indent=2))
if __name__=='__main__':main()

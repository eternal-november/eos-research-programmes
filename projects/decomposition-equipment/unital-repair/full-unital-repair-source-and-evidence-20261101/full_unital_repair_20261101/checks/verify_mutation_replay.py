#!/usr/bin/env python3
"""Isolated mutation-detection replay; the accepted checker is never edited.
Semantic counterexamples and deliberately corrupted implementations are distinct:
this script tests the latter, requiring a named mathematical rejection in both
normal and optimized Python, after unmodified temporary-copy controls pass.
"""
import ast
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys
import tempfile

HERE=Path(__file__).resolve().parent
TARGET=HERE/'verify_explicit_old_records.py'

def require(value,message):
 if not value:raise RuntimeError(message)

def main():
 source=TARGET.read_text();original_hash=sha256(TARGET.read_bytes()).hexdigest()
 require(not any(isinstance(node,ast.Assert) for node in ast.walk(ast.parse(source))), 'acceptance guards must not vanish under -O')
 mutations=[
  {'name':'omit_vertex_free_U',
   'old':'tuple(r.is_identity() and all(v==unit for v in xs) for xs in C)',
   'new':'tuple(False for xs in C)',
   'expected_failure':'generated closure differs from proposed quotient',
   'mathematical_reason':'Without the vertex-free relation, generated observations fail to recover exact rank-one group labels.'},
  {'name':'uniform_group_cosets_at_rank_one',
   'old':'labels[x] if r.rank()==1 else tuple(v%2 for v in labels[x])',
   'new':'tuple(v%2 for v in labels[x])',
   'expected_failure':'unit decoder not exact',
   'mathematical_reason':'The literal unit and a nonidentity kernel element acquire the same rank-one state but different zero-tree feasibility.'},
  {'name':'omit_size_two_old_unary_identity',
   'old':'return self.ordered_inputs==(self.vertices,) and self.grade_arrow',
   'new':'return len(self.vertices)<2 and self.ordered_inputs==(self.vertices,) and self.grade_arrow',
   'expected_failure':'full old unit control',
   'mathematical_reason':'The whole-graph unary identity on vertices {0,1} must admit the zero tree just as singleton identities do.'},
  {'name':'exchange_empty_identity_and_nullary',
   'old':'return self.ordered_inputs==(self.vertices,) and self.grade_arrow',
   'new':'return (self.ordered_inputs==(self.vertices,) if self.vertices else not self.ordered_inputs) and self.grade_arrow',
   'expected_failure':'nullary is not zero tree',
   'mathematical_reason':'An empty nullary operation vertex is not the empty-color identity or the vertex-free tree.'},
 ]
 results=[];controls=[]
 with tempfile.TemporaryDirectory(prefix='full_unital_mutation_',dir='/tmp') as temp:
  temp=Path(temp)
  unmodified=temp/'unmodified.py';unmodified.write_text(source)
  expected=json.loads((HERE/'explicit_old_record_results.json').read_text())
  for optimized in (False,True):
   command=[sys.executable]+(['-O'] if optimized else [])+[str(unmodified)]
   run=subprocess.run(command,capture_output=True,text=True,timeout=120)
   require(run.returncode==0,'unmodified control failed: '+run.stderr)
   actual=json.loads((temp/'explicit_old_record_results.json').read_text())
   require(actual==expected,'unmodified replay differs from accepted complete JSON')
   controls.append({'optimized':optimized,'returncode':run.returncode,'complete_result_equals_accepted':True})
  for mutation in mutations:
   require(source.count(mutation['old'])==1,'mutation must target exactly one code site: '+mutation['name'])
   changed=source.replace(mutation['old'],mutation['new'])
   mutant=temp/(mutation['name']+'.py');mutant.write_text(changed)
   ast.parse(changed) # Reject accidental syntax corruption as a test mechanism.
   replays=[]
   for optimized in (False,True):
    command=[sys.executable]+(['-O'] if optimized else [])+[str(mutant)]
    run=subprocess.run(command,capture_output=True,text=True,timeout=120)
    expected_line='Failure: '+mutation['expected_failure']
    require(run.returncode!=0,'mutation was not rejected: '+mutation['name'])
    require(expected_line in run.stderr,'not the expected mathematical rejection: '+mutation['name']+'\n'+run.stderr)
    require(not any(marker in run.stderr for marker in ('FileNotFoundError','ModuleNotFoundError','ImportError','SyntaxError','PermissionError')), 'infrastructure error masquerading as rejection')
    replays.append({'optimized':optimized,'returncode':run.returncode,
                    'expected_mathematical_failure':expected_line,
                    'stderr':run.stderr.replace(str(temp),'<temporary>'),
                    'stdout':run.stdout})
   results.append({'name':mutation['name'],'mutated_code_sha256':sha256(changed.encode()).hexdigest(),
                   'replacement_count':1,'mathematical_reason':mutation['mathematical_reason'],'replays':replays})
 require(sha256(TARGET.read_bytes()).hexdigest()==original_hash,'accepted checker was changed')
 receipt={'status':'All four implementation mutations rejected mathematically in normal and optimized Python',
          'scope':'Narrow temporary-copy mutations only; semantic negative controls remain separately reported',
          'target_checker':str(TARGET),'target_checker_sha256':original_hash,
          'accepted_result_sha256':sha256((HERE/'explicit_old_record_results.json').read_bytes()).hexdigest(),
          'unmodified_controls':controls,'mutations':results,'original_preserved':True,
          'harness_sha256':sha256(Path(__file__).read_bytes()).hexdigest()}
 out=HERE/'mutation_replay_results.json';out.write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
 print(json.dumps({'status':receipt['status'],'unmodified_controls':len(controls),'mutated_rejections':sum(len(m['replays']) for m in results),'receipt':str(out)},indent=2))
if __name__=='__main__':main()

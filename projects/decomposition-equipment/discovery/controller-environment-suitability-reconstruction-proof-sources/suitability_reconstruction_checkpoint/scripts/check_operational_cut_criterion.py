#!/usr/bin/env python3
"""Finite checks for the derived causal update and robust decoder criteria.
These do not replace the general proofs in Operational_Cut_Capability.md.
"""
import itertools,json,hashlib,pathlib
ROOT=pathlib.Path(__file__).resolve().parents[1]
vals=list(itertools.product(range(2),repeat=4))
tables=list(itertools.product(range(2),repeat=4))
cases=0
for old in vals:
 for obs in vals:
  for new in vals:
   kernel=all((old[i],obs[i])!=(old[j],obs[j]) or new[i]==new[j] for i in range(4) for j in range(4))
   physical=any(all(u[2*old[i]+obs[i]]==new[i] for i in range(4)) for u in tables)
   assert kernel==physical
   cases+=1
# Each physical occurrence is individually realizable, but one shared table is not.
occ1=[((0,0),0)]
occ2=[((0,0),1)]
def functional(rows):
 return all(x!=y or a==b for x,a in rows for y,b in rows)
assert functional(occ1) and functional(occ2) and not functional(occ1+occ2)
# Pairwise acceptable-response compatibility does not imply one robust response.
demands=[{0,1},{1,2},{0,2}]
assert all(a&b for a,b in itertools.combinations(demands,2))
assert not set.intersection(*demands)
# A finite recurrent state can carry multiple memory values after different histories.
# State s is restored after either observed reply; the driver remembers that reply.
reachable={("s",0),("s",1)}
assert len({m for s,m in reachable if s=="s"})==2
out={"status":"PASS","kernel_vs_physical_table_cases":cases,
 "shared_table_negative_control":"PASS","nonpairwise_task_response_control":"PASS",
 "state_memory_relation_control":"PASS",
 "source_sha256":hashlib.sha256((ROOT/'theory/Operational_Cut_Capability.md').read_bytes()).hexdigest()}
path=ROOT/'review/Operational_Cut_Criterion_Results.json'
path.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))

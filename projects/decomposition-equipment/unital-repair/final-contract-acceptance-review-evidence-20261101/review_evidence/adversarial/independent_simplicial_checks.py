from itertools import product, combinations_with_replacement
from pathlib import Path
import hashlib,json
if not __debug__:raise RuntimeError('Optimized execution not accepted')
C=((0,1,2),(3,4),(5,)); count=0; total=0

def op(x,a):
 rows,vertices=x
 changed=tuple(tuple(sum(row[a[i]:a[i+1]]) for i in range(len(a)-1)) for row in rows)
 changed=tuple(row for row in changed if sum(row))
 return changed,tuple(vertices[i] for i in a)
for n in range(4):
 if n==0: matrices={()}
 else:
  matrices={tuple(tuple(sum(labels[v]==i for v in c) for i in range(n)) for c in C) for labels in product(range(n),repeat=6)}
 for rows in matrices:
  x=(rows,tuple(min(i,2) for i in range(n+1)))
  for m in range(4):
   for a in combinations_with_replacement(range(n+1),m+1):
    y=op(x,a)
    for l in range(3):
     for b in combinations_with_replacement(range(m+1),l+1):
      direct=tuple(a[j] for j in b)
      assert op(y,b)==op(x,direct),(x,a,b)
      count+=1
  total+=1
r={'status':'PASS','graph_cliques':[3,2,1],'source_degrees':[0,3],'intermediate_degrees':[0,3],'target_degrees':[0,2],'source_records':total,'all_monotone_composition_checks':count,'typing':'Actual retained chain interfaces 0,1,2 and all selected repeated-vertex identities; transformations retain chosen endpoint objects.','trust':'Independent finite formula check; all-degree proof remains separate.','script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
Path(__file__).with_name('independent_simplicial_results.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))

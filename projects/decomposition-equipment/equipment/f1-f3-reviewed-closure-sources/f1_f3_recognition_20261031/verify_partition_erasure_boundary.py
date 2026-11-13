"""Independent finite coefficient-free F1 fibre check; no symbolic theorem claim."""
if not __debug__:
    raise RuntimeError("Verification requires assertions enabled; do not run with python -O")

import itertools,json
from pathlib import Path

def graph(n,mask):
    pairs=list(itertools.combinations(range(n),2))
    return frozenset(e for i,e in enumerate(pairs) if mask>>i&1)
def induced(G,U):
    U=sorted(U)
    return (len(U),tuple((i,j) for i,j in itertools.combinations(range(len(U)),2) if (U[i],U[j]) in G))
rows=[];checked=0;max_fibre=0;bad_examples=[]
for r in range(5):
 for mask in range(1<<(r*(r-1)//2)):
  G=graph(r,mask); hom=not G or len(G)==r*(r-1)//2
  graph_pass=True
  for n in range(3,5):
   for i in range(n):
    for j in range(i+2,n+1):
     if j-i==n: continue
     fibres={}
     for assignment in itertools.product(range(n),repeat=r):
      blocks=[{v for v in range(r) if assignment[v]==k} for k in range(n)]
      profile=tuple(induced(G,U) for U in blocks)
      middle=induced(G,set().union(*blocks[i:j]))
      fibres.setdefault(profile,set()).add(middle)
     for p,values in fibres.items():
      checked+=1; max_fibre=max(max_fibre,len(values))
      if len(values)!=1:
       graph_pass=False
       if len(bad_examples)<4:bad_examples.append({'r':r,'mask':mask,'n':n,'interval':[i,j],'profile':p,'intermediates':sorted(values)})
  assert graph_pass==hom,(r,mask,graph_pass,hom)
  rows.append({'vertices':r,'mask':mask,'homogeneous':hom,'all_tested_fibres_singleton':graph_pass})
result={'status':'PASS','domain':'all ordered simple graphs through four vertices; all 3- and 4-slot partitions including empty blocks; every proper interval length>=2','graph_count':len(rows),'quotient_interval_fibres_checked':checked,'maximum_distinct_intermediate_graphs':max_fibre,'rows':rows,'failure_controls':bad_examples}
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2))
print(json.dumps({k:v for k,v in result.items() if k not in ['rows','failure_controls']},indent=2))

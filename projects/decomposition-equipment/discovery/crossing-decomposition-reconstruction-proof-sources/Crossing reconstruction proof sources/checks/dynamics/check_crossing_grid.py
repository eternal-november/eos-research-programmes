from itertools import product
from pathlib import Path
import json

def compose(R,S):return {(a,c) for a,b in R for b2,c in S if b==b2}
R={(0,0),(1,1),(1,2)}
T={(0,2),(1,1),(2,0)}
qB={0:0,1:0,2:1};qC={0:0,1:0,2:1}
RY={(a,qB[b]) for a,b in R}
P={(a,qC[c]) for a,c in compose(R,T)}
assert P=={(0,1),(1,0)}
solutions=[]
for bits in product((0,1),repeat=4):
    U={pair for pair,keep in zip(product(range(2),repeat=2),bits) if keep}
    if compose(RY,U)==P:solutions.append(U)
assert not solutions
s={0:0,1:1,2:1}
W={((a,k),s[c]^(1-k)) for a,c in compose(R,T) for k in range(2)}
V={((qC[c],k),s[c]^(1-k)) for c in range(3) for k in range(2)}
row={((a,k),d) for a,z in P for (z2,k),d in V if z==z2}
N={((qB[b],l),s[c]^l) for b,c in T for l in range(2)}
col={((a,k),d) for a,y in RY for (y2,l),d in N for k in range(2) if y==y2 and l==1-k}
assert row==col==W
Ustar={(0,1),(1,0)}
SZ={((qC[c],l),s[c]^l) for c in range(3) for l in range(2)}
whole={((a,k),d) for a,z in compose(RY,Ustar) for (z2,l),d in SZ for k in range(2) if z==z2 and l==1-k}
assert whole==W
assert compose(RY,Ustar)!=P
result={'all_candidate_upper_right_relations_checked':16,'conservative_grid_solutions':0,'row_parent_exact':True,'column_parent_exact':True,'extensional_coarse_grid_exists':True,'scope':'Fixed four-component memoryless typed grid, no extra communication or restored concrete boundaries.'}
Path(__file__).with_name('check_crossing_grid_results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))

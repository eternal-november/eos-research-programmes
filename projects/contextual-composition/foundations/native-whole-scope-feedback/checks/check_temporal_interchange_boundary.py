from fractions import Fraction as Q
from itertools import product
import json
raw=list(product([0,1],repeat=4)) # x1,x2,y1,y2
q={z:Q(int(z[2]==z[1] and z[3]==z[0]),4) for z in raw}
assert sum(q.values())==1 and len(q)==16
for i in [0,1]:
 for x,y in product([0,1],repeat=2):
  assert sum(m for z,m in q.items() if z[i]==x and z[i+2]==y)==Q(1,4)
for xs in product([0,1],repeat=2):
 mass=sum(m for z,m in q.items() if z[:2]==xs)
 for i in [0,1]:
  assert [sum(m for z,m in q.items() if z[:2]==xs and z[i+2]==y)/mass for y in [0,1]] != [Q(1,2),Q(1,2)]
assert (2+2-1)**2==9 and 2*2+2*2-1==7
print(json.dumps({'fixed_local_row_types':True,'raw_atoms':16,'zero_atoms':12,'all_local_trajectories_independent_fair':True,'global_past_conditional_fairness_fails':True,'AugVect_dimensions':[9,7],'scope':'Scalar and dimension boundary diagnostic; not proof of shared-world typed interchange.'},indent=2))

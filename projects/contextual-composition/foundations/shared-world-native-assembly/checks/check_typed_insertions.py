from itertools import combinations
import json

def insert(old,m,positions,tag):
    placed=dict(zip(positions,old))
    return tuple(placed.get(k,(tag,k)) for k in range(m))
checks=0
for n in range(4):
  old=tuple(('old',k) for k in range(n))
  for m in range(n,5):
    for j in combinations(range(m),n):
      first=insert(old,m,j,'a')
      assert tuple(first[p] for p in j)==old
      for r in range(m,6):
        for k in combinations(range(r),m):
          second=insert(first,r,k,'b')
          composite=tuple(k[p] for p in j)
          assert tuple(second[p] for p in composite)==old
          assert len(second)==r and len(set(second))==r
          expected={k[p]:first[p] for p in range(m)}
          expected.update({p:('b',p) for p in range(r) if p not in k})
          assert second==tuple(expected[p] for p in range(r))
          checks+=1
b=insert((),1,(),'first')
a_b_c=insert(b,3,(1,),'second')
a_d_b_c=insert(a_b_c,4,(0,2,3),'third')
result={'status':'PASS','two_step_injection_cases':checks,'nonappend_final':a_d_b_c,'old_birth_final_rank_1based':a_d_b_c.index(('first',0))+1,'scope':'finite combinatorial diagnostic, not coefficient or native proof'}
print(json.dumps(result,indent=2))

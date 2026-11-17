from fractions import Fraction as F
from itertools import product
import json
X=range(3); D=range(4) # retry,return,Spin,zero
p=[F(1,2),F(1,4),F(1,4),F(0)]
def law(d,other):
    return F(int(d==0)) if other==0 else (F(1,2) if d in [1,2] else F(0))
q={(*x,*d):(F(1,4)*law(d[0],x[1])*law(d[1],x[0]) if all(v<2 for v in x) else F(0)) for x in product(X,repeat=2) for d in product(D,repeat=2)}
assert sum(q.values())==1
for x in product(X,repeat=2):
    assert sum(q[(*x,*d)] for d in product(D,repeat=2))==(F(1,4) if all(v<2 for v in x) else 0)
for i in range(2):
    for own in range(2):
        vec=[sum(m for key,m in q.items() if key[i]==own and key[2+i]==d) for d in D]
        assert vec==[F(1,2)*a for a in p]
source00=[sum(m for key,m in q.items() if key[0]==key[1]==0 and key[2]==d) for d in D]
assert source00==[F(1,4),F(0),F(0),F(0)]
assert source00!=[F(1,4)*a for a in p]
print(json.dumps({'all_raw_tuples':len(q),'positive_tuples':sum(m>0 for m in q.values()),'zero_tuples':sum(m==0 for m in q.values()),'incoming_reserve_exact':True,'both_own_binder_tests_exact':True,'full_binder_test_failure':[str(a) for a in source00]},indent=2))

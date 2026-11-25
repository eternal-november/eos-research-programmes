"""Independent exact action-intersection check, without the covering reduction."""
from itertools import combinations
from functools import lru_cache

M=6
B=[set(b) for b in combinations(range(M),2)]
Y=[set(y) for y in combinations(range(M),4)]
F=(1<<len(B))-1

def action_intersection(H, request, added):
    R=set(request)-set(added)
    for b in H:
        if not (b & set(added)): R-=b
    return R

nominal=[]
for mask in range(1,1+F):
    hs=[b for i,b in enumerate(B) if mask>>i&1]
    if all(action_intersection(hs,y,()) for y in Y):nominal.append(mask)
maximal=[a for a in nominal if not any(a!=b and a&b==a for b in nominal)]
@lru_cache(None)
def search(rem):
    if not rem:return 0
    first=rem&-rem
    return 1+min(search(rem&~a) for a in maximal if first&a)
assert search(F)==6==len(B)-9
w=0
for b,c in combinations(B,2):
    assert any(not action_intersection([b,c],y,[e])
               for e in set(range(M))-(b|c) for y in Y)
    w+=1
for b in B:
    assert all(action_intersection([b],y,[e]) for e in set(range(M))-b for y in Y)
print('valid nominal summary classes',len(nominal),'maximal',len(maximal),'exact codes',search(F))
print('pairs incompatible under some same visible reentry',w,'exact codes',len(B))

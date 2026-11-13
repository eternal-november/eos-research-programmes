"""Exhaustive three-dimensional GF(2) obstruction/transport checks."""
from itertools import product, combinations
import json

def span(rows):
    s={0}
    for row in rows:
        s |= {x^row for x in tuple(s)}
    return frozenset(s)

def dim(S):
    return len(S).bit_length()-1

def add(A,B):return span(A|B)
def image(S,E):
    def one(x):
        ans=0
        for i,e in enumerate(E):
            if x>>i&1:ans^=e
        return ans
    return frozenset(one(x) for x in S)

subs=set()
for mask in range(1<<7):
    subs.add(span(i+1 for i in range(7) if mask>>i&1))
assert len(subs)==16
repairs=0; transports=0; faithful=0
for B in subs:
    for A in subs:
        M=add(B,A); d=dim(M)-dim(B)
        # Arbitrary scalar linear repairs; enumerate all choices up to d.
        found=None
        for k in range(4):
            if any(A<=add(B,span(J)) for J in combinations(range(1,8),k)):
                found=k;break
        assert found==d
        repairs+=1
        for E in product(range(8),repeat=3):
            Bp=image(B,E); Ap=image(A,E)
            dp=dim(add(Bp,Ap))-dim(Bp)
            assert dp<=d
            if dim(span(E))==3:
                assert dp==d; faithful+=1
            transports+=1
# Raw catalog repair cost can exceed obstruction dimension.
B=span([]); A=span([7]); raw=(1,2,4)
assert dim(add(B,A))-dim(B)==1
assert not any(A<=span(J) for k in range(3) for J in combinations(raw,k))
assert A<=span(raw)
print(json.dumps({'status':'PASS','field':'GF(2)','dimension':3,'subspaces':len(subs),'minimum_unrestricted_repair_cases':repairs,'adapter_cases':transports,'injective_covector_adapter_cases':faithful,'raw_vs_semantic_gap':{'obstruction_dimension':1,'minimum_raw_sensors':3}},indent=2))

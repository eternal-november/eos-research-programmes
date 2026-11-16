from itertools import product,combinations
from fractions import Fraction as F
from pathlib import Path
import re

def lam(bits):
    r=len(bits); v=[0]*(r+1)
    if sum(bits)==0:v[0]=1
    elif sum(bits)==1:v[bits.index(1)+1]=1
    return tuple(v)
def factor_action(bits,maps):
    # maps_i=[[1,0],[a_i,b_i]], augmented with first-coordinate epsilon.
    out={}
    for target in product((0,1),repeat=len(bits)):
        c=1
        for src,dst,(a,b) in zip(bits,target,maps):
            c*=((1 if dst==0 else a) if src==0 else (0 if dst==0 else b))
        if c:out[target]=c
    return out
cases=0
for r in range(1,5):
    choices=[(-1,0),(0,1),(2,-1)]
    for maps in product(choices,repeat=r):
        for bits in product((0,1),repeat=r):
            lhs=[0]*(r+1)
            for out,c in factor_action(bits,maps).items():
                lhs=[x+c*y for x,y in zip(lhs,lam(out))]
            v=lam(bits);rhs=[v[0]]+[a*v[0]+b*v[i+1] for i,(a,b) in enumerate(maps)]
            assert lhs==rhs
            cases+=1
print(f'PASS {cases} exact augmented-map naturality basis cases')
cases=0
for r in range(7):
    for bits in product((0,1),repeat=r):
        for mask in product((0,1),repeat=r):
            keep=[i for i in range(r) if mask[i]]
            tensor_deleted=any(bits[i] for i in range(r) if not mask[i])
            lhs=(0,)*(len(keep)+1) if tensor_deleted else lam(tuple(bits[i] for i in keep))
            v=lam(bits);rhs=(v[0],)+tuple(v[i+1] for i in keep)
            assert lhs==rhs
            cases+=1
        for split in range(r+1):
            # Two-block comparison then block lambdas; each output node
            # augments every factor outside its block, then within its block.
            block1=lam(bits[:split]) if not any(bits[split:]) else (0,)*(split+1)
            block2=lam(bits[split:]) if not any(bits[:split]) else (0,)*(r-split+1)
            assert block1[0]==block2[0]
            assert (block1[0],)+block1[1:]+block2[1:]==lam(bits)
print(f'PASS {cases} deletion squares, and all two-block assembly splits through six factors')
for r in range(1,9):
    images={lam(bits) for bits in product((0,1),repeat=r)}
    assert sum(v!=(0,)*(r+1) for v in images)==r+1
    assert sum(lam(bits)==(0,)*(r+1) for bits in product((0,1),repeat=r))==2**r-r-1
print('PASS tensor-to-product rank/kernel formula through eight factors')
q={(0,0):F(1,2),(0,1):F(0),(1,0):F(0),(1,1):F(1,2)}
assert sum(q.values())==1
for i in (0,1):
    for b in (0,1):assert sum(v for t,v in q.items() if t[i]==b)==F(1,2)
# Auxiliary augmented maps differ on e1 but have same product comparison.
f_e1={}; g_e1={(1,1):1}
assert f_e1!=g_e1 and lam((1,1))==(0,0,0)
assert lam((0,0))==(1,0,0)
print('PASS genuinely shared fair-bit native-kernel witness, retaining zero raw tuples')
s=Path(__file__).with_name('Tensor_Causal_Execution_and_Native_Comparison.tex').read_text();stack=[]
for op,name in re.findall(r'\\(begin|end)\{([^}]+)\}',s):
    if op=='begin':stack.append(name)
    else:assert stack.pop()==name
assert not stack
print('PASS TeX environment nesting; no compilation/formal verification claimed')

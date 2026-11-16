from fractions import Fraction as F
from itertools import product
from pathlib import Path
import re

def profiles():
    out={(F(1),)}
    for den in range(2,5):
        for x in range(den+1): out.add((F(x,den),F(den-x,den)))
    return sorted(out,key=str)

def dirac(p): return sum(x==1 for x in p)==1 and all(x in (0,1) for x in p)
def bounds(ps):
    k=len(ps); rows=list(product(*ps))
    return (sum(max(F(0),sum(xs)-k+1) for xs in rows),sum(min(xs) for xs in rows))
count=0
for k in (2,3):
    for ps in product(profiles(),repeat=k):
        lo,hi=bounds(ps)
        assert lo<=1<=hi
        assert (lo==hi==1)==(sum(not dirac(p) for p in ps)<=1)
        count+=1
print('PASS',count,'exact coincidence-profile robustness cases')

# Each variant retains one or two closed raw atoms per row; an off-loop
# atom of mass 1-p completes normalization. Zero ghosts can be appended
# without changing these exact effect diagnostics.
variants=[(p,split) for p in profiles() for split in (1,2)]
count=0
for k in (2,3):
    for components in product(variants,repeat=k):
        ps=[x[0] for x in components]
        robust=True
        for i,(p,n) in enumerate(components):
            for q in p:
                for atom in ([q/n]*n):
                    if not atom: continue
                    other=[ps[j] for j in range(k) if j!=i]
                    lo=sum(max(F(0),atom+sum(xs)-k+1) for xs in product(*other))
                    hi=sum(min((atom,)+xs) for xs in product(*other))
                    robust &= lo==hi==atom
        nd=[i for i,p in enumerate(ps) if not dirac(p)]
        criterion=not nd or (len(nd)==1 and all(components[i][1]==1 for i in range(k) if i!=nd[0]))
        assert robust==criterion, (components,robust,criterion)
        count+=1
print('PASS',count,'exact raw-marginal robustness cases')

f={(0,0):(0,0),(0,1):(1,1),(1,0):(0,1),(1,1):(0,0)}
assert sum(x==y for x,y in f.items())==1
assert [sum(f[u,v][1]==v for v in (0,1)) for u in (0,1)]==[2,0]
assert [sum(f[u,v][0]==u for u in (0,1)) for v in (0,1)]==[1,0]
closed=[(u,0,F(1,2)) for u in (0,1)]
assert sum(x[2] for x in closed)==1
assert sum(x[2] for x in closed if x[1]==0)==1
print('PASS joint-only elimination and normalized-but-distorted closed marginal examples')

s=Path(__file__).with_name('Partial_Trace_Domains_and_Shared_Coupling.tex').read_text()
stack=[]
for m in re.finditer(r'\\(begin|end)\{([^}]+)\}',s):
    if m[1]=='begin': stack.append(m[2])
    else: assert stack and stack.pop()==m[2]
assert not stack
print('PASS TeX environment nesting; no compilation/formal proof claimed')

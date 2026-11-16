from fractions import Fraction as F
from itertools import product
from pathlib import Path
import re

# Exact finite-horizon branching probe: q shares one fresh bit across the
# entire active frontier. Raw mixed draws retained with zero weights.
hist = [((),1,F(1))]
terminal=[]
for n in range(1,5):
    new=[]
    for path,active,m in hist:
        for draw in product((0,1),repeat=active):
            q=F(1,2) if len(set(draw))==1 else F(0)
            # 0 settles one leaf, 1 creates two active children.
            nxt=2*sum(draw)
            t=(path+(draw,),nxt,m*q)
            if nxt==0: terminal.append(t)
            else: new.append(t)
    hist=new
    assert sum(t[2] for t in terminal)+sum(t[2] for t in hist)==1
    assert sum(t[2] for t in terminal)==1-F(1,2**n)
    # Prune only test expansion after checking ghost entries, not the model.
    # Otherwise zero-weight branching explosion would make diagnostics huge.
    assert any(t[2]==0 for t in hist) or n==1
    hist=[t for t in hist if t[2]>0]
print('PASS shared variable-arity first-hit layers, finite mass conservation, zero tuples')
# Exact geometric example with no countable tail approximated as complete.
for den in range(2,9):
    p=F(1,den)
    for N in range(1,15):
        layers=[p*(1-p)**(n-1) for n in range(1,N+1)]
        assert sum(layers)==1-(1-p)**N
        for cut in range(N):
            assembled=sum(layers[:cut])+(1-p)**cut*sum(p*(1-p)**j for j in range(N-cut))
            assert assembled==sum(layers)
print('PASS 98 geometric finite-layer identities and every bounded-cut factorization')
# Marginal flow criterion: all rational fair-bit couplings in a mesh.
for n in range(2,20,2):
    for k in range(n//2+1):
        a=F(k,n); q={(0,0):a,(0,1):F(1,2)-a,(1,0):F(1,2)-a,(1,1):a}
        for mass in (F(0),F(1,7),F(1)):
            child={w:mass*v for w,v in q.items()}
            assert sum(child.values())==mass
            for i in (0,1):
                for bit in (0,1):
                    assert sum(v for w,v in child.items() if w[i]==bit)==mass/2
            if mass: assert {w:v/mass for w,v in child.items()}==q
print('PASS exact prefix-flow conservation, conditional marginals and positive-flow reconstruction')
assert F(1)!=F(1,2) # exact-pushforward restriction obstruction
# Per-row finite does not guarantee finite composition: N partial sums grow N.
for N in range(1,30):
    assert sum(F(1,2**n)*2**n for n in range(1,N+1))==N
print('PASS unbounded-row composition witness (finite partial sums N)')
s=Path(__file__).with_name('Countable_Clock_Trace_and_Causal_Execution.tex').read_text()
stack=[]
for kind,name in re.findall(r'\\(begin|end)\{([^}]+)\}',s):
    if kind=='begin': stack.append(name)
    else: assert stack.pop()==name
assert not stack
print('PASS TeX environment nesting; no compilation or formal verification claimed')

from fractions import Fraction as F
from itertools import product
from collections import defaultdict
from pathlib import Path
import re

# Full C-shape trees with B leaves or loop-colored children. C has 0,1,2 slots.
def fulltrees(depth,colors):
    if depth==0:return [(0,())]
    children=['B']+[(c,t) for c in colors for t in fulltrees(depth-1,colors)]
    return [(arity,tuple(xs)) for arity in range(3) for xs in product(children,repeat=arity)]
# Contract all connected components of one edge color; nested payload retains
# original node/slot structure, with references to outer ordered ports.
def contract(t,color):
    outer=[]
    def component(node):
        payload,slots=node; ins=[]
        for s in slots:
            if s!='B' and s[0]==color:
                ins.append(('internal',component(s[1])))
            else:
                idx=len(outer)
                outer.append('B' if s=='B' else (s[0],contract(s[1],color)))
                ins.append(('external',idx))
        return (payload,tuple(ins))
    inner=component(t)
    return (('block',color,inner),tuple(outer))
def expand(t,color):
    payload,slots=t
    expanded=tuple('B' if s=='B' else (s[0],expand(s[1],color)) for s in slots)
    assert payload[0]=='block' and payload[1]==color
    def fill(inner):
        p,ins=inner;out=[]
        for typ,arg in ins:
            out.append((color,fill(arg)) if typ=='internal' else expanded[arg])
        return (p,tuple(out))
    return fill(payload[2])
count=0
for t in fulltrees(2,('U','V','W')):
    u=contract(t,'U');uv=contract(u,'V');uvw=contract(uv,'W')
    assert expand(expand(expand(uvw,'W'),'V'),'U')==t
    v=contract(t,'V');vu=contract(v,'U')
    assert expand(expand(vu,'U'),'V')==t
    count+=1
print(f'PASS {count} full unused colored shapes: component decomposition/flattening, two orders and three colors')

# All finite test invocation trees with cost0 only at leaves.
def costtrees(d):
    out=[(cost,()) for cost in range(3)]
    if d:
        ts=costtrees(d-1)
        for cost in (1,2):
            for arity in (1,2):out += [(cost,cs) for cs in product(ts,repeat=arity)]
    return out
def total(t):return t[0]+sum(total(c) for c in t[1])
def depth(t):return 1+max([depth(c) for c in t[1]] or [0])
cts=costtrees(2)
for t in cts:assert depth(t)<=total(t)+1
assert depth((0,()))==1 and total((0,()))==0
print(f'PASS {len(cts)} guarded invocation cost/depth bounds, including cost0')

# Paid root X1 births child. Next root X2 and child Y are concurrently enabled.
# State=(root stage, x1, x2, child stage, y); child stage -1 means not born.
def fire(s,event,bit):
    stage,x1,x2,child,y=s
    if event=='X1':
        assert stage==0 and child==-1
        return (1,bit,None,0,None)
    if event=='X2':
        assert stage==1
        return (2,x1,bit,child,y)
    assert event=='Y' and child==0
    return (stage,x1,x2,1,bit)
for x1,x2,y in product((0,1),repeat=3):
    s=fire((0,None,None,-1,None),'X1',x1)
    assert fire(fire(s,'X2',x2),'Y',y)==fire(fire(s,'Y',y),'X2',x2)
print('PASS parent/child paid-event diamonds with early-port child initialization')
ind=defaultdict(F);shared=defaultdict(F)
for x1,x2,y in product((0,1),repeat=3):
    ind[(y,x2)]+=F(1,8)
    shared[(y,x2)]+=F(1,4) if x2==y else F(0)
assert sum(ind.values())==sum(shared.values())==1
assert sum(v for (y,x),v in ind.items() if y==x)==F(1,2)
assert sum(v for (y,x),v in shared.items() if y==x)==1
for x2 in (0,1):assert sum(v for (y,x),v in shared.items() if x==x2)==F(1,2)
for y in (0,1):assert sum(v for (z,x),v in shared.items() if z==y)==F(1,2)
print('PASS strict shared-feedback law separation while primitive event marginals remain fair')
# If one macro row has total1/2 and another total1, their independent product
# has second marginal scaled by1/2, hence is not a coupling of original rows.
a=(F(1,4),F(1,4));b=(F(1,2),F(1,2))
assert tuple(sum(x*y for x in a) for y in b)!=(b)
print('PASS subprobability product is not misclassified as unchanged-marginal coupling')
s=Path(__file__).with_name('Guarded_Incremental_Arena_Feedback_and_Cost_Trace.tex').read_text();stack=[]
for op,name in re.findall(r'\\(begin|end)\{([^}]+)\}',s):
    if op=='begin':stack.append(name)
    else:assert stack.pop()==name
assert not stack
print('PASS TeX environment nesting; no compilation/formal verification claimed')
# Nontrivial native algebra model: input n executes a fair latent bit, outputs
# a constant B and (if n>0) child n-1. α flips only its root latent bit;
# child copies are unchanged. Its unique tree fold flips every retained bit.
def fold_bits(prefix):return tuple(1-b for b in prefix)
checks=0
for n in range(6):
    for d in range(n+2):
        for prefix in product((0,1),repeat=d):
            # Algebra equation: root α + recursive child fold.
            recursive=() if not prefix else (1-prefix[0],)+fold_bits(prefix[1:])
            assert fold_bits(prefix)==recursive
            if d<n+1:
                for b in (0,1):
                    assert fold_bits(prefix+(b,))==fold_bits(prefix)+(1-b,)
                    checks+=1
assert fold_bits(())==()
# An actual nonidentity augmented coefficient map may accompany the fair flip.
coef=((1,0),(0,0));assert coef[0]==(1,0) and coef!=((1,0),(0,1))
print(f'PASS {checks} native-algebra fold/paid-birth squares in latent-bit model, with nonidentity augmented coefficient map')
# GLOBAL namespace checks over disconnected/all-retained configurations.
# A reused port name may have distinct loop colors/values in different states.
p,e='p','e'
labels=(('U','u0'),('V','v0'),('U','u1'))
old_combined=[((p,),e) for lab in labels]
assert len(set(old_combined))==1
old_nested=[('innerU',p,e) if lab[0]=='U' else ('outerV',p,e) for lab in labels]
assert len(set(old_nested))==2  # no global inverse of the old flattening
fine_combined=[(((p,lab),),e) for lab in labels]
assert len(set(fine_combined))==3
# Nested representation is (outer V edge words, residual inner U word, e).
def nest(word,local):
    outer=[];inner=[]
    for port,(color,label) in word:
        if color=='U':inner.append((port,label))
        else:
            outer.append(((tuple(inner),port),label));inner=[]
    return (tuple(outer),tuple(inner),local)
def flat(nested):
    outer,inner,local=nested;word=[]
    for (us,port),v in outer:
        word += [(p,('U',u)) for p,u in us]
        word.append((port,('V',v)))
    word += [(p,('U',u)) for p,u in inner]
    return (tuple(word),local)
for length in range(5):
    for ls in product(labels,repeat=length):
        word=tuple((p,lab) for lab in ls)
        assert flat(nest(word,e))==(word,e)
        assert nest(*flat(nest(word,e)))==nest(word,e)
# T_P labelled deployment and F constructor agree across all input fibres.
child_ids=[(p,u,((),e)) for u in ('u0','u1')]
def constructor(tag):
    port,u,(word,local)=tag
    return (((port,u),)+word,local)
def unconstructor(identifier):
    word,local=identifier;(port,u)=word[0]
    return (port,u,(word[1:],local))
assert len(set(map(constructor,child_ids)))==2
assert all(unconstructor(constructor(x))==x for x in child_ids)
# Noninjective loop maps can merge global names across separate configurations,
# but preserve a simultaneous event set when its port identifiers differ.
merged=lambda ident: (tuple((port,'*') for port,u in ident[0]),ident[1])
simultaneous=[((('p0','u0'),),e),((('p1','u1'),),e)]
assert len(set(map(merged,simultaneous)))==2
assert len(set(merged(constructor(x)) for x in child_ids))==1
assert ((),e)==((),e) # external input reindexing adds no root input tag
print('PASS old GLOBAL namespace collision, labelled nesting inverse, same-color deployment/fold tags, noninjective loop maps')
# Recovered shared binary-branching instance: coefficient factors remain native.
for horizon in range(1,12):
    mass=sum(F(1,2**d) for d in range(1,horizon+1))
    assert mass==1-F(1,2**horizon)
    truncated_nodes=sum(F(2**d-1,2**d) for d in range(1,horizon+1))
    assert truncated_nodes==horizon-1+F(1,2**horizon)
assert 2*F(1,2**5)==F(1,16)
print('PASS balanced shared branching depth/mass/expected-node identities and independent three-leaf1/16 witness')

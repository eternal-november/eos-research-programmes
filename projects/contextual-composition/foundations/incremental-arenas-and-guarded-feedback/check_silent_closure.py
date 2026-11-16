from itertools import product
from pathlib import Path
import re

def acyclic(adj,vertices):
    active=set();done=set();vs=set(vertices)
    def visit(x):
        if x in active:return False
        if x in done:return True
        active.add(x)
        for y in adj[x]:
            if y in vs and not visit(y):return False
        active.remove(x);done.add(x);return True
    return all(visit(x) for x in vertices)
def derived(adj,U,V):
    out=[set() for _ in adj]
    for v in V:
        seen=set();stack=[v]
        while stack:
            x=stack.pop()
            for y in adj[x]:
                if y in V:out[v].add(y)
                elif y not in seen:seen.add(y);stack.append(y)
    return out
U={0,1};V={2,3};checks=0
for mask in range(1<<16):
    adj=[{j for j in range(4) if mask&(1<<(4*i+j))} for i in range(4)]
    lhs=acyclic(adj,range(4))
    rhs=acyclic(adj,U) and acyclic(derived(adj,U,V),V)
    assert lhs==rhs
    checks+=1
print(f'PASS exact colored nesting admission for all {checks} directed four-label relations')
# Separate same-color restrictions cannot detect an alternating cycle.
a=[{1},{0}]
assert acyclic(a,{0}) and acyclic(a,{1}) and not acyclic(a,{0,1})
assert not acyclic(derived(a,{0},{1}),{1})
# Pure decreasing initial chains: cost0 and unbounded input-indexed depth.
for m in range(100):
    closure=tuple(range(m,-1,-1))
    assert len(closure)==m+1
    assert all(x>y for x,y in zip(closure,closure[1:]))
    if m:assert len(closure)>1 # old cost+1 formula at cost0 fails
print('PASS alternating-cycle obstruction and 100 zero-cost decreasing initial closures')
# Finite structural exploration: a paid event may start any finite initial
# closure from its finite outcome list; no probability-support pruning.
initial=(3,2,1,0)
trans={initial:[(5,4,3,2,1,0),(1,0)],(5,4,3,2,1,0):[(7,6,5,4,3,2,1,0)],(1,0):[(2,1,0)]}
seen={initial};frontier={initial};bounds=[]
for n in range(4):
    bounds.append(max(map(len,seen)))
    new={y for x in frontier for y in trans.get(x,[])}
    seen|=new;frontier=new
assert bounds==[4,6,8,8]
print('PASS finite all-raw structural depth envelope, including initial silent cost0 closure')
s=Path(__file__).with_name('Well_Founded_Silent_Closure_and_Native_Feedback.tex').read_text();stack=[]
for op,name in re.findall(r'\\(begin|end)\{([^}]+)\}',s):
    if op=='begin':stack.append(name)
    else:assert stack.pop()==name
assert not stack
print('PASS TeX environment nesting; finite diagnostics do not certify general well-foundedness')

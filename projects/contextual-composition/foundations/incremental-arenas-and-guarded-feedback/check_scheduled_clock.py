from fractions import Fraction as F
from itertools import product
from collections import defaultdict
from pathlib import Path
import re
# Terminal outcomes include one zero-weight ghost; branch creates two children.
def trees(d):
    out=[('T',b) for b in range(3)]
    if d:out += [('R',x,y) for x,y in product(trees(d-1),repeat=2)]
    return out
def flatten(t,addr):
    if t[0]=='T':return {addr:('T',t[1])}
    out={addr:('R',)}
    out.update(flatten(t[1],addr+(0,)));out.update(flatten(t[2],addr+(1,)))
    return out
def prob(w):return F(1,2) if w[0]=='R' else (F(1,4) if w[1]<2 else F(0))
def pick(active,mode,past):
    a=sorted(active)
    if mode=='all':return a
    if mode=='first':return a[:1]
    if mode=='last':return a[-1:]
    if mode=='alternating':return a[::2]
    return a[:1] if sum(w[1] for w in past.values() if w[0]=='T')%2==0 else a[-1:]
def simulate(forest,mode):
    target={}
    for i,t in enumerate(forest):target.update(flatten(t,(i,)))
    active={(i,) for i in range(len(forest))};past={};plan=[];weight=F(1)
    while active:
        scope=pick(active,mode,past);assert scope
        assert not any(x in past for x in scope)
        plan.append(tuple(scope))
        for a in scope:
            w=target[a];past[a]=w;weight*=prob(w);active.remove(a)
            if w[0]=='R':active.update((a+(0,),a+(1,)))
    assert past==target and len(plan)<=len(target)
    return target,plan,weight
modes=('all','first','last','alternating','history')
cases=[(t,) for t in trees(2)]+list(product(trees(1),repeat=2))+[()]
size_laws={mode:defaultdict(F) for mode in modes}
for forest in cases:
    base=None
    for mode in modes:
        target,plan,w=simulate(forest,mode)
        signature=(target,w)
        if base is None:base=signature
        assert signature==base
        size_laws[mode][len(target)]+=w
        # Finite node-count row sees terminal history within its n-step unroll.
        assert len(plan)<=len(target) or not target
assert all(size_laws[x]==size_laws['all'] for x in modes)
assert any(simulate(f,'all')[2]==0 for f in cases)
print(f'PASS {len(cases)} finite raw forests (incl ghosts/empty) under five schedulers; fixed-size row equality')
f=(('R',('T',0),('T',1)),)
assert len(simulate(f,'all')[1])==2 and len(simulate(f,'first')[1])==3
print('PASS explicit failure of step-clock equality despite size-clock equality')
# Prefix-law normalization for all/serial schedulers, no zero-history pruning.
outcomes=(('T',0),('T',1),('T',2),('R',))
for mode in ('all','first'):
    rows=[({}, {(0,)},F(1))]
    for depth in range(3):
        nxt=[]
        for past,active,w in rows:
            if not active:nxt.append((past,active,w));continue
            scope=pick(active,mode,past);local=[]
            for draw in product(outcomes,repeat=len(scope)):
                pp=dict(past);aa=set(active);ww=w
                for a,o in zip(scope,draw):
                    pp[a]=o;aa.remove(a);ww*=prob(o)
                    if o[0]=='R':aa.update((a+(0,),a+(1,)))
                local.append((pp,aa,ww))
            assert sum(x[2] for x in local)==w
            nxt+=local
        rows=nxt
        assert sum(x[2] for x in rows)==1
    assert any(x[2]==0 for x in rows)
print('PASS normalized scheduled prefix fibres retaining all zero histories through horizon3')
# Same untimed two-root terminal forest: last-scope deletion needs plan.
plan_a=(((0,),),((1,),));plan_b=(((1,),),((0,),))
assert set(sum(plan_a,()))==set(sum(plan_b,()))
assert plan_a[:-1]!=plan_b[:-1]
# Nonlevel ideal root+two of three enabled children, shared diagonal draw.
J={(),(0,),(1,)}
assert (2,) not in J and all(a[:-1] in J for a in J if a)
q={(0,0):F(1,2),(0,1):F(0),(1,0):F(0),(1,1):F(1,2)}
assert sum(q.values())==1
assert sum(v for (x,y),v in q.items() if x==0)==F(1,2)
assert sum(v for (x,y),v in q.items() if y==0)==F(1,2)
print('PASS timed-grade necessity and nonlevel shared-scope ideal witness')
s=Path(__file__).with_name('Scheduled_Event_Ideals_and_Size_Clock.tex').read_text();stack=[]
for op,name in re.findall(r'\\(begin|end)\{([^}]+)\}',s):
    if op=='begin':stack.append(name)
    else:assert stack.pop()==name
assert not stack
print('PASS TeX environment nesting; no compilation/formal verification claimed')

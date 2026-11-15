from itertools import product
from fractions import Fraction as F
from ranked_adapter import *
from occurrence_machine import Machine

def split(arg,caps,w,s):
    gamma,a=arg
    assert a==17 # distinct current input, not capture gamma
    tree=Node('split',(Leaf(3,(caps[0],)),Leaf(3,(caps[1],))))
    return [[Outcome('split',F(1),(1,),'split',tree,w),Outcome('split',F(0),(7,),'split',tree,w)]]

def update(arg,caps,w,s):
    gamma,a=arg
    assert a==3
    return [[Outcome('choice',p,(2,),'update',Node('update',(Leaf(gamma+a+i,caps),)),w,stores={c:s[c]+gamma+i for c in caps}) for i,p in enumerate((F(1,4),F(3,4)))]]
from occurrence_machine import Outcome
lib=RankedAdapter({'leaf':Template(0,lambda gamma:Op('update',lambda a:(gamma,a))),
                  'outer':Template(1,lambda gamma:Bind(Op('split',lambda a:(gamma,a)),lambda b:Invoke(lambda a:('leaf',gamma))))},1)
prims={'split':split,'update':update}
count=0
for gamma in (2,5):
    for choices in product(range(2),repeat=3):
        term=ParameterCall('outer',gamma)
        it=iter(choices)
        oracle=lib.evaluate(term,17,('a','b'),prims,lambda name:(0,next(it)),stores={'a':10,'b':20})
        m=Machine(lib.compile(term),17,caps=('a','b'),stores={'a':10,'b':20},primitives=prims,procedures=lib.procedures)
        it=iter(choices)
        for _ in range(200):
            if m.jobs[0].mode=='done': break
            pid=m.phase_next();j=m.jobs[pid]
            oi=next(it) if j.mode=='eval' and isinstance(j.term,Op) else 0
            m.step(pid,outcome=oi)
        r=m.jobs[0].result
        assert (r.tree,r.raw,m.weight,m.cost,m.word,m.world,m.stores)==(oracle.tree,oracle.raw,oracle.weight,oracle.cost,oracle.word,oracle.world,oracle.stores)
        assert m.word==('split','update','update')
        assert m.owned(('result',0))==('a','b')
        count+=1
# Pure parameter substitution: instantiate Gamma via sigma; current input remains17.
sigma=lambda delta:delta+3
old=ParameterCall('outer',sigma(2));new=ParameterCall('outer',5)
for term in (old,new):
    m=Machine(lib.compile(term),17,caps=('a','b'),stores={'a':10,'b':20},primitives=prims,procedures=lib.procedures).prefix(200,stop_at_root=True)
    result=(m.jobs[0].result,m.weight,m.cost,m.word,m.stores)
    if term is old: expected=result
    else: assert result==expected
# Administrative inlining preserves raw record after the same call-marker erasure.
for term in (ParameterCall('outer',5),lib.templates['outer'].body(5)):
    m=Machine(lib.compile(term),17,caps=('a','b'),stores={'a':10,'b':20},primitives=prims,procedures=lib.procedures).prefix(200,stop_at_root=True)
    result=(m.jobs[0].result,m.weight,m.cost,m.word,m.stores)
    if isinstance(term,ParameterCall):expected=result
    else:assert result==expected
bad=RankedAdapter({'self':Template(0,lambda g:ParameterCall('self',g))},0)
try:
    Machine(bad.compile(ParameterCall('self',0)),17,procedures=bad.procedures).prefix(10)
    raise AssertionError('rank cycle accepted')
except ValueError as e:assert 'nondecreasing' in str(e)
print(f'PASS: {count} ranked exact branches, capture/input separation, parameter substitution, body plugging, rank-cycle rejection')
# Final stores are indexed by live result ownership, not archived retired entries.
def consume(arg,caps,w,s):
    return [[Outcome('consume',F(1),(1,),'consume',Node('consume',()),w,consume=caps)]]
consuming=RankedAdapter({'consume':Template(0,lambda capture:Op('consume'))},0)
t=ParameterCall('consume','ordinary capture')
o=consuming.evaluate(t,17,('a',),{'consume':consume},lambda name:(0,0),stores={'a':'old-private'})
m=Machine(consuming.compile(t),17,caps=('a',),stores={'a':'old-private'},primitives={'consume':consume},procedures=consuming.procedures).prefix(20,stop_at_root=True)
assert m.ledger['a']==('retired','a') and m.stores['a']=='old-private'
assert live_store_observation(o.tree,o.stores)==live_store_observation(m.jobs[0].result.tree,m.stores)==()
print('PASS: final store projection excludes retired archival entries')

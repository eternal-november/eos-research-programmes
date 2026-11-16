"""Finite discriminators only; not unrestricted coherence certification."""
from dataclasses import dataclass,replace
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json,re,hashlib
@dataclass(frozen=True)
class State:
 kind:str
 world:int
 cache:int
 pending:tuple
 seen:tuple=()
 done:bool=False
 ports:tuple=()
def init(kind,w):
 return State(kind,w,w,('ack',),ports=() if kind=='leaf' else ('p',))
def rebase(s,edge):
 src,dst,event=edge
 assert s.world==src
 return replace(s,world=dst,seen=s.seen+(event,))
def closure(kinds,w,prefix=()):
 if not kinds:return {}
 s=init(kinds[0],w);out={prefix:s}
 for p in s.ports:out.update(closure(kinds[1:],w,prefix+(p,)))
 return out
def flatten_init(expr,w):
 # The grouping is syntax only, never a wait-for-completion barrier.
 def word(e):return (e,) if isinstance(e,str) else sum((word(x) for x in e),())
 return closure(word(expr),w)
def update(states,active,edge):
 out={}
 for path,s in states.items():
  out[path]=active[path] if path in active else rebase(s,edge)
  assert out[path].world==edge[1]
 return out
left=(('root','middle'),'leaf');right=('root',('middle','leaf'))
l=flatten_init(left,0);r=flatten_init(right,0);assert l==r
edge=(0,1,'paid-world-update')
active={():replace(l[()],world=1,cache=17,seen=('own-active',))}
l=update(l,active,edge);r=update(r,active,edge);assert l==r
assert l[('p',)].cache==l[('p','p')].cache==0
assert l[('p',)].pending==l[('p','p')].pending==('ack',)
assert init('middle',1).cache==1!=l[('p',)].cache
assert rebase(init('middle',0),edge)!=init('middle',1)
# Rebase functor: action of a word equals consecutive event actions.
e2=(1,2,'next-update')
s=init('middle',0)
sequential=rebase(rebase(s,edge),e2)
word_action=replace(s,world=2,seen=('paid-world-update','next-update'))
assert sequential==word_action
# All five bracketings of four factors have identical initialization.
four=[((('root','middle'),'middle'),'leaf'),(('root',('middle','middle')),'leaf'),(('root','middle'),('middle','leaf')),('root',(('middle','middle'),'leaf')),('root',('middle',('middle','leaf')))]
assert all(flatten_init(x,0)==flatten_init(four[0],0) for x in four)
# Simultaneous correlated siblings, including zero tuples, with one passive observer.
base={('a',):init('leaf',0),('b',):init('leaf',0),('observer',):init('leaf',0)}
q={(a,b):F(int(a!=b),2) for a,b in product(range(2),repeat=2)}
posts={}
for (a,b),mass in q.items():
 active={('a',):replace(base[('a',)],world=1,cache=a,done=True),('b',):replace(base[('b',)],world=1,cache=b,done=True)}
 posts[(a,b)]=update(base,active,(0,1,'beta'))
 assert posts[(a,b)][('observer',)].cache==0
 assert posts[(a,b)][('observer',)].pending==('ack',)
 assert posts[(a,b)][('observer',)].seen==('beta',)
assert sum(q.values())==1 and len(posts)==4 and sum(x==0 for x in q.values())==2
# Raw source auxiliary bit includes a third zero atom; forgetting it pushes q exactly.
audit={0:F(1,2),1:F(1,2),2:F(0)}
source={(a,b,x,y):p*audit[x]*audit[y] for (a,b),p in q.items() for x,y in product(audit,repeat=2)}
for ab,p in q.items():assert sum(v for z,v in source.items() if z[:2]==ab)==p
assert len(source)==36
# Actual augmented coefficient map on K x_k K = k^3: retain first private direction, erase second.
def mv(A,v):return tuple(sum(a*x for a,x in zip(row,v)) for row in A)
A=((1,0,0),(0,1,0),(0,0,0));I=((1,0,0),(0,1,0),(0,0,1))
for v in product(range(3),repeat=3):
 assert mv(A,v)[0]==v[0]
 assert mv(A,mv(A,v))==mv(A,v)
 assert mv(I,mv(A,v))==mv(A,v)
assert mv(A,(0,0,1))==(0,0,0)!=mv(I,(0,0,1))
# Every old scope partitions by actor and reassembles without losing zero tuples.
events=(('root','e0'),('child1','e1'),('child2','e2'))
partitions=0
for flags in product((0,1),repeat=3):
 chosen=[e for e,b in zip(events,flags) if b]
 if not chosen:continue
 groups={v:tuple(e for e in chosen if e[0]==v) for v in dict(chosen)}
 assert set(sum(groups.values(),()))==set(chosen);partitions+=1
tex=(Path(__file__).resolve().parent.parent / 'World_Rebased_Multi_Active_Open_Assembly.tex').read_text();stack=[]
for op,name in re.findall(r'\\(begin|end)\{([^}]+)\}',tex):
 if op=='begin':stack.append(name)
 else:assert stack.pop()==name
assert not stack
print(json.dumps({'status':'PASS','world_dependent_initializer':{'old_child_cache':0,'delayed_child_cache':1,'seed_naturality':False},'four_factor_bracketings':5,'multi_active_joint_raw_tuples':4,'zero_joint_tuples':2,'auxiliary_source_raw_tuples':36,'actual_coefficient_map_nonidentity':True,'old_scope_partitions':partitions,'source_sha256':hashlib.sha256(tex.encode()).hexdigest(),'scope':'finite world/rebase/joint and coefficient discriminators, not full theorem verification'},indent=2))

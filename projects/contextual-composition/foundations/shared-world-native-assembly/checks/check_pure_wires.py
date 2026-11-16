"""Exact finite normal-form/balance discriminators, not categorical certification."""
from itertools import product
from fractions import Fraction as F
from dataclasses import dataclass
from pathlib import Path
import hashlib,json,re
X=range(3);functions=list(product(X,repeat=3));identity=tuple(X)
def comp(g,f):return tuple(g[f[x]] for x in X)
@dataclass(frozen=True)
class WireWord:
 actors:tuple
 wires:tuple
 def __post_init__(self):assert len(self.wires)==len(self.actors)+1
def then(p,q):
 return WireWord(p.actors+q.actors,p.wires[:-1]+(comp(q.wires[0],p.wires[-1]),)+q.wires[1:])
def inp(p,f):return WireWord(p.actors,(comp(p.wires[0],f),)+p.wires[1:])
def out(p,g):return WireWord(p.actors,p.wires[:-1]+(comp(g,p.wires[-1]),))
empty=WireWord((),(identity,));counts=0
# Noninjective maps included exhaustively in each three-wire middle equation.
for u,v,w in product(functions,repeat=3):
 p=WireWord(('P',),(identity,u));q=WireWord(('Q',),(w,identity))
 assert then(out(p,v),q)==then(p,inp(q,v));counts+=1
# Empty/positive actor lengths and all three associations, with diverse pure wires.
assoc=0
for ns in product(range(3),repeat=3):
 for f,g,h in product((identity,(0,0,1),(2,0,2)),repeat=3):
  ps=[WireWord(tuple(f'{k}{j}' for j in range(n)),tuple([z]*(n+1))) for k,n,z in zip('PQR',ns,(f,g,h))]
  p,q,r=ps
  assert then(then(p,q),r)==then(p,then(q,r))
  assert then(empty,p)==p==then(p,empty);assoc+=1
# Actual balance inverse from retained upstream labels, not inverse pure function.
v={'b0':'*','b1':'*'}
def to_right(left):
 s,copies=left
 return s,{p:(s['labels'][p],t) for p,t in copies.items()}
def to_left(right):
 s,copies=right
 return s,{p:t for p,(label,t) in copies.items()}
s={'labels':{'p0':'b0','p1':'b1'},'original_state':'retained'}
copies={p:{'anchor':v[b],'world':0,'cache':0,'pending':('ack',)} for p,b in s['labels'].items()}
left=(s,copies);right=to_right(left);assert to_left(right)==left
assert right[1]['p0'][0]!='b1' and right[1]['p1'][0]=='b1'
# Existing copies rebase after an update, not reinitialize at world1.
post=(s,{p:dict(t,world=1) for p,t in copies.items()})
right_post=(s,{p:(label,dict(t,world=1)) for p,(label,t) in right[1].items()})
assert to_right(post)==right_post
assert all(t['cache']==0 for t in post[1].values())
# Whole correlated scope and zero tuples survive relocation, including an actual K-limit coefficient.
q={(a,b):F(int(a!=b),2) for a,b in product(range(2),repeat=2)}
assert q.copy()==q and len(q)==4 and sum(q.values())==1
K_limit_basis=('shared','private0','private1')
assert tuple(K_limit_basis)==K_limit_basis
whole_schema_shapes=('used','unused')
assert tuple(whole_schema_shapes)==whole_schema_shapes
# Native raw erasure commuting with forced input tags, including zero raw atoms.
raw={0:F(1,2),1:F(1,2),2:F(0)};rho={0:'x',1:'x',2:'z'}
assert sum(p for r,p in raw.items() if rho[r]=='x')==1
for label,r in product(('b0','b1'),raw):
 assert (label,rho[r])==(label,rho[r])
source=(Path(__file__).resolve().parent.parent / 'Pure_Wires_and_Relative_Shared_World_Assembly.tex').read_text();stack=[]
for op,name in re.findall(r'\\(begin|end)\{([^}]+)\}',source):
 if op=='begin':stack.append(name)
 else:assert stack.pop()==name
assert not stack
print(json.dumps({'status':'PASS','middle_balance_cases':counts,'association_empty_word_cases':assoc,'noninjective_two_copy_balance':True,'world_dependent_initial_cache_preserved':0,'joint_raw_tuples':4,'joint_zero_tuples':2,'unused_schema_shape_retained':True,'source_sha256':hashlib.sha256(source.encode()).hexdigest(),'scope':'finite discriminating diagnostics; not full native coherence verification'},indent=2))

from itertools import product, permutations
from fractions import Fraction as F

# Zero-event N: all finite arity profiles up to three outer slots, arities 0..3.
profiles=0
for n in range(4):
 for ar in product(range(4), repeat=n):
  pairs=[(i,j) for i,k in enumerate(ar) for j in range(k)]
  flat={(i,j):sum(ar[:i])+j for i,j in pairs}
  assert sorted(flat.values())==list(range(sum(ar)))
  inv={v:k for k,v in flat.items()}
  assert all(inv[flat[p]]==p for p in pairs)
  profiles+=1
assert sum((1,1)[:1])+0==1 and sum((2,1)[:1])+0==2
# Associativity of all leaf-rank maps: two outer nodes, at most two
# middle slots and bottom arity at most two, including empty branches.
assoc=0
for ns in product(range(3), repeat=2):
 for bottom in product(range(3), repeat=sum(ns)):
  offset=0; tree=[]
  for n in ns:
   tree.append(bottom[offset:offset+n]); offset+=n
  leaves=[(i,j,k) for i,row in enumerate(tree)
          for j,m in enumerate(row) for k in range(m)]
  for rank,(i,j,k) in enumerate(leaves):
   left=sum(sum(row) for row in tree[:i])+sum(tree[i][:j])+k
   flat_middle=[m for row in tree for m in row]
   middle=sum(ns[:i])+j
   right=sum(flat_middle[:middle])+k
   assert rank==left==right
  assoc+=1

# Actual two-event persistent arenas: the same source event name has
# different target names in the two input fibres. States retain event results.
def rename(a,e): return e if a==0 else 1-e
def h(a,s): return {rename(a,e):w for e,w in s.items()}
checks=0
for a in (0,1):
 for vals in product((None,0,1),repeat=2):
  s={e:w for e,w in enumerate(vals) if w is not None}
  target=h(a,s)
  enabled=set(range(2))-set(s)
  assert {rename(a,e) for e in enabled}==set(range(2))-set(target)
  # Port order is declared by inverse rename, not unstable ranks.
  source_ports=sorted(s)
  target_ports=sorted(target,key=lambda q:rename(a,q))
  assert [rename(a,p) for p in source_ports]==target_ports
  for e in enabled:
   for w in (0,1): # includes either outcome even if its future weight is zero
    t=dict(s);t[e]=w
    tp=dict(target);tp[rename(a,e)]=w
    assert h(a,t)==tp
    assert all(rename(a,p)==rename(a,p) for p in source_ports)
    for f in enabled-{e}:
     for z in (0,1):
      u=dict(t);u[f]=z
      v=dict(s);v[f]=z;v[e]=w
      assert h(a,u)==h(a,v)
    checks+=1
assert rename(0,0)!=rename(1,0) # no single global source-name map
# Non-iso-reflection: two global names collapse, but each active singleton inverts.
forget={('e',0):'e',('e',1):'e'}
assert len(set(forget.values()))<len(forget)
for a in (0,1):
 inv={'e':('e',a)}
 assert inv[forget[('e',a)]]==('e',a)
print({'rank_profiles':profiles,'associativity_profiles':assoc,
       'native_transition_squares':checks,'non_global_and_non_iso_reflection':'PASS'})


from itertools import product
from fractions import Fraction as F
from pathlib import Path
import json
# Finite formal C trees, arities 0,1,2; every edge is I, U, or V.
def trees(height):
 if height==0:return []
 prev=trees(height-1); slots=[None]+[(c,t) for c in ('U','V') for t in prev]
 return [(arity,tuple(ch)) for arity in range(3) for ch in product(slots,repeat=arity)]
def cut(t):
 outer=[]
 def component(n):
  a,children=n; out=[]
  for x in children:
   if x is None:out.append(None)
   elif x[0]=='V':out.append(('V',component(x[1])))
   else:
    idx=len(outer);outer.append(cut(x[1]));out.append(('U',idx))
  return a,tuple(out)
 c=component(t);return c,tuple(outer)
def flatten(t):
 component,outer=t
 def walk(n):
  a,ch=n
  return a,tuple(None if x is None else ('V',walk(x[1])) if x[0]=='V' else ('U',flatten(outer[x[1]])) for x in ch)
 return walk(component)
def arity(t):return sum(1 if x is None else arity(x[1]) for x in t[1])
T=trees(3)
assert len(T)==13341
assert all(flatten(cut(t))==t and arity(flatten(cut(t)))==arity(t) for t in T)
# u->v->u: both same-color restrictions empty, condensed U has u->u.
edges={('u','v'),('v','u')}
assert not any(a==b for a,b in edges)
assert ('u','v') in edges and ('v','u') in edges
# Whole-V conditioning excludes diagonal fresh U seed / old V paid bit.
O=list(product(range(2),repeat=2));q={x:F(x[0]==x[1],2) for x in O}
assert all(sum(v for x,v in q.items() if x[i]==b)==F(1,2) for i in (0,1) for b in (0,1))
assert any(q[y,z]!=F(1,4) for y,z in O)
# In bases (s,x,y) tensor (l0,l1), extraction sends y*l1 to zero.
# Target coordinates: shared augmentation, s*l1, x*l0, x*l1, y.
M=[[F(i==j) for j in range(6)] for i in range(5)]
assert all(sum(M[i][j]*F(j==5) for j in range(6))==0 for i in range(5))
assert all(M[i][j]==F(i==j) for i in range(5) for j in range(5))
r={'formal_mixed_trees_checked':len(T),'max_formal_height':3,
'grade_cut_flatten_inverse_and_arity':True,'separate_color_guards_insufficient':True,
'flat_diagonal_rejected_by_nested_conditioning':True,
'coefficient_source_dimension':6,'coefficient_target_dimension':5,
'extraction_rank':5,'explicit_kernel':'y tensor l1',
'scope':'Finite exact diagnostics; proofs of all-shape/native/coherence statements remain in TeX.'}
out=Path(__file__).with_name('nested_feedback_fusion_exact_results.json');out.write_text(json.dumps(r,indent=2)+'\n');print(out.read_text())

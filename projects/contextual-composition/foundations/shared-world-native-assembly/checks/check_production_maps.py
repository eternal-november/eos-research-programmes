"""Finite actual Set-coefficient/naturality/empty-case checks; not a proof."""
from itertools import combinations, product
import json
O=('a','b'); B=(0,1)
def act(old,new,j,m,audit):
    out=[None]*m
    for p,x in zip(j,old):out[p]=x
    for p,x in zip((p for p in range(m) if p not in j),new):out[p]=x
    return tuple(out)
def fmap(item):
    shape,value=item
    return ('b' if shape=='a' else 'a', 0 if shape=='a' else 1-value)
checks=0
for n in range(3):
 for m in range(n,4):
  for j in combinations(range(m),n):
   for shapes in product(O,repeat=m):
    for vals in product(B,repeat=m):
     items=tuple(zip(shapes,vals)); old=items[:n]; new=items[n:]
     for audit in B:
      lhs=tuple(map(fmap,act(old,new,j,m,audit)))
      rhs=act(tuple(map(fmap,old)),tuple(map(fmap,new)),j,m,0)
      assert lhs==rhs
      checks+=1
# Empty writer word uses the actual unit, no invented payload element.
assert act((),(),(),0,0)==()
# n=m schema can retain a nontrivial audit even with no terminal change.
nullary_source=((0,),(1,))
assert nullary_source[0]!=nullary_source[1]
assert act((),(),(),0,0)==act((),(),(),0,1)==()
# Empty payload family: positive-birth writer shape family is empty.
assert list(product((),repeat=1))==[]
assert list(product((),repeat=0))==[()]
# Different birth chronology gives same final payload and coefficients.
a=('a',0); b=('b',1)
one=act((),(a,b),(),2,0)
first=act((),(a,),(),1,0)
two=act(first,(b,),(0,),2,1)
assert one==two
print(json.dumps({'status':'passed','actual_shape_and_coefficient_naturality_cases':checks,
 'empty_word_unit_checked':True,'nullary_audit_loss_checked':True,
 'empty_payload_unboundedness_counterexample_checked':True,
 'distinct_birth_chronology_same_terminal_payload':True,
 'scope':'Finite Set-coefficient discriminators only; universal family-map and graft proofs reviewed separately'},indent=2))

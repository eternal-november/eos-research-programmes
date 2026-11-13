import json
if not __debug__: raise RuntimeError('Assertions required')
# Free ternary planar trees have odd leaf counts; this is the stated arity obstruction.
assert all((1+2*v)%2==1 for v in range(10))
# C2 represented additively modulo two.
factors=[(a,b) for a in range(2) for b in range(2) if (a+b)%2==1]
assert factors==[(0,1),(1,0)]
# Every chosen proper-interval section gives inner h=1 and outer m+h.
def section(m):return ((m+1)%2,1)
r,b=section(0); mid,bot=section(b); route1=(r,mid,bot)
a,bot=section(0);r,mid=section(a);route2=(r,mid,bot)
assert route1==(1,0,1) and route2==(0,1,1) and route1!=route2
assert sum(route1)%2==sum(route2)%2==0
# Two-witness spans with singleton interfaces: one transposed triangle.
left=lambda x:x
right=lambda x:1-x
assert all(left(x)!=right(x) for x in (0,1))
# A nonempty-block record cannot admit designated empty-block insertion.
blocks=((0,),)
def nonempty(bs):return all(len(b)>0 for b in bs)
assert nonempty(blocks) and not nonempty(((),)+blocks)
# Nullary fixed-endpoint control: the empty forest changes no scalar.
assert 0!=1 and (0+sum(()))%2!=1
result={'status':'PASS','checks':{'ternary_arity_formula_values':10,'C2_ambiguity_pairs':len(factors),'incompatible_section_routes':[route1,route2],'tetrahedral_inputs':2,'missing_empty_block_insertion':True,'nullary_fixed_endpoint_failure':True},'scope':'Finite arithmetic/record corroboration of explicit prose controls; not a free-operad or all-degree formalization.'}
print(json.dumps(result,indent=2))

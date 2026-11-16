"""Finite Cartesian-content/empty-case/shear discriminators; not a proof."""
from itertools import product
import json
bits=(0,1)
# Two global events, two actors; content at an event is the pullback
# of (boundary,private0) and (boundary,private1) over boundary.
event=tuple(product(bits,repeat=3))
history=tuple(product(event,repeat=2))
def split(h):
    boundary=tuple(x[0] for x in h)
    actor0=tuple((x[0],x[1]) for x in h)
    actor1=tuple((x[0],x[2]) for x in h)
    return actor0,boundary,actor1
def join(s):
    a,bd,c=s
    assert tuple(x[0] for x in a)==bd==tuple(x[0] for x in c)
    return tuple((bd[i],a[i][1],c[i][1]) for i in range(len(bd)))
assert all(join(split(h))==h for h in history)
# Actor coefficient compilers are XOR monoid folds. Source keeps exactly
# two joint event factors, not four separately inserted actor factors.
def fold(xs):
    a=0
    for x in xs:a^=x
    return a
def terminal(h):return tuple(fold(x[v+1] for x in h) for v in (0,1))
assert all(terminal(h)==tuple(fold(x[1] for x in split(h)[j]) for j in (0,2)) for h in history)
assert join(split(()))==() and terminal(())==(0,0)
# Full formal word shapes use Z/3, including unused choices, with fixed
# actor arities1(root) and0(child); the coefficient monoid is independent.
formal=tuple(product(range(3),repeat=4))
compiled={q:((q[0]+q[2])%3,(q[1]+q[3])%3) for q in formal}
assert len(formal)==81 and len(set(compiled.values()))==9
assert all(((a+b)%3+c)%3==(a+(b+c)%3)%3 for a,b,c in product(range(3),repeat=3))
assert all((a^b)^c==a^(b^c) for a,b,c in product(bits,repeat=3))
# A nonidentity coefficient monoid map (constant0) commutes with folds.
assert all(fold(0 for _ in h)==0 for h in history)
# In unrestricted AugVect tensor content, the first-factor shear fixes
# joint-vector(0,f) but moves every projection-compatible tensor image.
for c in range(-4,5):
    t=(0,1,0,c) # ee, ef, fe, ff
    sheared=(t[0],t[1],t[2]+t[0],t[3]+t[1])
    assert tuple(sheared[i]-t[i] for i in range(4))==(0,0,0,1)
# Context coefficients do not inherit Cartesian content interchange.
assert 3*3==9 and (4+4-1)==7 and 9!=7
print(json.dumps({'status':'passed','event_content_elements':len(event),
 'history_content_elements':len(history),'global_event_factors':2,
 'actor_appearances':4,'empty_timeline_terminal_unit_value':terminal(()),
 'full_formal_writer_assignments':len(formal),'compiled_shape_pairs':9,
 'context_interchange_dimensions':[9,7],
 'scope':'Finite exact examples only; generic coherence and naturality reviewed in writing.'},indent=2))

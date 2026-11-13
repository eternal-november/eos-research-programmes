"""Exact rational regression checks; not a replacement for the written proofs."""
from fractions import Fraction as F
import json

def mm(a,b):
    assert len(a[0]) == len(b)
    return [[sum((x*y for x,y in zip(row,col)),F(0)) for col in zip(*b)] for row in a]

def row_stochastic(a):
    return all(all(v>=0 for v in r) and sum(r)==1 for r in a)

def text(a):
    return [[str(x) for x in row] for row in a]

sg=[[F(1,2),F(1,2)]]
sh=[[F(1),F(0),F(0)],[F(0),F(1,2),F(1,2)]]
direct=[[F(1,3)]*3]
composed=mm(sg,sh)
assert composed == [[F(1,2),F(1,4),F(1,4)]] and composed != direct

# Nontrivial measured interface and two adjacent kernels.
k=[[F(1,4),F(3,4)],[F(2,3),F(1,3)]]
l=[[F(1,5),F(4,5)],[F(3,5),F(2,5)]]
g=[[F(1),F(0)],[F(0),F(1)],[F(0),F(1)]]
s=[[F(1),F(0),F(0)],[F(0),F(1,3),F(2,3)]]
assert mm(s,g)==[[F(1),F(0)],[F(0),F(1)]]
kp,lp=mm(k,s),mm(g,l)
assert row_stochastic(kp) and row_stochastic(lp)
assert mm(kp,lp)==mm(k,l)

p=[[F(3,4),F(1,4)],[F(1,4),F(3,4)]]
d0=[[F(3,4),F(0)],[F(0),F(1,4)]]
d1=[[F(1,4),F(0)],[F(0),F(3,4)]]
m0,m1=mm(p,d0),mm(p,d1)
s0=[[F(1,2),F(1,2)]]
q=[[F(1)],[F(1)]]
assert mm(s0,p)==s0
sm0=mm(s0,m0)
lifted=mm(mm(sm0,q),s0)
assert sm0==[[F(3,8),F(1,8)]]
assert lifted==[[F(1,4),F(1,4)]] and sm0!=lifted
assert all(v>0 for m in (m0,m1) for r in m for v in r)
same=sum(mm(mm(mm(s0,m),m),q)[0][0] for m in (m0,m1))
assert same==F(9,16)

print(json.dumps({
 "all_checks_passed":True,
 "naked_sections_composite":text(composed),
 "naked_sections_direct":text(direct),
 "adjacent_normalized_cancellation":True,
 "stationary_transition_lift":True,
 "outcome_conditioned_fine_row":text(sm0),
 "purported_fixed_section_row":text(lifted),
 "strictly_positive_symbols":True,
 "true_same_consecutive_observation_probability":str(same),
 "one_state_same_probability":"1/2"
},indent=2))

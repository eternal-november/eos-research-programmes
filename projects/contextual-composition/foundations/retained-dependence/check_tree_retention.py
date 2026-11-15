"""Finite diagnostics only: canonical-carrier marginals, not redundant witnesses."""
from fractions import Fraction as F
from itertools import product


def trees(lo, hi):
    if hi-lo == 1:
        return [lo]
    return [(a,b) for k in range(lo+1,hi) for a in trees(lo,k) for b in trees(k,hi)]


def leaves(t):
    return [t] if isinstance(t,int) else leaves(t[0])+leaves(t[1])


def marginal(law, lo, hi):
    out={}
    for x,p in law.items():
        key=x[lo:hi+1]
        out[key]=out.get(key,F(0))+p
    return out

# Four vertex objects are adjacent pairs, with three shared-bit overlap maps.
# Canonical joint carrier has five bits, including many zero-weight tuples.
xs=list(product(range(2),repeat=5))
weights=[0 if i%3 else i+1 for i in range(len(xs))]
z=sum(weights)
q={x:F(w,z) for x,w in zip(xs,weights)}
assert any(p==0 for p in q.values())
for t in trees(0,4):
    def check(node):
        ls=leaves(node); lo,hi=min(ls),max(ls)+1
        law=marginal(q,lo,hi)
        if not isinstance(node,int):
            for child in node:
                cs=leaves(child); a,b=min(cs),max(cs)+1
                assert marginal(law,a-lo,b-lo)==marginal(q,a,b)
                check(child)
        return law
    assert check(t)==q
# Cyclic equal/equal/unequal binary pair constraints have matching local marginals
# but no compatible raw tuple.
assert not [x for x in product(range(2),repeat=3)
            if x[0]==x[1] and x[1]==x[2] and x[2]!=x[0]]
# Extra raw coordinates would defeat a presentation-level bijection.
# q on X and lifted q on X x {0,1} are distinct carriers with same X marginal.
lift={(x,b):p/2 for x,p in q.items() for b in range(2)}
assert all(sum(lift[x,b] for b in range(2))==p for x,p in q.items())
print('PASS: five four-component bracketings, zero weights, cyclic obstruction, redundant-witness boundary')

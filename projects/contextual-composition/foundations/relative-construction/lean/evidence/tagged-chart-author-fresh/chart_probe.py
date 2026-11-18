'''One-object cyclic-3 groupoid. A chart equivalence with both underlying
functors identity, but nonidentity unit a and counit -a, is permitted.'''
from itertools import product
for a,q in product((1,2),range(3)):
    descended=(a+q)%3  # inverse counit followed by q
    assert (descended-a)%3==q
    assert descended!=q   # forgetting the chart unit is observable
# Commuting an arbitrary pair of bijective two-element components with the
# unique moving-base arrow acting by identity enforces equality of the pair.
perms=[(0,1),(1,0)]
good=[(f,g) for f,g in product(perms,repeat=2) if all(f[x]==g[x] for x in range(2))]
assert good==[(f,f) for f in perms]
print('6/6 chart equations hold; 6/6 naked restrictions fail; 2/4 invertible component families descend.')

from fractions import Fraction as F
from itertools import product
bits=range(2)
correlated={(s,t,u):F(u==s,4) for s,t,u in product(bits,repeat=3)}
independent={(s,t,u):F(1,8) for s,t,u in product(bits,repeat=3)}
for law in (correlated,independent):
    assert sum(law.values())==1
    for s,t in product(bits,repeat=2):
        assert sum(law[s,t,u] for u in bits)==F(1,4)
    for t,u in product(bits,repeat=2):
        assert sum(law[s,t,u] for s in bits)==F(1,4)
assert sum(v for (s,t,u),v in correlated.items() if s==u)==1
assert sum(v for (s,t,u),v in independent.items() if s==u)==F(1,2)
# For an arbitrary input prior alpha, ordinary two-step feedback mass is 1/2.
# Exact grid regression is not the general proof: each conditional row has
# 1/2 probability of returning to its own initial state.
for k in range(21):
    p={0:F(k,20),1:F(20-k,20)}
    law={(s,t,u):p[s]*F(1,4) for s,t,u in product(bits,repeat=3)}
    assert sum(v for (s,t,u),v in law.items() if s==u)==F(1,2)
print('PASS: both joint marginals, distinct couplings, shared closure, independent nonclosure; 21-prior regression.')

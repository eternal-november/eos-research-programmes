"""Exact finite check of fixed seed encoding versus permitted local recoding.
This is an obstruction to a pinned implementation, not to equal behavior laws.
"""
from fractions import Fraction as F
from itertools import product
import json

bits=(0,1)
# Chart1 output e; chart2 output e2 XOR a, both seeds marginally fair.
for a in bits:
    law1={y:sum(F(1,2) for e in bits if e==y) for y in bits}
    law2={y:sum(F(1,2) for e in bits if (e^a)==y) for y in bits}
    assert law1==law2
allowed={a:{(e,f) for e,f in product(bits,repeat=2) if e==(f^a)} for a in bits}
assert not (allowed[0]&allowed[1])
# Local action-aware reencoding sends common fair U to e2=U XOR a.
for a in bits:
    for u in bits:
        assert u==((u^a)^a)
    assert {u^a for u in bits}==set(bits)
# If recoding cannot see a, no deterministic common-source atom works for both.
assert all(any(u!=(f^a) for a in bits) for u,f in product(bits,repeat=2))
# Locality is substantial: PR-box relation x XOR y = a AND b has no
# deterministic response atom x=f(a), y=g(b), hence no positive shared mixture.
functions=list(product(bits,repeat=2))
pr_atoms=[(f,g) for f,g in product(functions,repeat=2)
          if all((f[a]^g[b])==(a&b) for a,b in product(bits,repeat=2))]
assert not pr_atoms
# All four requested pair laws are positive and each local marginal fair.
for a,b in product(bits,repeat=2):
    pair={(x,y):F(int((x^y)==(a&b)),2) for x,y in product(bits,repeat=2)}
    assert sum(pair.values())==1
    assert all(sum(pair[x,y] for y in bits)==F(1,2) for x in bits)
    assert all(sum(pair[x,y] for x in bits)==F(1,2) for y in bits)
# One bit of licensed communication a to second party implements same relation.
for a,b,u in product(bits,repeat=3):
    assert (u^(u^(a&b)))==(a&b)
print(json.dumps({'status':'PASS','equal_observable_kernels':True,
 'fixed_seed_joint_support_empty':True,'action_aware_recoding_repairs':True,
 'local_pr_response_atoms':len(pr_atoms),'one_bit_communication_repairs':True},indent=2))

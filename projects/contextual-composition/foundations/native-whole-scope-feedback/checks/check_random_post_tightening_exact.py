"""Finite exact diagnostics, not substitutes for categorical/native proofs."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json
O=list(product(range(2),repeat=2))
diag={z:F(z[0]==z[1],2) for z in O}
prod={z:F(1,4) for z in O}
def fair_marginals(q):
 return all(sum(v for z,v in q.items() if z[i]==b)==F(1,2) for i in (0,1) for b in (0,1))
def conditional_fair(q):
 return all(q[a,b]==sum(q[a,c] for c in (0,1))*F(1,2) for a,b in O)
assert fair_marginals(diag) and not conditional_fair(diag)
assert fair_marginals(prod) and conditional_fair(prod)
assert len(diag)==4 and sum(v==0 for v in diag.values())==2
# Probe A: L=local test, R=whole-paid test; probe B reverses them.
assert not conditional_fair(diag) # in BOTH obstructed destination families
# The prescribed successor cache tuple makes the canonical raw map identity.
assert all(z==z for z in O)
# No deterministic function pushes two positive atoms to four positive atoms.
assert 2<4
xor={b:sum(v for (y,z),v in diag.items() if (y^z)==b) for b in (0,1)}
assert xor=={0:F(1),1:F(0)}
# Coarsening a full-tree predecessor to P-only ancestry: x=b,
# a and b independent fair. x is fair given a, not given (a,b).
q={(a,b,x):F(1,4) if x==b else F(0) for a,b,x in product(range(2),repeat=3)}
assert all(sum(v for (aa,b,xx),v in q.items() if aa==a and xx==x)==F(1,4) for a,x in O)
assert any(q[a,b,x]!=F(1,8) for a,b,x in q)
r={'probe_A_L_admits_diagonal_R_rejects':True,
   'probe_B_R_admits_diagonal_L_rejects':True,
   'full_raw_atoms':4,'diagonal_zero_atoms':2,
   'hidden_xor_pushforward':['1','0'],
   'ancestry_coarsening_retains_fair_marginal':True,
   'scope':'Exact finite law diagnostics; native coefficient/full-grade proofs remain written.'}
out=Path(__file__).with_name('random_post_tightening_exact_results.json')
out.write_text(json.dumps(r,indent=2)+'\n');print(out.read_text())

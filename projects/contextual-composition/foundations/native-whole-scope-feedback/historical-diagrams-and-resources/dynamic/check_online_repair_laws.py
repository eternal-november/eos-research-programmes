"""Exact finite witness checks; not a mechanized proof of the recurrent theorem."""
from fractions import Fraction as F
from itertools import product
import json
old={0:F(1,2),1:F(1,2)}
# Native material identities B*T_j=-C_t with unit resource:
assert all((j==t)==(-t+j==0) for t,j in product(range(2),repeat=2))
# Constant local view has only constant response tables, neither raw-safe.
constant=[j for j in range(2) if all(j==t for t in range(2))]
assert constant==[]
# Disclosed local t has exactly one raw-safe table.
tables=[f for f in product(range(2),repeat=2) if all(f[t]==t for t in range(2))]
assert tables==[(0,1)]
q={(t,j):old[t]*F(int(j==t)) for t,j in product(range(2),repeat=2)}
assert all(sum(q[t,j] for j in range(2))==old[t] for t in range(2))
assert all(sum(q[t,j] for t in range(2))==F(1,2) for j in range(2))
# Renormalizing to a repair with constant j=0 discards half the old law.
accepted=sum(old[t] for t in old if t==0)
assert accepted==F(1,2)
renormalized={t:old[t]/accepted if t==0 else F(0) for t in old}
assert renormalized!=old
# If j=t is mislabeled as selection of a whole law with fair incoming margin,
# calibration fails on each selected label.
for label in range(2):
    posterior={t:q[t,label]/F(1,2) for t in old}
    assert posterior!=old
# Fresh independent fair repairs satisfy two fair marginals but not equality.
independent={(a,b):F(1,4) for a,b in product(range(2),repeat=2)}
assert sum(p for (a,b),p in independent.items() if a==b)==F(1,2)
shared={(a,b):F(1,2) if a==b else F(0) for a,b in product(range(2),repeat=2)}
assert sum(p for (a,b),p in shared.items() if a==b)==1
# A missing zero-raw branch remains fatal even if positive-law feasibility holds.
raw_with_zero={0:(0,2),1:(1,)}
supplied_matrix_maps={(0,0),(1,1)}
zero_extended_law={(0,0):F(1,2),(0,2):F(0),(1,1):F(1,2)}
assert sum(zero_extended_law.values())==1
assert all(key in supplied_matrix_maps for key,mass in zero_extended_law.items() if mass>0)
missing=[(t,j) for t,js in raw_with_zero.items() for j in js if (t,j) not in supplied_matrix_maps]
assert missing==[(0,2)]
assert zero_extended_law[missing[0]]==0
print(json.dumps({'status':'PASS','constant_view_raw_safe_tables':0,'disclosed_view_raw_safe_tables':1,'old_marginal_preserved':True,'fair_repair_marginal':True,'conditioning_retained_mass':'1/2','mislabelled_selection_calibration':'FAIL as expected','independent_cross_repair_equality':'1/2','shared_cross_repair_equality':'1','missing_zero_raw_alternative':'rejected despite zero probability','scope':'exact finite rational discriminator checks'},indent=2))

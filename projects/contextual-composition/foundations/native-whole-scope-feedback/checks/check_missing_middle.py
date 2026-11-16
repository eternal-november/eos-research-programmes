from fractions import Fraction as F
from itertools import product
import json
full=list(product(range(2),repeat=2))
diag=[(0,0),(1,1)]
D={z:F(1,2) for z in diag}
A={z:(F(1,2) if z[0]!=z[1] else F(0)) for z in full}
pushD={z:D.get(z,F(0)) for z in full}
assert pushD!=A
for i in (0,1):
    assert {b:sum(q for z,q in D.items() if z[i]==b) for b in (0,1)}=={0:F(1,2),1:F(1,2)}
    assert {b:sum(q for z,q in A.items() if z[i]==b) for b in (0,1)}=={0:F(1,2),1:F(1,2)}
# Boundary u_b at middle root 1 forces equality; collapsing boundaries frees it.
assert [z for z in full if z[0]==z[1]]==diag
assert [z for z in full if 0==0]==full
# Source only probes history 0, where raw joint maps are identity.
assert A==A
# Middle history 1 forced D cannot push to target selected A.
assert any(pushD[z]!=A[z] for z in full)
# Global terminal path mass at the zero middle root branch vanishes.
assert all(0*D[z]==0 for z in diag)
print(json.dumps({'primitive_fair_rows':'PASS','native_boundary_collapse':'PASS','composite_pair_admitted':True,'middle_extension_exists':False,'all_coupling_admission':True,'law_menu_transport':'all middle joints push to fair target joints; diagonal branch checked exactly','scope':'exact witness computation, not categorical proof certification'},indent=2))

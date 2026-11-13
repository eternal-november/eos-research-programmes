#!/usr/bin/env python3
"""Independent supplementary [2] x C2 finite-category law check."""
from itertools import product
from pathlib import Path
import json

arrows=tuple((a,b,e) for a in range(3) for b in range(a,3) for e in range(2))
def comp(f,g):
    assert f[1]==g[0]
    return (f[0],g[1],(f[2]+g[2])%2)

identities=0; pairs=0; triples=0
for f in arrows:
    assert comp((f[0],f[0],0),f)==f==comp(f,(f[1],f[1],0))
    identities+=1
for f,g in product(arrows,repeat=2):
    if f[1]!=g[0]:continue
    assert comp(f,g) in arrows;pairs+=1
for f,g,h in product(arrows,repeat=3):
    if f[1]!=g[0] or g[1]!=h[0]:continue
    assert comp(comp(f,g),h)==comp(f,comp(g,h));triples+=1
assert comp((1,1,1),(1,1,1))==(1,1,0)
result={'status':'PASS','arrows':len(arrows),'two_sided_identity_cases':identities,
        'composable_pair_closure_cases':pairs,'composable_associativity_triples':triples,
        'nonidentity_loop_square_is_identity':True}
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))

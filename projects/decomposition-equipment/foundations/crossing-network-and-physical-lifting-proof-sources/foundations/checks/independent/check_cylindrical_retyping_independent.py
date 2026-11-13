#!/usr/bin/env python3
from itertools import product,permutations
from pathlib import Path
import json
perms=((0,1),(1,0));triples=list(product(range(2),repeat=3)) # r,t,ell
count=square_count=cylinder_count=0
for choices in product(perms,repeat=8):
    eta=dict(zip(triples,choices))
    # Build actual incidence edges V'=(r,t,cprime,ell) -- W'=(bprime,ell,t).
    stars={}
    for r,t,c,ell in product(range(2),repeat=4):
        b=eta[r,t,ell][c]
        stars.setdefault((b,ell,t),[]).append((r,t,c,ell))
    square=True;descs={0:set(),1:set()}
    for (b,ell,t),vs in stars.items():
        # Right span has exactly one witness per(cprime,ell), so each rectangular component must have a fixed cprime and all R labels.
        if len({v[2] for v in vs})!=1 or {v[0] for v in vs}!={0,1}:
            square=False;break
        c=vs[0][2]
        phi=tuple((r,t,c) for r in range(2))
        descs[ell].add((b,c,phi))
    cylinder=square and descs[0]==descs[1]
    square_expected=all(eta[0,t,ell]==eta[1,t,ell] for t,ell in product(range(2),repeat=2))
    cylinder_expected=all(eta[r,t,ell]==eta[0,t,0] for r,t,ell in triples)
    assert square==square_expected
    assert cylinder==cylinder_expected
    count+=1;square_count+=square;cylinder_count+=cylinder
assert (count,square_count,cylinder_count)==(256,16,4)
out={'status':'PASS','whole_matching_families':count,'ordinary_square_fillers_exist':square_count,'genuine_cylindrical_fillers_exist':cylinder_count,'scope':'Original R2,T2,P4; two lower interface values, one Q witness and one S witness per level; two-element fibres for both B/C retyping maps. All 8 independent S2-valued eta choices. Actual incidence-star rectangle and cylinder descriptors independently compared with independence conditions.'}
Path(__file__).with_name('Cylindrical_Retyping_Independent_Checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))

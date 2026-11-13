#!/usr/bin/env python3
"""Nonauthor adversarial API probes. Imports author API deliberately; NOT the
independent finite oracle. The imported source is hashed in the output."""
import hashlib
import json
from pathlib import Path
import runpy

root=Path(__file__).resolve().parents[1]
source=root/'finite/check_c2_model.py'
a=runpy.run_path(str(source))
Interface,Relation,Profile,Cell,InterfaceMap=(a[k] for k in ('Interface','Relation','Profile','Cell','InterfaceMap'))
rejections=[]
def reject(label,fn):
    try: fn()
    except ValueError as exc:
        rejections.append({'case':label,'exception':str(exc)})
    else: raise AssertionError('unguarded: '+label)

B=Interface('B',2); BP=Interface('Bprime',2); wrong=Interface('WrongLabelSameSize',2)
r=Relation(B,B,15); f=InterfaceMap(BP,B,(0,0)); idB=InterfaceMap(B,B,(0,1))
positive=0
for n in range(9):
    c=Cell(r,Profile(B,B,(r,)*n))
    pulled=a['restrict_cell'](c,(f,)*(n+1))
    assert len(pulled.profile.edges)==n
    assert pulled.whole==Relation(BP,BP,15)
    assert a['restrict_cell'](c,(idB,)*(n+1))==c
    reject(f'arity{n}:too-many-boundaries',lambda c=c,n=n:a['restrict_cell'](c,(f,)*(n+2)))
    reject(f'arity{n}:too-few-boundaries',lambda c=c,n=n:a['restrict_cell'](c,(f,)*n))
    bad=InterfaceMap(BP,wrong,(0,0))
    reject(f'arity{n}:wrong-target-label',lambda c=c,n=n:a['restrict_cell'](c,(bad,)+(f,)*n))
    null=Cell(r,Profile(B,B,()))
    children=(null,)*n
    family={B:f}
    lhs=a['restrict_family'](a['substitute'](c,children),family)
    rhs=a['substitute'](a['restrict_family'](c,family),tuple(a['restrict_family'](q,family) for q in children))
    assert lhs==rhs and lhs.profile.edges==()
    positive+=1
# Distinct maps may occur at separately chosen loop endpoints in a nonnullary
# profile, but a nullary has ONE vertex/map; gluing is not silently forgotten.
c=Cell(r,Profile(B,B,(r,)))
g=InterfaceMap(BP,B,(1,1))
assert len(a['restrict_cell'](c,(f,g)).profile.edges)==1
reject('nullary-two-independent-maps',lambda:a['restrict_cell'](Cell(r,Profile(B,B,())),(f,g)))
report={'status':'PASS','source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
        'positive_arities':list(range(9)),'global_nullary_substitution_comparisons':positive,
        'rejections':rejections,
        'limit':'Finite API guard probes, not an all-arity proof. General incidence-compatible forest law is P; no local-forest restriction API is invented.'}
print(json.dumps(report,indent=2,sort_keys=True))

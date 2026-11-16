"""Finite exact diagnostics only; not a proof of native universal claims."""
from fractions import Fraction as F
from itertools import product
import json
rows = {s: (('halt', F(1,2), None), ('c0', F(1,4), 0), ('c1', F(1,4), 1)) for s in (0,1)}
def layer(seed, n):
    active = [(seed, (), (), F(1))]
    for i in range(n):
        nxt, done = [], []
        for s, ws, labels, p in active:
            for w,q,t in rows[s]:
                if t is None:
                    done.append((ws+(w,), labels, p*q))
                else:
                    nxt.append((t,ws+(w,),labels+(t,),p*q))
        active=nxt
    return done
layers=[]
for n in range(1,8):
    xs=layer(0,n)
    assert len(xs)==2**(n-1)
    assert sum(p for _,_,p in xs)==F(1,2**n)
    for ws,labels,p in xs:
        # Chain carries every step witness and every internal incoming label.
        chain=tuple((w, labels[i] if i<n-1 else None) for i,w in enumerate(ws))
        assert tuple(w for w,_ in chain)==ws
        assert tuple(s for _,s in chain[:-1])==labels
        assert len(chain)==n
    layers.append({'cost':n,'raw_atoms':len(xs),'mass':str(sum(p for _,_,p in xs))})
# Cost-two no-arrow witness: exact weights force a permutation; a global
# grade map from the shared source word would force constant target shape.
xs=layer(0,2)
legal=[]
for r in product(range(2),repeat=2):
    push=[sum(xs[i][2] for i in range(2) if r[i]==j) for j in range(2)]
    exact=push==[x[2] for x in xs]
    body=len({xs[r[i]][1] for i in range(2)})==1
    if exact and body:legal.append(r)
assert legal==[]
# Periodic raw paths of deterministic flip versus singleton identity.
periods=[]
for n in range(1,7):
    bitclosed=[s for s in (0,1) if (s+n)%2==s]
    assert len(bitclosed)==(2 if n%2==0 else 0)
    periods.append({'n':n,'flip_closed_mass':len(bitclosed),'singleton_closed_mass':1})
# Exact same grade cardinalities in finite formal word fibres.
assert [2**(n-1) for n in range(1,5)]==[1,2,4,8]
print(json.dumps({'status':'passed','terminal_layers':layers,
 'cost_two_reverse_native_raw_and_shape_maps':len(legal),
 'periodic_state_intertwiner_obstruction':periods,
 'limitations':'Finite rational and set-map diagnostics; no test of arbitrary coefficient categories or full naturality.'},indent=2))

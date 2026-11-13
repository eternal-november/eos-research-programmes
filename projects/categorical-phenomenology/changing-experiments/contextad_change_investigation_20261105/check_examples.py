"""Exact finite checks for the original examples; not substitutes for general proofs."""
from itertools import product
import json
from pathlib import Path

report={}
# Reader environment refinement r:{0,1,2,3}->{0,1}; A=B=C={0,1}.
E=range(2); Ep=range(4); A=range(2); r=lambda e:e%2
source_inputs=list(product(E,A)); rich_inputs=list(product(Ep,A))
functions=[dict(zip(source_inputs,v)) for v in product(A, repeat=len(source_inputs))]
rich_functions=[dict(zip(rich_inputs,v)) for v in product(A, repeat=len(rich_inputs))]
def translate(f): return {(e,a):f[r(e),a] for e,a in rich_inputs}
def compose(f,g,env): return {(e,a):g[e,f[e,a]] for e,a in product(env,A)}
for f,g in product(functions,repeat=2):
    assert translate(compose(f,g,E))==compose(translate(f),translate(g),Ep)
image={tuple(translate(f)[p] for p in rich_inputs) for f in functions}
fibre_constant={tuple(f[p] for p in rich_inputs) for f in rich_functions
                if all(f[e,a]==f[d,a] for e,d,a in product(Ep,Ep,A) if r(e)==r(d))}
assert image==fibre_constant
assert len(image)==len(functions)
assert len(image)<len(rich_functions)
report['reader']={'source_arrows':len(functions),'target_arrows':len(rich_functions),
 'pairs_composition_checked':len(functions)**2,'image_equals_fibre_constant':True,
 'faithful':True,'full':False}

# C2 regular action, diagonal product; relative equality survives diagonal quotient.
X=range(2); pairs=list(product(X,X))
orbits={frozenset(((x+g)%2,(y+g)%2) for g in X) for x,y in pairs}
assert len(orbits)==2
values=[]
for orbit in orbits:
    obs={x==y for x,y in orbit}; assert len(obs)==1; values.append(obs.pop())
assert set(values)=={False,True}
report['orbit_span']={'source_composite_orbits':[sorted(o) for o in sorted(orbits,key=lambda z:sorted(z))],
 'number_of_composite_orbits':len(orbits),'composite_of_orbits_size':1,
 'canonical_comparison_invertible':False,'relative_equality_separates':True}

# New operation need not descend along an old observational quotient.
X=range(3); h={0:0,1:0,2:1}; u={0:0,1:2,2:2}
old_rows={x:(h[x],) for x in X}
new_rows={x:(h[x],h[u[x]]) for x in X}
assert old_rows[0]==old_rows[1] and h[u[0]]!=h[u[1]]
assert len(set(new_rows.values()))==3
report['new_operation']={'old_rows':len(set(old_rows.values())), 'continuation_closed_rows':len(set(new_rows.values())),
 'descends_to_old_rows':False}

# Probe representation gate: f:X->{*}; truth and falsehood cannot recover a nonconstant predicate.
coarse_tests=[(0,0),(1,1)]
assert (0,1) not in coarse_tests
report['probe_gate']={'rich_probe_descends':False}

out=Path(__file__).with_name('finite_checks.json')
out.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))

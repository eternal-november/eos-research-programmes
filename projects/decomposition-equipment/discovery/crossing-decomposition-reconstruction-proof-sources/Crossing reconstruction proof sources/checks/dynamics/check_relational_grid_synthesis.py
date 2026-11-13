from itertools import product
from pathlib import Path
import json
points=tuple(product(range(2),repeat=2))
rels=[frozenset(p for p,b in zip(points,bits) if b) for bits in product((0,1),repeat=4)]
def comp(R,S):return frozenset((a,c) for a,b in R for b2,c in S if b==b2)
composition={(R,S):comp(R,S) for R in rels for S in rels}
count=feasible=nonunique=0
for R,S,P,N in product(rels,repeat=4):
    Umax=frozenset((y,z) for y,z in points if all((a,z) in P for a,y2 in R if y==y2) and all((y,d) in N for z2,d in S if z==z2))
    solutions=[U for U in rels if composition[R,U]==P and composition[U,S]==N]
    maximum_works=composition[R,Umax]==P and composition[Umax,S]==N
    assert bool(solutions)==maximum_works
    assert all(U<=Umax for U in solutions)
    if solutions:
        feasible+=1
        assert Umax in solutions
        nonunique+=len(solutions)>1
    count+=1
U1={(0,1)};U2={(1,2)}
assert not comp(U1,U1) and not comp(U2,U2) and comp(U1|U2,U1|U2)=={(0,2)}
result={'two_sided_two_by_two_specs_checked':count,'feasible_specs':feasible,'specs_with_multiple_solution_relations':nonunique,'residual_vs_exhaustive_search':'PASS','repeated_unknown_counterexample':'PASS','scope':'All R,S,P,N binary relations on two-element interfaces and all candidate U; no finite-span witness or general-feedback completeness claim.'}
Path(__file__).with_name('check_relational_grid_synthesis_results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))

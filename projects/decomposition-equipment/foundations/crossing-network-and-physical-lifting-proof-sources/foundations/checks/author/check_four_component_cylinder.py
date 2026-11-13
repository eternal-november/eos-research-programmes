from itertools import product,permutations
from pathlib import Path
import json
B=(0,1)
pairs=tuple(product(B,repeat=2))
# Source labels (e,v); target labels (e,u), for each actual l.
for l in B:
    theta={ (e,v):(e,v^(e*l)) for e,v in pairs }
    assert len(set(theta.values()))==4
    for e,u in pairs:
        p=(e,u^(e*l))
        assert theta[p]==(e,u)
# Any alpha:R(2) x T(2) -> P(4), and beta_l:T(2)->N_l(2).
# This enumerates all bijections, including those not preserving e.
perms2=list(permutations(B))
counts={0:0,1:0}
tested=0
for image in permutations(pairs):
    alpha=dict(zip(pairs,image))
    for beta0,beta1 in product(perms2,repeat=2):
        tested+=1
        beta={0:beta0,1:beta1}
        for twist in B:
            ok=True
            for e,t,l in product(B,repeat=3):
                pe,pv=alpha[e,t]
                actual=(pe,pv^(twist*pe*l))
                expected=(e,beta[l][t])
                if actual!=expected:ok=False
            counts[twist]+=ok
assert tested==96
assert counts=={0:2,1:0}
# Every labelled R-tiling at l=0 differs from every one at l=1.
tiles={l:{tuple((e,u^(e*l)) for e in B) for u in B} for l in B}
assert tiles[0]!=tiles[1]
# Full external typing and behavior for all actual a,k,e,v.
for a,k,e,v in product(B,repeat=4):
    b=1-a;c=a;l=1-k;d=c^l
    assert d==(1-b)^l
    u=v^(e*l)
    assert (u^(e*l))==v
# Independent actual-Q-witness obstruction with theta_Q(e,v,j)=(e,v XOR j).
q_fixture_solutions=0
for image in permutations(pairs):
    alpha=dict(zip(pairs,image))
    for beta0,beta1 in product(perms2,repeat=2):
        beta={0:beta0,1:beta1}
        ok=True
        for e,t,l,j in product(B,repeat=4):
            pe,pv=alpha[e,t]
            if (pe,pv^j)!=(e,beta[l][t]):ok=False
        q_fixture_solutions+=ok
assert q_fixture_solutions==0
q_tiles={j:{tuple((e,u^j) for e in B) for u in B} for j in B}
assert q_tiles[0]==q_tiles[1]
assert all(tuple((e,u) for e in B)!=tuple((e,u^1) for e in B) for u in B)
for e,u,j in product(B,repeat=3):
    pe,pv=e,u^j
    assert (pe,pv^j)==(e,u)
result={'actual_parallel_witness_fixture_solutions':q_fixture_solutions,'parallel_witness_tile_sets_agree':True,'fixed_middle_descriptors_depend_on_parallel_witness':True,'bijection_assignments_per_state_fibre':tested,'untwisted_labelled_solutions_per_state_fibre':counts[0],'twisted_labelled_solutions_per_state_fibre':counts[1],'ordinary_square_filler':'PASS','external_endpoint_typing':'PASS','descriptor_set_mismatch':'PASS','scope':'All alpha bijections of four events and both beta bijections of two events, for a representative state fibre; the general no-go proof allows arbitrary finite middle-event names.'}
Path(__file__).with_name('check_four_component_cylinder_results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))

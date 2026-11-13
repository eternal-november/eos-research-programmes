"""Author finite check of coherent internal B/C retyping, using explicit lifted matching arrays."""
import itertools,json
from pathlib import Path
# Original T singleton; R2, Q_l2, S_l2, L2. Each old whole tuple
# (l,r,q,s) gets one of two bijections between two-element B/C lifts.
old=list(itertools.product(range(2),repeat=4))
# A cylindrical middle T' has two points and must give one fixed
# bijection C'->B' independent of all four original tuple indices.
explicit_cylinders={tuple(c^flip for _ in old for c in range(2)) for flip in range(2)}
# Ordinary square fillers can choose one bijection at each parallel l.
explicit_squares={tuple(c^flips[l] for l,r,q,s in old for c in range(2)) for flips in itertools.product(range(2),repeat=2)}
count=0;sc=0;cc=0
for choices in itertools.product(range(2),repeat=len(old)):
    theta=tuple(c^choices[i] for i in range(len(old)) for c in range(2))
    cylinder=len(set(choices))<=1
    square=all(len({choices[i] for i,t in enumerate(old) if t[0]==l})<=1 for l in range(2))
    assert cylinder==(theta in explicit_cylinders)
    assert square==(theta in explicit_squares)
    count+=1;sc+=square;cc+=cylinder
out={'status':'PASS','domain':'One original middle witness, R2,Q_l2,S_l2,L2; both retyping fibres size2. All2^16 independent per-old-tuple fibre bijections, compared to explicitly generated cylindrical and square alignments.','lifted_matchings':count,'ordinary_square_lifts':sc,'cylindrical_lifts':cc}
Path(__file__).with_name('check_internal_cylinder_retyping_results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))

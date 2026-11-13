"""Finite regression tests for the framing review, not substitutes for proofs."""
from itertools import product

def decorations(labels, fibres):
    return list(product(*(fibres[b] for b in labels)))

count=0
for nx in range(4):
    X=range(nx)
    for n0 in range(3):
        for n1 in range(3):
            fibres={0:tuple((0,i) for i in range(n0)),1:tuple((1,i) for i in range(n1))}
            for length in range(4):
                for labels in product((0,1),repeat=length):
                    # Each explicit q tag carries x even if length=0.
                    right={(x,t) for x in X for t in decorations(labels,fibres)}
                    left={(x,tuple((x,e) for e in t)) for x,t in right}
                    forward=lambda z:(z[0],tuple(e for _,e in z[1]))
                    backward=lambda z:(z[0],tuple((z[0],e) for e in z[1]))
                    assert {forward(z) for z in left}==right
                    assert all(backward(forward(z))==z for z in left)
                    assert all(forward(backward(z))==z for z in right)
                    count+=1
X=range(2)
frame_composite={(tag,x,y) for tag in ('s','q') for x in X for y in X}
composite_frames={('s',x,y) for x in X for y in X}|{('q',x,x) for x in X}
assert len(frame_composite)==8 and len(composite_frames)==6
assert frame_composite-composite_frames=={('q',0,1),('q',1,0)}
print(f'PASS: {count} uniform-decoration fixtures, including empty frame and nullary arity; retained PB-frame counterexample 6 != 8.')

assert len({(0,'q')}) != len({(0,'q'),(1,'q')})
print('PASS: uniform receipt parameter-map pseudonaturality obstruction 1 != 2.')

# Exact finite witness for the universal two-inclusions no-go proof.
# A slice isomorphism between singleton grades must carry their unique tag
# to the unique tag and preserve its label. No enumeration of candidate
# actions is involved: the proof forces BOTH target singleton isomorphisms.
def singleton_slice_isomorphism_exists(left_label, right_label):
    return left_label == right_label
inclusions = {0: lambda _: 0, 1: lambda _: 1}
post_labels = tuple(inclusions[i]('*') for i in (0, 1))
assert post_labels == (0, 1)
assert not singleton_slice_isomorphism_exists(*post_labels)
# General cartesian-polynomial unit has a unary addressed label.
eta = lambda b: ('unit_shape', (b,))
assert not singleton_slice_isomorphism_exists(eta(0), eta(1))
print('PASS: two-inclusions global-grade no-go witness: singleton labels 0 and 1 are not isomorphic in Set/2; unary eta labels remain distinct.')

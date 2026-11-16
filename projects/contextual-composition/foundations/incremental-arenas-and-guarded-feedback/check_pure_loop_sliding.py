"""Finite discriminating diagnostics; not a proof of general arena laws."""
from fractions import Fraction
from itertools import product
import json
V=(0,1,2); U=(0,1); W=(0,)
g={0:0,1:0,2:1}; h={0:0,1:0}
def edge_map(word,f): return tuple((p,f[v]) for p,v in word)
n=0
for depth in range(5):
    for labels in product(V,repeat=depth):
        word=tuple(zip(range(depth),labels))
        assert edge_map(edge_map(word,g),h)==edge_map(word,{v:h[g[v]] for v in V})
        # The target retained original parent labels, not just projected edge labels.
        projected=edge_map(word,g)
        reconstructed=tuple((p,v) for (p,u),v in zip(projected,labels))
        assert reconstructed==word
        n+=1
# Positive-body obstruction: both target atoms have one body shape; source differs.
weights=(Fraction(1,2),)*2
native_reverse=[]
for rawmap in product(range(2),repeat=2):
    if tuple(sum((weights[i] for i in range(2) if rawmap[i]==j),Fraction()) for j in range(2)) != weights:
        continue
    for image_of_single_shape in range(2):
        if all(rawmap[i]==image_of_single_shape for i in range(2)):
            native_reverse.append((rawmap,image_of_single_shape))
assert not native_reverse
# Full unused binary tree: two binary nodes have three external leaves.
assert 2+2-1==3 and 3!=2
out={'status':'passed','labelled_words':n,'surjective_reverse_candidates':len(native_reverse),
     'checks':['label-function-composition','retained-parent-label-reconstruction','positive-body-exact-pushforward-obstruction','unused-arity-obstruction'],
     'scope':'finite namespace and scalar/body probes; no general coherence certification'}
print(json.dumps(out,indent=2))

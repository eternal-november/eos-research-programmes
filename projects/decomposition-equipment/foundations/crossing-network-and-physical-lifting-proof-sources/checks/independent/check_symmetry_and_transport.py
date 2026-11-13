from itertools import permutations,product
from check_reconstruction_independent import partitions,static,kernel
import json
# Two invisible local two-event carriers: exactly two matchings, group 4 acts
# transitively and each stabilizer has two elements.
ks=[k for k in partitions(4) if static(k,[0]*4,[(0,[0,1]),(0,[2,3])],[])]
group=[a+tuple(v+2 for v in b) for a in permutations(range(2)) for b in permutations(range(2))]
def act(k,g):
 inv=[g.index(i) for i in range(4)]
 return kernel(tuple(k[inv[i]] for i in range(4)))
assert len(ks)==2
assert {act(ks[0],g) for g in group}==set(ks)
assert all(sum(act(k,g)==k for g in group)==2 for k in ks)
# Noninjective global base change duplicates each matching independently.
# Thus four primed solutions versus two transported old solutions.
newfibres=[(0,[0,1]),(1,[2,3]),(0,[4,5]),(1,[6,7])]
newtypes=[0,0,1,1,0,0,1,1]
newks=[k for k in partitions(8) if static(k,newtypes,newfibres,[])]
assert len(newks)==4
# Four original elements repeated at each base lift; block pairs use lift tag.
oldindex=[0,1,0,1,2,3,2,3]
transported={kernel(tuple((newtypes[j],k[oldindex[j]]) for j in range(8))) for k in ks}
assert len(transported)==2 and transported<=set(newks)
print(json.dumps({'symmetry':'PASS: transitive matching action, stabilizer S2','transport':'PASS: four lifted solutions, only two descend','scope':'explicit finite fixtures'},indent=2))

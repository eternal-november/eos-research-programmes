"""Extend the geometry premise, not the names, to four static contexts."""
from decimal import Decimal as D
from pathlib import Path
import json,sys
import ride
sys.argv[1], saved_geom = str(Path(sys.argv[1]).parent), sys.argv[1]
import lower
sys.argv[1] = saved_geom
from positive_discovery import slab_hit
rays=json.loads(Path(sys.argv[4]).read_text())
beams=[(rays[x]['observer'],rays[x]['marker']) for x in 'AB']
def identity(beam):
    found=[s for s in ride.closures.values() if slab_hit(*beam,*s,D(0))]
    assert len(found)==1
    return found[0]
gates=list(map(identity,beams))
assert gates[0]!=gates[1]
A,lo,vox=lower.bulk();_,E=lower.adjacent(A,lo)
assert vox==138777
matched=[]
for key in lower.K:
    lo2,hi2=E[key]
    found=[i for i,s in enumerate(gates)
           if all(a*2<=int(x) and int(y)<=b*2 for a,b,x,y in zip(*s,lo2,hi2))]
    assert len(found)==1
    matched.extend(found)
assert sorted(matched)==list(range(2))
assert lower.reach(set(E),lower.K) is None
words=[]
for mask in range(4):
    closed=[s for n,s in enumerate(gates) if mask&(1<<n)]
    words.append(['c' if any(slab_hit(*beam,*k,D(0)) for k in closed) else 'o' for beam in beams])
assert words==[["o","o"],["c","o"],["o","c"],["c","c"]]
with Path(sys.argv[5]).open('a') as f:
    for row in words:print(*row,file=f)
print(json.dumps(dict(contexts=words,native_center_cubes=vox,both_closed_reachable=False),sort_keys=True))

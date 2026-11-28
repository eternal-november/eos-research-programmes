"""The physical comparison: source beam, closed slab, and licensed path.

The input identifiers for beam slots and certified paths are deliberately
not identified. Match exact beam/slab intersections and prove which path
can pass each gate, across both label permutations.
"""
from pathlib import Path
from itertools import pairwise, permutations
from decimal import Decimal as D
import json
import sys
import ride
from positive_discovery import slab_hit

paths=json.loads(Path(sys.argv[3]).read_text())
rays=json.loads(Path(sys.argv[4]).read_text())
matrix=[]
for tag in "AB":
    beam=rays[tag]
    u,v=beam["observer"],beam["marker"]
    matching=[s for s in ride.closures.values() if slab_hit(u,v,*s,D(0))]
    assert len(matching)==1
    L,H=matching[0]
    assert sum((a-b)**2 for a,b in zip(u,v))==36
    assert beam["port"] in [str(coord) for coord in L]
    hits=[]
    for label in "AB":
        p=paths[label]["polyline"]
        nominal=[i for i,(a,b) in enumerate(pairwise(p)) if slab_hit(a,b,L,H,D(0))]
        padded=[i for i,(a,b) in enumerate(pairwise(p)) if slab_hit(a,b,L,H,D(".302"))]
        assert bool(nominal)==bool(padded)
        hits.append(nominal)
    assert sum(map(bool,hits))==1
    matrix.append(hits)
assert all(sum(bool(row[j]) for row in matrix)==1 for j in range(2))
gate_route=[next(i for i,x in enumerate(row) if x) for row in matrix]
for pi in permutations(range(2)):
    inv=[pi.index(x) for x in gate_route]
    for closed in range(2):
        assert not matrix[closed][pi[inv[1-closed]]]
        assert matrix[1-closed][pi[inv[1-closed]]]
print(json.dumps(dict(hit_segments=matrix, route_requiring_gate=gate_route),sort_keys=True))
with Path(sys.argv[5]).open("a") as f:
    print(*gate_route,file=f)

from fractions import Fraction as F
from pathlib import Path
from math import isqrt
import json, sys

paths=json.loads(Path(sys.argv[1]).read_text())
proof=[json.loads(x) for x in Path(sys.argv[2]).read_text().splitlines()]
lower=F(proof[0]["local_lower"],proof[0]["dual_denominator"])
H=(275,-175,2)
G=(350,-300,13)
V=F(1);a=F(5);delay=F(1)
seg={}
for k,p in paths.items():
    q=p["polyline"]
    assert (tuple(q[0]),tuple(q[-1]))==(H,G)
    lens=[sum((x-y)**2 for x,y in zip(u,v)) for u,v in zip(q,q[1:])]
    for i in lens:
        assert i>=(V*V/a)**2
    def ceil_um(l):
        x=isqrt(l*10**12)
        return x+int(x*x!=l*10**12)
    total=F(sum(ceil_um(x) for x in lens)*2,10**6)
    assert p["up_um"]==total*10**6
    L=2*len(lens)
    seg[k]=(L,total,total/V+L*V/a+delay)
# Each outbound/return leg must cover Euclidean start-target distance
# and hence is long enough to reach the speed cap for the lower bound.
assert sum((x-y)**2 for x,y in zip(H,G))>(V*V/a)**2
late=lower/V+2*V/a
early=max(v[-1] for v in seg.values())
assert early<late
n=seg["B"][0]
a_threshold=F((n-2)*V*V,lower-seg["B"][1]-V*delay)
assert a_threshold<a
print(json.dumps(dict(V=str(V),accel=str(a),deadline_open_interval=[str(early),str(late)],
                      early_by_case={k:str(v[-1]) for k,v in seg.items()},
                      gap=str(late-early),sufficient_crit_accel=str(a_threshold)),sort_keys=True))

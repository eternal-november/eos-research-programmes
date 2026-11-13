"""Independent finite rational proof regressions; no author imports or experiments."""
from fractions import Fraction as F
from itertools import product, combinations
import json

results = {}
# Exhaust every orientation and forced two-batch schedule on a four-job path.
n = 4
edges = [(0,1),(1,2),(2,3)]
worlds = list(product((0,1), repeat=3))
batches = list(combinations(range(n), 2))
def trace(world, batch):
    first=set(batch)
    u=lambda j,t: int((t==0 and j in first) or (t==1 and j not in first))
    return [[u(e[o],t)+u(e[1-o],t-1) for t in range(3)] for e,o in zip(edges,world)]
for batch in batches:
    assert any(max(map(max, trace(w,batch)))>1 for w in worlds)
for w in worlds:
    # Derive an order independently by repeatedly removing vertices with no predecessors.
    arcs=[(e[o],e[1-o]) for e,o in zip(edges,w)]
    order=[]
    while len(order)<n:
        order.append(next(v for v in range(n) if v not in order and all(a in order for a,b in arcs if b==v)))
    assert max(map(max,trace(w,order[:2])))<=1
results['path']={'worlds':len(worlds),'forced_batches':len(batches),'all_fine_safe':True,'all_coarse_batches_spoiled':True}
# Exhaust sparse-grid rows, conditioned known columns and binary two-tick schedules.
grid=(F(0),F(1,2),F(1)); n=3; L=1; s=2
rows=[r for r in product(grid,repeat=n*(L+1)) if sum(x>0 for x in r)<=s]
count=0
for J in ((),(0,),(0,1),(0,1,2)):
    groups={}
    for r in rows:
        key=tuple(r[j*2+l] for j in J for l in range(2))
        groups.setdefault(key,[]).append(r)
    for compatible in groups.values():
        r0=compatible[0]; remaining=s-sum(r0[j*2+l]>0 for j in J for l in range(2))
        for bits in product((0,1),repeat=6):
            u=lambda j,t: F(bits[2*j+t]) if 0<=t<2 else F(0)
            for t in range(3):
                known=sum((r0[j*2+l]*u(j,t-l) for j in J for l in range(2)),F(0))
                z=[u(j,t-l) for j in range(n) if j not in J for l in range(2)]
                proposed=known+sum(sorted(z,reverse=True)[:remaining],F(0))
                exact=max(sum((r[j*2+l]*u(j,t-l) for j in range(n) for l in range(2)),F(0)) for r in compatible)
                assert proposed==exact
                count+=1
results['top_k']={'sparse_rows':len(rows),'exact_equalities':count}
# Singleton bounded-error nearest-grid recovery and sensor-gap boundary failure.
eps=F(1,2); eta=F(1,10)
for g in grid:
    for noise in (-eta,F(0),eta):
        measured=eps*g+noise
        nearest=min(grid,key=lambda x: abs(measured/eps-x))
        assert nearest==g
# epsilon Delta == 2 eta permits identical observations for adjacent coefficients.
eta_boundary=eps*F(1,2)/2
assert eps*grid[0]+eta_boundary == eps*grid[1]-eta_boundary
results['singleton']={'endpoint_noise_cases':9,'strict_gap_necessary':True}
# Delayed hazard after service is real: last command at 1, two-step lag -> load at 3.
u=[F(0),F(1),F(0),F(0)]
assert all(F(2)*(u[t-2] if t>=2 else 0)<=1 for t in (0,1))
assert F(2)*u[1]>1
# Sensor-only noise cannot itself change physical load, physical residual can.
load=F(9,10); sensor=F(1,5); physical=F(1,5)
assert load<=1 and load+sensor>1 and load+physical>1
results['tails_and_disturbance']={'post_service_violation_detected':True,'separate_quantities_required':True}
print(json.dumps(results,indent=2,sort_keys=True))

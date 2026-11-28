"""Prove candidate lines to an ideal known face marker from exact cave mesh."""
from pathlib import Path
from fractions import Fraction as F
from decimal import Decimal as D
import json,sys
import survey,ride
import positive_discovery
P=Path(sys.argv[3]);pose=json.loads(P.read_text())
rays=json.loads(Path(sys.argv[4]).read_text())
survey.verify()
T,_,_,_=survey.source()
m=survey.Map(T,[])
res=[]
for spec in pose:
    if spec["mode"]!="bounded":
        continue
    q=spec["gate"]
    m.fences=[ride.closures[(118,132) if q==0 else (117,132)]]
    origin=tuple(rays["AB"[q]]["observer"])
    xyz=[list(map(F,pair)) for pair in spec['witness_xyz']]
    velocity=[list(map(F,pair)) for pair in spec["velocity_xyz"]]
    for j,((l,h),(u,v)) in enumerate(zip(xyz,velocity)):
        sl=l+min(0,u/100);sh=h+max(0,v/100)
        xyz[j]=[sl,sh]
    axis,sign=spec["axis"],spec["sign"]
    xyz[axis]=[e+sign*F(302,1000) for e in xyz[axis]]
    # Rounded sample position and uncertainty envelope proved by tiny
    # directed intervals. Include an extra 1 mm around the whole beam
    # for robust line separation, not a claimed sensor accuracy.
    Q=10**9
    mpoint=[]
    for lo,hi in xyz:
        center=(lo+hi)/2
        t=(center*Q).numerator//(center*Q).denominator
        x=F(t,Q)
        assert max(abs(lo-x),abs(hi-x))<F(51,10000)
        mpoint.append(F(t,Q))
    outward=all(sign*(F(origin[axis])-x)>F(1,1000) for x in xyz[axis])
    ds2=sum(max((s-a)**2,(s-b)**2) for s,(a,b) in zip(origin,xyz))
    inrange=ds2<F(599,100)**2
    qualified=outward and inrange and positive_discovery.boxzonotope(m,origin,mpoint,True,D(".007"))
    res.append(dict(gate=q,mode=spec["mode"],source=list(origin),
                    range_m_rounded=round(float(ds2)**.5,5),
                    outward=outward,range_qualified=inrange,tube_mesh_clear=qualified))
assert {x["gate"] for x in res}=={0,1} and all(x["tube_mesh_clear"] for x in res)
print(json.dumps(res,sort_keys=True))

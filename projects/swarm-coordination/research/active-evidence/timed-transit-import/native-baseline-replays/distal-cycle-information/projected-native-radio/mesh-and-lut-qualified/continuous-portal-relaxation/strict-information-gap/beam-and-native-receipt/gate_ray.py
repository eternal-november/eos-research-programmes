"""One model of locally earned gate evidence; no optical hardware assumption."""
import sys,json
from pathlib import Path
from math import isqrt
from decimal import Decimal as D
from fractions import Fraction
import survey,ride
from positive_discovery import boxzonotope,slab_hit
geom=Path(sys.argv[1])

def lower_scope(lookup,slabs):
    candidates=[]
    for L,H in slabs:
        # Exact lower bound in millimetres from closed authorized center
        # cubes outside all four sensing endpoint labels, to closed slab.
        l=[int(v*1000) for v in L];h=[int(v*1000) for v in H]
        least=None
        for p,who in lookup.items():
            if who in (115,118,117,119):continue
            ds=[max(0,a-x*1000-500,x*1000-500-b) for x,a,b in zip(p,l,h)]
            n=sum(d*d for d in ds)
            hit=(n,p,who)
            if least is None or hit<least:least=hit
        assert least is not None and least[0]>6000**2
        candidates.append([least[0],isqrt(least[0]),list(least[1]),least[2]])
    return candidates

def choose(m,rows,face,other,who,axis,nose):
    close=face[0][axis] if nose>0 else face[1][axis]
    marker=314 if axis==0 else -239
    cand=[]
    for p,v in rows.items():
        if v!=who:continue
        if not D(".8")<=nose*(close-p[axis])<=D("4.5"):continue
        if any(not face[0][i]+D(".3")<=p[i]<=face[1][i]-D(".3")
               for i in range(3) if i!=axis):continue
        q=tuple(marker if i==axis else p[i] for i in range(3))
        if abs(p[axis]-q[axis])>6:continue
        if q not in rows:continue
        # Aim near the physical location used in the previous radio trial.
        target=(302,-247,11) if axis==0 else (325,-225,26)
        cand.append((sum((a-b)**2 for a,b in zip(p,target)),p,q))
    for _,p,q in sorted(cand):
        m.fences=[face]
        if not boxzonotope(m,p,p,True):continue
        assert slab_hit(p,q,*face,D(0))
        m.fences=[other]
        if not boxzonotope(m,p,p,True) or not boxzonotope(m,q,q,True,D(".05")):continue
        if not boxzonotope(m,p,q,True,D(".02")):continue
        # Straight center ray intersects the closed slab. Open-world
        # beam is mesh-separated and reaches a positive authored marker.
        return dict(observer=p,marker=q,port=face[0][axis],poses_checked=len(cand),
                    tiles=[rows[p],rows[q]],length=abs(p[axis]-q[axis]))
    raise AssertionError("no qualified stage box")
def main():
    survey.verify()
    T,poses,typ,tt=survey.source()
    rows=ride.read_lut(set(poses))
    m=survey.Map(T,[])
    A=ride.closures[117,132];B=ride.closures[118,132]
    R=lower_scope(rows,(A,B))
    p=choose(m,rows,A,B,118,0,1)
    q=choose(m,rows,B,A,117,1,-1)
    beam_codes=[["c" if slab_hit(r["observer"],r["marker"],*slab,D(0)) else "o" for r in (p,q)] for slab in (A,B)]
    assert beam_codes==[["c","o"],["o","c"]]
    print(json.dumps(dict(nonendpoint_range_lower=R,A=p,B=q,beam_codes=beam_codes),default=str,sort_keys=True))
if __name__=="__main__":main()

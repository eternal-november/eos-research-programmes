from pathlib import Path
from hashlib import sha1
from fractions import Fraction as Q
from itertools import combinations
import csv

def width(turns,period=1):
    pts=sorted(x%period for x in turns)
    return period-max(pts[0]+period-pts[-1],max((b-a for a,b in zip(pts,pts[1:])),default=0))

def recorded():
    phi=Q(1,9)     # 4 * 10 deg per-sample phase allowance, expressed in turns.
    lam=Q('0.06') # a model parameter, not inferred sensor calibration.
    for name,digest,source in csv.reader(open("SOURCE.tsv"),delimiter="\t"):
        b=Path(name).read_bytes()
        assert sha1(f'blob {len(b)}\0'.encode()+b).hexdigest()==digest
        r=[(Q(a), Q(y)) for a,_,x,y,z,*tail in csv.reader(b.decode().splitlines())]
        assert all(a[0] <= b[0] for a,b in zip(r,r[1:]))
        t0=r[0][0]
        first=[y/lam for t,y in r if t-t0<=Q("0.25")]
        assert len(first)>=1 and width(first)<phi
        p=[]
        for t,y in r:
            p.append(y/lam)
            if width(p)>phi:
                onset=t-t0
                break
        else:
            raise AssertionError("declared pair never separates in this recording")
        print(name,len(first),f"{float(width(first)):.8f}",f"{float(onset):.6f}")

def grid():
    n=12
    def dist(a,b):
        d=(a-b)%n
        return min(d,n-d)
    count=0
    # Integer-valued circular-phase interpretation. A common output per
    # sample exists iff its two closed radius-e arcs intersect.
    for length in range(1,5):
        for case in combinations(range(n),length):
            for e in range(3):
                by_offset=any(all(any(dist(v,h)<=e and dist(v,k)<=e for v in range(n))
                                  for k in case) for h in range(n))
                assert by_offset==(width(case,n)<=4*e)
                count+=1
    assert width([0,1,2],12)>width([0,12,24],12)
    print("Discrete direct phase-support checks:",count)
if __name__=="__main__":
    recorded()
    grid()

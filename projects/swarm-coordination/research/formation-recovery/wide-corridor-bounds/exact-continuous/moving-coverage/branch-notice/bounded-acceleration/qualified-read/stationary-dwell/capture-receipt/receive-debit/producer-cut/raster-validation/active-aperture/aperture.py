"""A robust fixed-ray acquisition aperture and a separately charged travel bound."""
from fractions import Fraction as F
from itertools import product
from egl_depth import context,inputs
import raster
from pathlib import Path
import sys
from subprocess import run
from struct import pack
import json
sys.path.insert(0,str(Path(__file__).resolve().parent/'sensor/radio'))
import joined as radio
import motion

E=F(1,5)
T=F(7,25)
O=F(8)
XMIN=F(0)
XMAX=F(2,5)
D=(F(37),F(38))
def apertures(a,width,depths):
    for i in range(width):
        ray=a*F(2*i+1-width,width)
        # For nonnegative camera shifts in this envelope, a target ray
        # cannot pass to the left of the occluder at z=8.
        lo=max(XMIN,E-O*ray,*(-T-d*ray for d in depths))
        hi=min(XMAX,*(T-d*ray for d in depths))
        if lo<hi:yield lo,hi,i
def travel(a,v,t):
    if a*t<=2*v:return a*t*t/4
    return v*t-v*v/a
def midpoint_margin(lo,hi,cap):
    x=min(cap,(lo+hi)/2)
    return min(x-lo,hi-x),x
def join(pixels,center):
    cfg=radio.setups()['far']
    assert cfg[0]==motion.S-F(3,20)
    good_bias=(center-F(1,100),center,center+F(1,100))
    poses=(F(3,20),F(185,1000),*good_bias)
    sources=[(p,w) for p,w in product(poses,(0,1))]
    fmt=b''.join(pack('=ii8f',1,1,*pixels[p,w]) for p,w in sources)
    frame=run(['./sensor/frame'],input=fmt,check=True,capture_output=True).stdout.decode().splitlines()
    assert len(frame)==len(sources)
    records=[]
    for pair,line in zip(sources,frame):
        p,w=pair
        old,raw,stock=map(int,line.split())
        assert old and stock==-1 and raw==(w if p in good_bias else -1)
        records.append((pair,raw))
    q=radio.CEIL(1024*cfg[0]);latest=radio.FLOOR(1024*cfg[1])
    queries=[];inp=[]
    for ((p,w),raw),c,o in product(records,(2,3),(-421,-411,-401)):
        t=q if c==3 else max(q,o+1025)
        a=[(1024+o,'P','OK')]
        if raw>=0:a.append((1024+t,'Q','F' if raw else 'L'))
        inp.append(f'{c} {len(a)}')
        inp.extend(f'{tick} {name} {v}' for tick,name,v in a)
        queries.append((p,w,c,o,t,a))
    lines=run(['./sensor/radio/broker'],input='\n'.join(inp)+'\n',check=True,text=True,capture_output=True).stdout.splitlines()
    assert len(lines)==len(queries)
    hits=0
    for (p,w,c,o,t,a),line in zip(queries,lines):
        n,*got=line.split()
        assert int(n)==len(a) and got==radio.broker_oracle(c,a) and got[0]=='P:OK'
        ok=len(got)==2 and got[-1]==('Q:F' if w else 'Q:L') and t<=latest
        assert ok==(p in good_bias and (c==3 or o==-421))
        hits+=ok
    return len(queries),hits

def main():
    s=inputs();context();r=raster.Render(s)
    # Exact rational for the actual binary64 pinhole parameter consumed
    # by this driver. GPU comparison at non-edge offsets is numerical.
    h=F.from_float(r.halfx)
    a=sorted(apertures(h,r.w,D))
    assert [v[2] for v in a]==[160,159,158,157,156,155]
    lo,hi,i=a[0]
    tlow=F(1,5)
    lo0=min(x[0] for w in D for x in apertures(h,r.w,(w,)))
    assert lo0==lo
    assert F(18556620,10**8)<lo<F(18556621,10**8)
    high=travel(F(20),F(2),tlow)
    low=travel(F(20),F(1),tlow)
    assert (high,low)==(F(1,5),F(3,20))
    best=max((midpoint_margin(l,u,high)+(j,) for l,u,j in a))
    margin,x,ray=best
    assert i==ray and lo<x<hi and x<=high
    assert F(1293662,10**8)<margin<F(1293664,10**8)
    assert low<lo and high-F(15,1000)<lo
    assert F(10,1000)<margin<F(15,1000)

    n=0;maxerr=0
    gpu={};pixels={}
    # Sample safely away from the exact open aperture cuts. The two worlds
    # must be byte-identical at every registered draw before emergence.
    sweep=(F(0),F(15,100),F(185,1000),F(186,1000),F(2,10),F(212,1000),
           F(214,1000),F(215,1000),x-F(1,100),x,x+F(1,100))
    for b,w in product(sweep,(0,1)):
        sc=raster.scene('far',w,'cover')
        a0=r.render(sc,(float(b),0),300.)
        s0,e=raster.rays(r,sc,(float(b),0),300.,a0)
        n+=s0;maxerr=max(maxerr,e)
        v=r.pick(a0,ray,120)[0]
        if any(l<b<u and j==ray for l,u,j in apertures(h,r.w,(D[w],))):
            assert abs(v-(37+w))<.03
        else:
            assert not (isfinite(v) and abs(v-(37+w))<.03)
        gpu[b,w]=bytes(a0)
        pixels[b,w]=(*r.pick(a0,48,120),*r.pick(a0,160,120))
    for b in (F(0),F(15,100),F(185,1000)):
        assert gpu[b,0]==gpu[b,1]
    for b in (x-F(1,100),x,x+F(1,100)):
        assert gpu[b,0]!=gpu[b,1]
    source,cues=join(pixels,x)
    print(json.dumps(dict(
       native_joint_cases=source,native_timely_cues=cues,
       ray_count=n,rendered_scene_count=len(sweep)*2,first_ray=i,
       first_interval=[round(float(lo),9),round(float(hi),9)],
       fixed_ray_bias_supremum=round(float(margin),9),best_nominal=round(float(x),9),
       reach_v2=str(high),reach_v1=str(low),tested_one_centimeter_bias=True,
       impossible_with_fifteen_mm=True,max_observed_error=round(maxerr,7)),
       sort_keys=True,separators=(',',':')))

def isfinite(v):return raster.isfinite(v)
if __name__=='__main__':main()

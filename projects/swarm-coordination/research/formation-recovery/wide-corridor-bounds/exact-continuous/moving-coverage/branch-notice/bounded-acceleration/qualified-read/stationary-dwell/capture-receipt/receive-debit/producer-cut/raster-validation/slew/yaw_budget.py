"""Exact aperture bounds and physically charged two-ray acquisition replay."""
from fractions import Fraction as F
from math import atan,cos,sin,sqrt,isfinite,degrees
from itertools import product
from pathlib import Path
from struct import pack
from subprocess import run
import sys
import json
ROOT=Path.cwd()
sys.path.insert(0,str(ROOT))
sys.path.insert(0,str(ROOT/'sensor/radio'))
import raster
from egl_depth import inputs,context
import joined as radio

class Yaw(raster.Render):
 def __init__(self,s):
    super().__init__(s)
    geom=raster.GEOMETRY.replace(b'uniform float distance;',b'uniform float distance;uniform vec2 yaw;')
    old=b'gl_Position=vec4((u-camera.z)/camera.x,(v-camera.w)/camera.y,\n     (2*projection.x-1)*distance+2*projection.y,distance);'
    assert old in geom
    geom=geom.replace(old,b'float x=yaw.x*(u-camera.z)-yaw.y*distance;\nfloat z=yaw.y*(u-camera.z)+yaw.x*distance;\ngl_Position=vec4(x/camera.x,(v-camera.w)/camera.y,(2*projection.x-1)*z+2*projection.y,z);')
    self.geom=self.program(geom,raster.EMPTY)
    self.orientation=0.
 def unifs(self,prog,v):
    if prog==self.geom and 'camera' in v:v={**v,'yaw':(cos(self.orientation),sin(self.orientation))}
    super().unifs(prog,v)

p=F(1,5);e=F(15,1000);lo=p-e;hi=p+e
old=(F(2,1000),F(15,10000))
optimized=(F(19,10000),F(169,100000))
A=F(4)
q=F(400,637)-F(3,20)
work=p+2*F(1,8)+F(1,100)
budget=q-work
def ap(s):return p-8*s,F(7,25)-38*s
def dangle(s):return atan(float(s[0]))-atan(float(s[1]))
def slew(m,v):
    return 2*sqrt(m/float(A)) if m<=float(v*v/A) else m/float(v)+float(v/A)
def proof():
    s1=e/8;s2=(F(8,100)-e)/38
    # Lower and upper bounds on angular travel via integral 1/(1+x²).
    lower=(s1-s2)/(1+s1*s1)
    assert F(1644,10**7)<lower<s1-s2
    assert lower>F(1,100)**2/A
    assert lower/F(1,100)+F(1,100)/A>budget
    assert F(21,100000)/F(2,100)+F(2,100)/A<budget
    assert F(5,10000)/(1+old[0]**2)>A*budget**2/4
    assert 2*(q-p)>q-p
    e1=F(64,4600);e2=F(8,100)*46*8/(38**2+8**2)
    assert e1<e<e2
    # Strictly bracket the two tangent perturbations using elementary
    # tan(x) bound over |x|<=5e-6: |tan(x)|<5.000001e-6. Consequently
    # each ray slope changes less than 5.001e-6 with these nominal rays.
    z=F(5001,10**9)
    assert ap(optimized[0]-z)[0]<lo and hi<ap(optimized[1]+z)[1]
    assert ap(optimized[1]-z)[0]<ap(optimized[0]+z)[1]
    return lower,e1,e2

def main():
    lower,e1,e2=proof()
    defs=inputs();context();r=Yaw(defs)
    cases=[]
    for schedule,slopes in (('original',old),('optimized',optimized)):
      for b,w,i,bias in product((lo,F(186,1000),F(190,1000),p,F(205,1000),F(210,1000),hi),
                                (0,1),(0,1),(-5e-6,0,5e-6)):
        r.orientation=atan(float(slopes[i]))-atan(r.halfx/r.w)+bias
        frame=r.render(raster.scene('far',w,'cover'),(float(b),0),300.)
        pix=r.pick(frame,160,120)
        oldpix=r.pick(frame,48,120)
        assert abs(oldpix[0]-5)<.012
        cases.append((schedule,b,w,bias,i,oldpix,pix))
    src=b''.join(pack('=ii8f',1,1,*oldpix,*pix) for _,_,_,_,_,oldpix,pix in cases)
    observations=run(['./sensor/frame'],input=src,capture_output=True,check=True).stdout.decode().splitlines()
    assert len(observations)==len(cases)
    seen={}
    for (schedule,b,w,bias,i,oldpix,pix),line in zip(cases,observations):
        good,raw,stock=map(int,line.split())
        assert good and stock==-1
        assert raw==-1 or raw==w
        seen[schedule,b,w,bias,i]=raw
    cfg=radio.setups()['far'];assert cfg[0]==q
    rq=radio.CEIL(q*1024);deadline=radio.FLOOR(cfg[1]*1024)
    queries=[];inp=[]
    configs={('original','both'):(False,old),('optimized','slow'):(False,optimized),
             ('optimized','faster'):(True,optimized)}
    witnessed={}
    for (schedule,limit),(ready,slopes) in configs.items():
      rate=F(2 if limit!='slow' else 1,100)
      assert (float(work)+slew(dangle(slopes),rate)<float(q))==ready
      witnessed[schedule,limit]=0
      for b,w,ang,c,o in product((lo,F(186,1000),F(190,1000),p,F(205,1000),F(210,1000),hi),
             (0,1),(-5e-6,0,5e-6),(2,3),(-421,-411)):
        valid=[i for i in (0,1) if seen[schedule,b,w,ang,i]==w]
        assert valid
        # At lo only angle 0 works, at hi only angle 1. If only
        # first completed, some tested offsets are still serviceable,
        # while the robust requirement over the whole envelope fails.
        usable=(0 in valid or ready)
        t=rq if c==3 else max(rq,o+1025)
        schedule_msgs=[(1024+o,'P','OK')]
        if usable:schedule_msgs.append((1024+t,'Q','F' if w else 'L'))
        inp.append(f'{c} {len(schedule_msgs)}')
        inp.extend(f'{k} {a} {v}' for k,a,v in schedule_msgs)
        queries.append((schedule,limit,usable,t,schedule_msgs,c))
    rs=run(['./sensor/radio/broker'],input='\n'.join(inp)+'\n',text=True,capture_output=True,check=True).stdout.splitlines()
    assert len(rs)==len(queries)
    for (sched,limit,usable,t,a,c),out in zip(queries,rs):
        n,*ret=out.split()
        assert int(n)==len(a) and ret==radio.broker_oracle(c,a)
        assert ret[0]=='P:OK'
        ok=(len(ret)==2 and ret[1]!='-' and t<=deadline)
        assert ok==(usable and t<=deadline)
        witnessed[sched,limit]+=ok
    assert witnessed['optimized','faster']==126
    print(json.dumps(dict(native_frames=len(cases),broker_cases=len(queries),
       codewords={a+'/'+b:c for (a,b),c in witnessed.items()},
       old_gate=float(work)+slew(dangle(old),F(2,100)),
       optimized_gate=float(work)+slew(dangle(optimized),F(2,100)),cut=float(q),
       one_ray_supremum=float(e1),two_rays_supremum_no_slew=float(e2),
       slow_actuator_infeasible_lower_angle=float(lower),
       optimized_move_degrees=degrees(dangle(optimized))),sort_keys=True,separators=(',',':')))
if __name__=='__main__':main()

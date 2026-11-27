"""Pinned Ogre2 depth shader passes applied to real EGL-rasterized geometry."""
from ctypes import *
from xml.etree import ElementTree as XML
from math import tan,isfinite,isinf
from pathlib import Path
from functools import lru_cache
import json
from egl_depth import GL,context,symbol,inputs

def pin(s):
    x=XML.fromstring(s['camera.sdf']).find(".//sensor[@name='camera_front']/camera")
    assert list(map(float,(x.findtext('clip/far'),x.findtext('depth_camera/clip/far'))))==[300.,10.]
    assert 'depthTexDef->formatList = {Ogre::PF_D32_FLOAT};' in s['camera-render.cc'].decode()
    assert 'projectionB /= farPlane;' in s['camera-render.cc'].decode()
    w,h=int(x.findtext('image/width')),int(x.findtext('image/height'))
    a=tan(float(x.findtext('horizontal_fov'))/2)
    return w,h,a,a*h/w,float(x.findtext('clip/near'))

# Geometry uses a simple centered perspective pin, not Ogre's full scene graph.
# The two pinned postprocess passes are unmodified.
GEOMETRY=b'''#version 330
uniform vec4 edges;
uniform vec4 camera;
uniform float distance;
uniform vec2 projection;
void main(){
  const int labels[6]=int[6](0,1,2,2,1,3);
  int c=labels[gl_VertexID];
  float u=(c%2)==0 ? edges.x : edges.y;
  float v=(c/2)==0 ? edges.z : edges.w;
  gl_Position=vec4((u-camera.z)/camera.x,(v-camera.w)/camera.y,
     (2*projection.x-1)*distance+2*projection.y,distance);
}'''
EMPTY=b'''#version 330
void main(){}'''

class Render(GL):
 def __init__(self,s):
    super().__init__()
    self.w,self.h,self.halfx,self.halfy,self.near=pin(s)
    for method,ret,args in [
       ('DrawBuffer',None,(c_uint,)),('ReadBuffer',None,(c_uint,)),('Enable',None,(c_uint,)),
       ('Disable',None,(c_uint,)),('DepthFunc',None,(c_uint,)),('ClearDepth',None,(c_double,)),
       ('Clear',None,(c_uint,)),('GenBuffers',None,(c_int,POINTER(c_uint))),
       ('BindBuffer',None,(c_uint,c_uint)),('BufferData',None,(c_uint,c_ssize_t,c_void_p,c_uint)),
       ('GetAttribLocation',c_int,(c_uint,c_char_p)),('EnableVertexAttribArray',None,(c_uint,)),
       ('DisableVertexAttribArray',None,(c_uint,)),
       ('VertexAttribPointer',None,(c_uint,c_int,c_uint,c_ubyte,c_int,c_void_p)),
       ('UniformMatrix4fv',None,(c_int,c_int,c_ubyte,POINTER(c_float))),
       ('DeleteTextures',None,(c_int,POINTER(c_uint))),('DeleteFramebuffers',None,(c_int,POINTER(c_uint))),
    ]:setattr(self,method,symbol(self.g,'gl'+method,ret,*args))
    self.geom=self.program(GEOMETRY,EMPTY)
    self.raw=self.program(s['native-depth.vs'],s['native-depth.fs'])
    self.final=self.program(s['native-final.vs'],s['native-final.fs'])
    v=c_uint();self.GenBuffers(1,byref(v));self.vbo=v
    self.active=()
    self.color=self.texture(0x8814,0x1908,[.1,.1,.1,1]*(self.w*self.h))
 def texture(self,iformat,fmt,data=None):
    t=c_uint();self.GenTextures(1,byref(t));self.bind(t,7)
    for param,key in ((0x2801,0x2600),(0x2800,0x2600),(0x2802,0x812f),(0x2803,0x812f)):
      self.TexParameteri(0xde1,param,key)
    arr=(c_float*len(data))(*data) if data is not None else None
    self.TexImage2D(0xde1,0,iformat,self.w,self.h,0,fmt,0x1406,arr)
    return t
 def attach(self,t,depth=False):
    f=c_uint();self.GenFramebuffers(1,byref(f));self.BindFramebuffer(0x8d40,f)
    self.FramebufferTexture2D(0x8d40,0x8d00 if depth else 0x8ce0,0xde1,t,0)
    self.DrawBuffer(0 if depth else 0x8ce0)
    self.ReadBuffer(0 if depth else 0x8ce0)
    assert self.CheckFramebufferStatus(0x8d40)==0x8cd5
    self.Viewport(0,0,self.w,self.h)
    return f
 def unifs(self,prog,values):
    for k,v in values.items():
      u=self.GetUniformLocation(prog,k.encode())
      assert u>=0,k
      getattr(self,f'Uniform{len(v)}f')(u,*v)
 def draw(self,scene,pos,far):
    for idx in self.active:self.DisableVertexAttribArray(idx)
    self.active=()
    near_outer=.9*self.near;far_outer=1.1*far
    A=far_outer/(far_outer-near_outer)
    B=-far_outer*near_outer/(far_outer-near_outer)
    t=self.texture(0x8cac,0x1902);f=self.attach(t,True) # DEPTH_COMPONENT32F
    self.Enable(0xb71);self.DepthFunc(0x201);self.ClearDepth(1);self.Clear(0x100)
    self.UseProgram(self.geom)
    self.unifs(self.geom,{'camera':(self.halfx,self.halfy,*pos),'projection':(A,B)})
    for d,l,r,b,u in scene:
        self.unifs(self.geom,{'distance':(d,),'edges':(l,r,b,u)})
        self.DrawArrays(4,0,6)
    self.Disable(0xb71)
    return t,f,(A,B,far_outer)
 def sample(self,prog,refs,far_outer,values,read=False):
    for idx in self.active:self.DisableVertexAttribArray(idx)
    active=[]
    # Uniform camera-frustum corners, following the native quad vertex interface.
    b=[]
    for x,y in ((-1,-1),(1,-1),(-1,1),(-1,1),(1,-1),(1,1)):
        b.extend((x,y,0,1,
                  x*self.halfx*far_outer,y*self.halfy*far_outer,-far_outer,(x+1)/2,(y+1)/2))
    arr=(c_float*len(b))(*b)
    self.BindBuffer(0x8892,self.vbo);self.BufferData(0x8892,sizeof(arr),arr,0x88e4)
    for k,n,o in (('vertex',4,0),('normal',3,4),('uv0',2,7)):
      idx=self.GetAttribLocation(prog,k.encode())
      if idx<0:continue
      self.EnableVertexAttribArray(idx)
      self.VertexAttribPointer(idx,n,0x1406,0,36,c_void_p(o*4))
      active.append(idx)
    self.active=tuple(active)
    t=self.texture(0x8814,0x1908);f=self.attach(t)
    self.UseProgram(prog)
    uni=self.GetUniformLocation(prog,b'worldViewProj')
    assert uni>=0
    self.UniformMatrix4fv(uni,1,0,(c_float*16)(1,0,0,0,0,1,0,0,0,0,1,0,0,0,0,1))
    for i,(k,a) in enumerate(refs):
      self.bind(a,i)
      uni=self.GetUniformLocation(prog,k.encode())
      assert uni>=0
      self.Uniform1i(uni,i)
    self.unifs(prog,values)
    self.DrawArrays(4,0,6)
    out=None
    if read:
        out=(c_float*(self.w*self.h*4))()
        self.ReadPixels(0,0,self.w,self.h,0x1908,0x1406,out)
    assert self.GetError()==0
    return t,f,out
 def render(self,scene,pos,far):
    depth,fd,(A,B,F)=self.draw(scene,pos,far)
    limits={'near':(self.near,),'far':(far,),'min':(-float('inf'),),'max':(float('inf'),)}
    raw,fr,_=self.sample(self.raw,[('depthTexture',depth),('colorTexture',self.color)],F,
             {**limits,'projectionParams':(A,B/F),'backgroundColor':(0.,0.,0.)})
    final,ff,out=self.sample(self.final,[('inputTexture',raw)],F,
             {**limits,'texResolution':(self.w,self.h,0,0)},True)
    self.DeleteTextures(3,(c_uint*3)(depth.value,raw.value,final.value))
    self.DeleteFramebuffers(3,(c_uint*3)(fd.value,fr.value,ff.value))
    return out
 def pick(self,v,i,j):
    return tuple(v[4*(j*self.w+i):4*(j*self.w+i+1)])

OLD=(5.,-2.2,-1.7,-.25,.25)
COVER=(8.,-.20,.20,-.20,.20)
SLIVER=(8.,.021,.026,-.25,.25)
def scene(site,world,occlusion):
    target=(float((37 if site=='far' else 7)+world),-.28,.28,-.28,.28)
    return (OLD,target) + {'open':(),'cover':(COVER,),'sliver':(SLIVER,)}[occlusion]

def rays(r,sc,pos,far,gpu):
    """Independent analytic pinhole/ray visibility before numerical value comparison."""
    total=0;err=0
    for j in range(r.h):
      y=r.halfy*(2*(j+.5)/r.h-1)
      for i in range(r.w):
        x=r.halfx*(2*(i+.5)/r.w-1)
        ds=[]
        for d,l,u,b,t in sc:
          if r.near<=d<=far and l<pos[0]+d*x<u and b<pos[1]+d*y<t:ds.append(d)
        got=r.pick(gpu,i,j)
        if not ds:
            assert all(isinf(a) and a>0 for a in got[:3]),(i,j,got,sc,pos)
        else:
            d=min(ds)
            expect=(d,-d*x,d*y)
            delta=max(abs(a-b) for a,b in zip(got,expect))
            assert delta<.03,(i,j,got,expect)
            err=max(err,delta)
        total+=1
    return total,err

def main():
    s=inputs();context();r=Render(s);n=0;maxerr=0;trace={};cache={}
    for site in ('near','far'):
      for occ in ('open','cover','sliver') if site=='far' else ('open',):
        for off in (0.,.009):
          for fr in (10.,300.):
            for w in (0,1):
              sc=scene(site,w,occ)
              g=r.render(sc,(off,0),fr)
              count,err=rays(r,sc,(off,0),fr,g)
              n+=count;maxerr=max(maxerr,err)
              cache[site,occ,off,fr,w]=bytes(g)
              old,x=r.pick(g,48,120)[0],r.pick(g,160,120)[0]
              assert abs(old-5)<.01
              val=round(x,5) if isfinite(x) else None
              trace[f'{site}/{occ}/{off}/{fr}/{w}']=val
    for far in (10.,300.):
      for offset in (0.,.009):assert cache['far','cover',offset,far,0]==cache['far','cover',offset,far,1]
    assert cache['far','open',0.,10.,0]==cache['far','open',0.,10.,1]
    for w in (0,1):
      assert cache['far','open',0.,300.,w]==cache['far','sliver',0.,300.,w]
      assert abs(trace[f'far/sliver/0.009/300.0/{w}']-8)<.02
      assert abs(trace[f'far/open/0.0/300.0/{w}']-(37+w))<.02
    print(json.dumps({'images':len(trace),'ray_comparisons':n,'max_observed_axis_error':round(maxerr,7),
       'renderer':r.GetString(0x1f01).decode(),'gl':r.GetString(0x1f02).decode(),
       'cue_depths':trace},sort_keys=True,separators=(',',':')))
if __name__=='__main__':main()

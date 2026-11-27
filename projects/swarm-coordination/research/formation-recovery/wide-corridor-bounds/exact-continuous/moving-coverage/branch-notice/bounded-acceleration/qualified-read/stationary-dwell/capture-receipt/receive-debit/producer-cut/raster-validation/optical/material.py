"""Rasterize an explicitly colored optical sign before unmodified native shaders."""
from ctypes import c_uint,c_float,byref
from pathlib import Path
import sys
import json
sys.path.insert(0,str(Path.cwd()))
import raster
from egl_depth import symbol,context,inputs

PAL=((.25,.015625,.00390625,1.),(.015625,.25,.00390625,1.))
NEUTRAL=(.0625,.0625,.0625,1.)
class ColorRender(raster.Render):
 def __init__(self,s):
    super().__init__(s)
    self.geom=self.program(raster.GEOMETRY,b'''#version 330
uniform vec4 material;out vec4 frag;void main(){frag=material;}''')
    self.ClearColor=symbol(self.g,'glClearColor',None,c_float,c_float,c_float,c_float)
 def draw_pair(self,scene,pos,far):
    for a in self.active:self.DisableVertexAttribArray(a)
    self.active=()
    outer=.9*self.near;F=1.1*far
    A=F/(F-outer);B=-F*outer/(F-outer)
    depth=self.texture(0x8cac,0x1902);col=self.texture(0x8814,0x1908)
    f=self.attach(col)
    self.FramebufferTexture2D(0x8d40,0x8d00,0xde1,depth,0)
    assert self.CheckFramebufferStatus(0x8d40)==0x8cd5
    self.Enable(0xb71);self.DepthFunc(0x201);self.ClearDepth(1)
    self.ClearColor(*NEUTRAL);self.Clear(0x100|0x4000)
    self.UseProgram(self.geom)
    self.unifs(self.geom,{'camera':(self.halfx,self.halfy,*pos),'projection':(A,B)})
    for (d,l,r,b,u),col0 in scene:
        self.unifs(self.geom,{'distance':(d,),'edges':(l,r,b,u),'material':col0})
        self.DrawArrays(4,0,6)
    self.Disable(0xb71)
    return depth,col,f,A,B,F
 def render_flags(self,s,pose,far):
    depth,col,fd,A,B,F=self.draw_pair(s,pose,far)
    lim={'near':(self.near,),'far':(far,),'min':(-float('inf'),),'max':(float('inf'),)}
    raw,fr,_=self.sample(self.raw,[('depthTexture',depth),('colorTexture',col)],F,
                {**lim,'projectionParams':(A,B/F),'backgroundColor':NEUTRAL[:3]})
    fin,ff,out=self.sample(self.final,[('inputTexture',raw)],F,
                {**lim,'texResolution':(self.w,self.h,0,0)},True)
    self.DeleteTextures(4,(c_uint*4)(depth.value,col.value,raw.value,fin.value))
    self.DeleteFramebuffers(3,(c_uint*3)(fd.value,fr.value,ff.value))
    return out

def scene(w,mode,oc):
    # The source-provided sign is the controlled channel. The scene's
    # mechanical choice is held fixed at the qualified source cut.
    p=raster.scene('far',w,oc)
    return tuple((v,((PAL[w] if mode=='right' else PAL[1-w]) if j==1 and mode!='none'
                     else NEUTRAL)) for j,v in enumerate(p))
if __name__=='__main__':
    s=inputs();context();r=ColorRender(s)
    from struct import pack,unpack
    out=[]
    for w in (0,1):
        f=r.render_flags(scene(w,'right','open'),(0,0),300.)
        raw=r.pick(f,160,120)
        out.append((raw[0],hex(unpack('=I',pack('=f',raw[3]))[0])))
    print(out)

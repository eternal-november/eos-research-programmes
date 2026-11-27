"""Exact pinned GLSL on Mesa with authored, synthetic depth-buffer samples."""
from ctypes import *
from pathlib import Path
from hashlib import sha1
import json
import math
import os

os.environ['EGL_PLATFORM']='surfaceless'
os.environ['LIBGL_ALWAYS_SOFTWARE']='1'
os.environ['MESA_SHADER_CACHE_DISABLE']='true'
def symbol(lib,n,res,*args):
    p=getattr(lib,n);p.restype=res;p.argtypes=list(args);return p
def inputs():
    ds={}
    for l in Path('INPUTS.tsv').read_text().splitlines():
        p,_,_,_,h=l.split('\t')
        b=Path(p).read_bytes()
        assert sha1(f'blob {len(b)}\0'.encode()+b).hexdigest()==h
        ds[p]=b
    return ds

def context():
    egl=CDLL('libEGL.so.1')
    gp=symbol(egl,'eglGetDisplay',c_void_p,c_void_p)(None)
    a=c_int();b=c_int()
    assert symbol(egl,'eglInitialize',c_uint,c_void_p,POINTER(c_int),POINTER(c_int))(gp,byref(a),byref(b))
    assert symbol(egl,'eglBindAPI',c_uint,c_uint)(0x30a2)
    cfg=c_void_p();n=c_int()
    assert symbol(egl,'eglChooseConfig',c_uint,c_void_p,POINTER(c_int),POINTER(c_void_p),c_int,POINTER(c_int))(
      gp,(c_int*5)(0x3033,1,0x3040,8,0x3038),byref(cfg),1,byref(n)) and n.value
    ctx=symbol(egl,'eglCreateContext',c_void_p,c_void_p,c_void_p,c_void_p,POINTER(c_int))(
      gp,cfg,None,(c_int*5)(0x3098,3,0x30fb,3,0x3038))
    assert ctx
    assert symbol(egl,'eglMakeCurrent',c_uint,c_void_p,c_void_p,c_void_p,c_void_p)(gp,None,None,ctx)
def vertex(depth):
    return ('''#version 330
    out block { vec2 uv0; STRIDE } outVs;
    uniform float visualFar;
    void main(){
      vec2 uv=vec2(gl_VertexID == 1 ? 2.0 : 0.0, gl_VertexID == 2 ? 2.0 : 0.0);
      gl_Position=vec4(uv*2-1,0,1);
      outVs.uv0=uv;
      END
    }'''.replace('STRIDE','vec3 cameraDir;' if depth else '')
         .replace('END','outVs.cameraDir=vec3(0,0,-visualFar);' if depth else '')).encode()

class GL:
 def __init__(self):
    self.g=CDLL('libGL.so.1')
    for method,ret,args in [
       ('GetString',c_char_p,(c_uint,)),
       ('CreateShader',c_uint,(c_uint,)),('ShaderSource',None,(c_uint,c_int,POINTER(c_char_p),c_void_p)),
       ('CompileShader',None,(c_uint,)),('GetShaderiv',None,(c_uint,c_uint,POINTER(c_int))),
       ('GetShaderInfoLog',None,(c_uint,c_int,POINTER(c_int),c_char_p)),
       ('CreateProgram',c_uint,()),('AttachShader',None,(c_uint,c_uint)),('LinkProgram',None,(c_uint,)),
       ('GetProgramiv',None,(c_uint,c_uint,POINTER(c_int))),
       ('GetProgramInfoLog',None,(c_uint,c_int,POINTER(c_int),c_char_p)),
       ('UseProgram',None,(c_uint,)),('GetUniformLocation',c_int,(c_uint,c_char_p)),
       ('Uniform1i',None,(c_int,c_int)),('Uniform1f',None,(c_int,c_float)),
       ('Uniform2f',None,(c_int,c_float,c_float)),('Uniform3f',None,(c_int,c_float,c_float,c_float)),
       ('Uniform4f',None,(c_int,c_float,c_float,c_float,c_float)),
       ('GenTextures',None,(c_int,POINTER(c_uint))),('BindTexture',None,(c_uint,c_uint)),
       ('ActiveTexture',None,(c_uint,)),('TexParameteri',None,(c_uint,c_uint,c_int)),
       ('TexImage2D',None,(c_uint,c_int,c_int,c_int,c_int,c_int,c_uint,c_uint,c_void_p)),
       ('GenFramebuffers',None,(c_int,POINTER(c_uint))),('BindFramebuffer',None,(c_uint,c_uint)),
       ('FramebufferTexture2D',None,(c_uint,c_uint,c_uint,c_uint,c_int)),
       ('CheckFramebufferStatus',c_uint,(c_uint,)),
       ('GenVertexArrays',None,(c_int,POINTER(c_uint))),('BindVertexArray',None,(c_uint,)),
       ('Viewport',None,(c_int,c_int,c_int,c_int)),('DrawArrays',None,(c_uint,c_int,c_int)),
       ('ReadPixels',None,(c_int,c_int,c_int,c_int,c_uint,c_uint,c_void_p)),
       ('GetError',c_uint,()),
    ]:setattr(self,method,symbol(self.g,'gl'+method,ret,*args))
    v=c_uint();self.GenVertexArrays(1,byref(v));self.BindVertexArray(v)
 def program(self,vs,fs):
    p=self.CreateProgram()
    for kind,src in ((0x8b31,vs),(0x8b30,fs)):
      h=self.CreateShader(kind)
      b=c_char_p(src);self.ShaderSource(h,1,byref(b),None);self.CompileShader(h)
      ok=c_int();self.GetShaderiv(h,0x8b81,byref(ok))
      if not ok.value:
        b=create_string_buffer(16384);self.GetShaderInfoLog(h,len(b),None,b);raise ValueError(b.value.decode())
      self.AttachShader(p,h)
    self.LinkProgram(p);ok=c_int();self.GetProgramiv(p,0x8b82,byref(ok))
    if not ok.value:
      b=create_string_buffer(16384);self.GetProgramInfoLog(p,len(b),None,b);raise ValueError(b.value.decode())
    return p
 def tex(self,n,samples=None,rgba=True,unit=0):
    t=c_uint();self.GenTextures(1,byref(t));self.ActiveTexture(0x84c0+unit);self.BindTexture(0xde1,t)
    for param,key in ((0x2801,0x2600),(0x2800,0x2600),(0x2802,0x812f),(0x2803,0x812f)):
      self.TexParameteri(0xde1,param,key)
    data=(c_float*len(samples))(*samples) if samples is not None else None
    self.TexImage2D(0xde1,0,0x8814 if rgba else 0x822e,n,1,0,0x1908 if rgba else 0x1903,0x1406,data)
    return t
 def bind(self,tid,unit):
    self.ActiveTexture(0x84c0+unit);self.BindTexture(0xde1,tid)
 def emit(self,n,program,read,unif):
    t=self.tex(n,unit=7)
    f=c_uint();self.GenFramebuffers(1,byref(f));self.BindFramebuffer(0x8d40,f)
    self.FramebufferTexture2D(0x8d40,0x8ce0,0xde1,t,0)
    assert self.CheckFramebufferStatus(0x8d40)==0x8cd5
    self.UseProgram(program)
    for i,(name,texture) in enumerate(read):
      self.bind(texture,i);self.Uniform1i(self.GetUniformLocation(program,name.encode()),i)
    for name,values in unif.items():
      getattr(self,f'Uniform{len(values)}f')(self.GetUniformLocation(program,name.encode()),*values)
    self.Viewport(0,0,n,1);self.DrawArrays(4,0,3)
    o=(c_float*(n*4))();self.ReadPixels(0,0,n,1,0x1908,0x1406,o)
    assert self.GetError()==0
    return t,tuple(o)

def main():
    s=inputs();context();gl=GL()
    raw=gl.program(vertex(True),s['native-depth.fs'])
    final=gl.program(vertex(False),s['native-final.fs'])
    outputs={}
    for far in (10.,300.):
      near=.01;nclip=.9*near;fclip=1.1*far
      a=fclip/(fclip-nclip);b=-nclip/(fclip-nclip)
      vals=(.001,5,7,8,37,38,299,far,500)
      data=[max(0,min(1,a+b*fclip/d)) for d in vals];n=len(vals)
      dep=gl.tex(n,data,rgba=False)
      col=gl.tex(n,[.1,.1,.1,1]*n)
      limits={'near':(near,),'far':(far,),'min':(-math.inf,),'max':(math.inf,)}
      mid,pre=gl.emit(n,raw,[('depthTexture',dep),('colorTexture',col)],
         {**limits,'visualFar':(fclip,),'projectionParams':(a,b),'backgroundColor':(0.,0.,0.)})
      _,post=gl.emit(n,final,[('inputTexture',mid)],{**limits,'texResolution':(n,1,0,0)})
      assert math.isinf(post[0]) and post[0]<0
      assert abs(post[4]-5)<.02 and abs(post[8]-7)<.02 and abs(post[12]-8)<.02
      if far==10.:
        assert all(math.isinf(post[4*i]) and post[4*i]>0 for i in (4,5,6))
      else:
        assert abs(post[16]-37)<.05 and abs(post[20]-38)<.05 and post[20]-post[16]>.9
        assert abs(post[24]-299)<1
      outputs[str(int(far))]=[round(post[4*i],5) if math.isfinite(post[4*i]) else
           ('+inf' if post[4*i]>0 else '-inf') for i in range(n)]
    print(json.dumps({'gl_version':gl.GetString(0x1f02).decode(),
      'driver':gl.GetString(0x1f01).decode(),'ranges':outputs},sort_keys=True,separators=(',',':')))
if __name__=='__main__':main()

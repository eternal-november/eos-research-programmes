from fractions import Fraction as F
from itertools import product
import json

def safe(p,r,d):
 a,b,c=p;m=r-d
 return all(abs(t)<=m for t in (c,c+r*a,c+r*b))
def step(x,p,w):
 a,b,c=p
 return a*max(x,0)+b*max(-x,0)+c+w

def psi(q,z):
 r,d=q;m=r-d;z0,zp,zm=z
 return (m/r*(zp-z0),m/r*(zm-z0),m*z0)
def inv(q,p):
 r,d=q;m=r-d;a,b,c=p
 return (c/m,(c+r*a)/m,(c+r*b)/m)
def transport(q,qq,p):return psi(qq,inv(q,p))
def clip(z):return tuple(max(F(-1),min(F(1),x)) for x in z)
def run():
 out={};q=(F(1),F(1,4));r,d=q
 grid=[F(i,4) for i in range(-6,7)];n=0
 for p in product(grid,repeat=3):
  explicit=all(abs(step(x,p,w))<=r for x,w in product((-r,F(0),r),(-d,d)))
  assert safe(p,r,d)==explicit;n+=1
 out['endpoint_equivalence_parameter_grid']=n
 qs=[q,(F(2),F(1,2)),(F(3,2),F(1,3))]
 for z in product((F(-1),F(0),F(1)),repeat=3):
  p=psi(q,z);assert inv(q,p)==z and safe(p,*q)
  assert transport(qs[1],qs[2],transport(qs[0],qs[1],p))==transport(qs[0],qs[2],p)
 out['transport_cube_vertices_and_faces']=27
 p=(F(3,4),F(3,4),F(0));assert safe(p,*q)
 assert step(F(1),p,F(1,2))==F(5,4)
 pp=transport(q,(F(1),F(1,2)),p);assert safe(pp,F(1),F(1,2))
 out['changed_disturbance_transport']='pass'
 z=(F(0),F(1),F(1));eps=F(1,100)
 loss=lambda dd:sum(psi((F(1),dd),z)[:2])
 assert (loss(d+eps)-loss(d))/eps==-2
 out['legal_context_derivative']=-2
 z=clip((F(3),F(-2),F(1,2)));assert safe(psi(q,z),*q)
 out['clipped_training_update']='pass'
 x=F(2,3)
 for t in range(60):
  dd=F(1,4) if t%2 else F(1,2)
  zz=clip((F(-1) if x<0 else F(1),F(t%5-2),F(1,2)));p=psi((F(1),dd),zz)
  x=step(x,p,dd if t%3 else -dd);assert abs(x)<=1
 out['adaptive_certified_deployment_steps']=60
 exact=max(step(x,(F(3,4),F(3,4),F(0)),d) for x in (-r,F(0),r))
 interval=F(3,4)*2+d
 assert exact==1 and interval==F(7,4)
 out['joint_feature_hull_vs_box']={'exact':str(exact),'box':str(interval)}
 f=lambda v,w,x:v*max(w*x,0)
 assert f(0,4,1)==0 and f(4,0,1)==0 and f(2,2,1)==4
 out['hidden_layer_midpoint_failure']='pass'
 return out
if __name__=='__main__':print(json.dumps(run(),indent=2))

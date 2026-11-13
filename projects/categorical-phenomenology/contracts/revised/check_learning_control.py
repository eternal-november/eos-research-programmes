#!/usr/bin/env python3
"""Exact algebra checks only, not an ODE existence or research-target proof."""
from pathlib import Path
from fractions import Fraction as F
import json, hashlib
# w = uv, s = u*u + v*v, du = -v*g, dv = -u*g.
# Formal monomials are tuples (power(u), power(v), power(g)).
def plus(a,b):
 out=a.copy()
 for k,v in b.items(): out[k]=out.get(k,0)+v
 return {k:v for k,v in out.items() if v}
def times(a,b):
 out={}
 for k,v in a.items():
  for l,w in b.items():
   key=tuple(x+y for x,y in zip(k,l));out[key]=out.get(key,0)+v*w
 return {k:v for k,v in out.items() if v}
u={(1,0,0):1};v={(0,1,0):1};g={(0,0,1):1}
neg={(0,0,0):-1};two={(0,0,0):2};minus4={(0,0,0):-4}
du=times(neg,times(v,g));dv=times(neg,times(u,g))
w=times(u,v);s=plus(times(u,u),times(v,v))
dw=plus(times(v,du),times(u,dv))
ds=plus(times(two,times(u,du)),times(two,times(v,dv)))
if dw != times(neg,times(s,g)):
 raise ValueError("The formal identity dw = -s*g failed.")
if ds != times(minus4,times(w,g)):
 raise ValueError("The formal identity ds = -4*w*g failed.")
points=[(F(1),F(1)),(F(2),F(1,2))]
if [u*v for u,v in points] != [F(1),F(1)]:
 raise ValueError("The two predictors do not equal 1.")
if [u*u+v*v for u,v in points] != [F(2),F(17,4)]:
 raise ValueError("The two response-state values are incorrect.")
source=Path(__file__).with_name('contract.tex').read_bytes()
result={'source_sha256':hashlib.sha256(source).hexdigest(),'status':'pass','checks':['Formal chain rule gives dw = -s*g and ds = -4*w*g.','The two points have w = 1 and distinct s = 2, 17/4.'],'scope':'Exact polynomial identities and rational point arithmetic only. Well-posedness, minimality, empirical access and new research targets are not verified.'}
Path(__file__).with_name('learning_control_checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))

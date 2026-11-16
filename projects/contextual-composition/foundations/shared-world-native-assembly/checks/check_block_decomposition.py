"""Finite exact block/native-body discriminators, not universal limit proof."""
from fractions import Fraction as F
from itertools import product
import json
U=(0,1)
flat=tuple((u,a,b) for u in U for a,b in product((0,1),repeat=2))
q={z:(F(1,4) if z[1]==z[2] else F(0)) for z in flat}
# Three blocks: actor1, empty, actor2. Empty block retains world coordinate.
def split(z):
 u,a,b=z
 return ((u,a),u,(u,b))
def join(t):
 (u,a),v,(w,b)=t
 assert u==v==w
 return (u,a,b)
assert all(join(split(z))==z for z in flat)
lam={split(z):p for z,p in q.items()}
assert sum(q.values())==sum(lam.values())==1
marg=[{} for _ in range(3)]
for t,p in lam.items():
 for j,x in enumerate(t):marg[j][x]=marg[j].get(x,F(0))+p
assert marg[1]=={0:F(1,2),1:F(1,2)}
# Marginals and common boundary do not retain the cross-block correlation.
ind={z:F(1,8) for z in flat}
assert ind!=q
for j in (1,2):
 for u,b in product(U,(0,1)):
  assert sum(p for z,p in q.items() if z[0]==u and z[j]==b)==sum(p for z,p in ind.items() if z[0]==u and z[j]==b)
# Full writer shape families include unused coordinate9 at each actor.
shapes=tuple((u,a,b) for u in U for a,b in product((0,1,9),repeat=2))
assert len(shapes)==18 and all(join(split(s))==s for s in shapes)
# Missing boundary body witness: U singleton, participant returns raw bit
# at full boundary grade B=bits. No possible passive singleton body works.
possible=[]
for passive_body in (0,1):
 if all(passive_body==bit for bit in (0,1)):possible.append(passive_body)
assert not possible
# Slice coefficient neutral test on concrete coordinate elements:
# L=(x,y), K1=(x,y,a), K2=(x,y,b), K1 x_L K2=(x,y,a,b).
for x,y,a,b in product((-1,0,1),repeat=4):
 grouped=((x,y,a),(x,y),(x,y,b))
 ((xx,yy,aa),(xxx,yyy),(xxxx,yyyy,bb))=grouped
 assert (xx,yy)==(xxx,yyy)==(xxxx,yyyy)
 assert (xx,yy,aa,bb)==(x,y,a,b)
print(json.dumps({'status':'passed','raw_atoms':len(flat),'raw_zero_atoms':sum(p==0 for p in q.values()),
 'full_writer_shapes_including_unused':len(shapes), 'empty_block_world_marginal':{str(k):str(v) for k,v in marg[1].items()},
 'missing_boundary_body_possible_maps':possible,
 'scope':'finite discriminator checks; full limit and naturality proof reviewed separately'},indent=2))

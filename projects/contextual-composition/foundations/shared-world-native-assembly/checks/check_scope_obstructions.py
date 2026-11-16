from fractions import Fraction as F
from itertools import product
import json,re
from pathlib import Path
# Full state: world, cached read1, cached read2, pc1, pc2.
def step(s,c):
 x,r1,r2,p1,p2=s
 if c=='R1': assert p1==0;return x,x,r2,1,p2
 if c=='R2': assert p2==0;return x,r1,x,p1,1
 if c=='W1': assert p1==1;return r1+1,r1,r2,2,p2
 if c=='W2': assert p2==1;return r2+1,r1,r2,p1,2
s=step((0,None,None,0,0),'R1')
a=step(step(s,'R2'),'W1');b=step(step(s,'W1'),'R2')
assert a[0]==b[0]==1 and a[2]==0 and b[2]==1
assert step(a,'W2')[0]==1 and step(b,'W2')[0]==2
# Every read-before-write shuffle, no quotient by endpoint or probability.
words=[]
def extend(prefix,remaining):
 if not remaining: words.append(prefix);return
 for c in remaining:
  if c[0]=='W' and 'R'+c[1] not in prefix:continue
  extend(prefix+[c],[x for x in remaining if x!=c])
extend([],['R1','W1','R2','W2'])
finals=[]
for word in words:
 t=(0,None,None,0,0)
 for c in word:t=step(t,c)
 finals.append(t[0])
assert len(words)==6 and sorted(finals)==[1,1,1,1,2,2]
# Native finite row pushforward with raw zero retained, plus dependent bind.
p={0:F(1,2),1:F(1,2),2:F(0)};r={0:0,1:0,2:1};pp={0:F(1),1:F(0)}
q={0:{0:F(1,3),1:F(2,3)},1:{0:F(1,3),1:F(2,3)},2:{0:F(1),1:F(0)}}
qp={0:q[0],1:q[2]}
for u,v in product(range(2),repeat=2):
 assert sum((p[w]*q[w][v] for w in p if r[w]==u),F())==pp[u]*qp[u][v]
assert (2,1) in [(w,z) for w in p for z in q[w]]
# 9->7 coefficient interchanger matrix from baseline labelled basis.
# Columns ee,eu,ev,ue,uu,uv,ve,vu,vv. Cross terms uv,vu vanish.
columns=[0,1,4,2,3,None,5,None,6]
mat=[[F(int(x==i)) if x is not None else F(0) for x in columns] for i in range(7)]
assert all(sum(abs(a) for a in row)==1 for row in mat)
assert all(sum(abs(mat[i][j]) for i in range(7))==0 for j in (5,7))
assert len(set(x for x in columns if x is not None))==7
source=(Path(__file__).resolve().parent.parent / 'Shared_World_Scope_Transitions_and_Arena_Obstruction.tex').read_text();stack=[]
for op,name in re.findall(r'\\(begin|end)\{([^}]+)\}',source):
 if op=='begin':stack.append(name)
 else:assert stack.pop()==name
assert not stack
print(json.dumps({'status':'PASS','read_write_shuffles':6,'lost_update_histories':4,'full_state_diamond_failure':{'R2_W1':a,'W1_R2':b},'dependent_fibre_checks':4,'zero_tuple_retained':True,'interchanger_rank':7,'interchanger_kernel_dimension':2,'scope':'finite discriminators and source environment balance; not general categorical verification'},indent=2))

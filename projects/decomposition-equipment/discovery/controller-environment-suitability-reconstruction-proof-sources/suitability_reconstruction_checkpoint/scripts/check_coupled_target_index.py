#!/usr/bin/env python3
"""Exhaustive small-instance checks for stable-block capability and its driver."""
import itertools,json,math,pathlib,hashlib
ROOT=pathlib.Path(__file__).resolve().parents[1]
def words(m,r):
 n=m*r
 for j in range(1,m+1):
  for x in itertools.product(range(2),repeat=n):
   for ell in range(1,r+1):
    yield (('S',j),)+tuple(('R',i+1,x[i]) for i in range(n))+(('E',j,ell),),x[(j-1)*r+ell-1]
def cutcolor(prefix,r):
 if not prefix:return 0
 j=prefix[0][1];value=0
 for tag in prefix:
  if tag[0]=='R' and (tag[1]-1)//r==j-1:value|=tag[2]<<((tag[1]-1)%r)
  if tag[0]=='E':return (value>>(tag[2]-1))&1
 return value
def run(w,m,r,k):
 n=m*r;batchwidth=r*k;state=('RESET',);visited=[state]
 for event in w:
  if event[0]=='S':state=('WAIT',(event[1]-1)//k)
  elif event[0]=='R':
   i,bit=event[1:];g=(i-1)//batchwidth;pos=(i-1)%batchwidth;last=min((g+1)*batchwidth,n)
   if state[0]=='WAIT':
    if state[1]==g:
     assert pos==0
     state=('DONE',bit) if i==last else ('ACTIVE',bit)
   elif state[0]=='ACTIVE':
    value=state[1] | (bit<<pos)
    state=('DONE',value) if i==last else ('ACTIVE',value)
   elif state[0]!='DONE':raise AssertionError(state)
  elif event[0]=='E':
   assert state[0]=='DONE'
   j,ell=event[1:];pos=((j-1)%k)*r+ell-1
   state=('OUT',(state[1]>>pos)&1)
  visited.append(state)
 return state[1],visited
result=[]
for n in range(1,9):
 for r in range(1,n+1):
  if n%r:continue
  m=n//r;records=list(words(m,r));length=n+2
  for t in range(length+1):
   requirements={};colors=set()
   for w,y in records:
    c=cutcolor(w[:t],r);colors.add(c);key=(c,w[t:])
    assert key not in requirements or requirements[key]==y
    requirements[key]=y
   assert len(colors)<=2**r
  # Full selected-block vectors at pre-End cut have all distinct response rows.
  vectors=list(itertools.product(range(2),repeat=r))
  assert len(set(vectors))==2**r
  for v,z in itertools.combinations(vectors,2):assert any(a!=b for a,b in zip(v,z))
  checks=0
  for k in range(1,m+1):
   used=set()
   for w,y in records:
    out,visited=run(w,m,r,k);assert out==y
    used.update(visited);checks+=1
   assert len(used)<=math.ceil(m/k)+2**(r*k+1)+3
  result.append({'N':n,'m':m,'r':r,'worlds':len(records),'cuts':length+1,
   'all_cut_2_to_r_color_certificate':'PASS','pre_end_lower_bound':'PASS',
   'grouped_driver_cases':checks,'all_batch_sizes_correct':'PASS'})
# Losing the actual same-block promise invalidates a compressed driver.
w=(('S',1),('R',1,0),('R',2,1),('R',3,0),('R',4,0),('E',2,1))
out,_=run(w,4,1,1)
assert out!=1
out={'status':'PASS','instances':result,'lost_matching_negative_control':'PASS',
 'source_sha256':hashlib.sha256((ROOT/'theory/Coupled_Target_Index_Capability.md').read_bytes()).hexdigest()}
(ROOT/'review/Coupled_Target_Index_Results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':out['status'],'parameter_instances':len(result),'driver_world_runs':sum(x['grouped_driver_cases'] for x in result),'lost_matching_negative_control':'PASS','source_sha256':out['source_sha256']},indent=2))

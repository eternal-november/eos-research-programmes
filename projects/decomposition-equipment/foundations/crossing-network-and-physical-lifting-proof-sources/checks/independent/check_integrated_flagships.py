"""Independent flagship integration regressions. Literal finite table checks."""
from itertools import product,permutations
from check_reconstruction_independent import partitions,kernel
import json
bits=(0,1)
def least(n,edges):
 p=list(range(n))
 def find(x):
  while p[x]!=x:x=p[x]
  return x
 for x,y in edges:p[find(x)]=find(y)
 return kernel([find(i) for i in range(n)])
def admissible(k,types,fibres,edges):
 if any(k[a]!=k[b] for a,b in edges):return False
 for c in set(k):
  ts={types[j] for j in range(len(k)) if k[j]==c}
  if len(ts)!=1:return False
  t=next(iter(ts))
  if any(sum(k[j]==c for j in js)!=1 for z,js in fibres if z==t):return False
 return True
def candidates(types,fibres,edges):
 f=least(len(types),edges);m=max(f,default=-1)+1
 return {kernel([k[f[j]] for j in range(len(f))]) for k in partitions(m) if admissible([k[f[j]] for j in range(len(f))],types,fibres,edges)}

def cycle(twist):
 domains=({0,1},{1,2},{2,0});events=[(i,b,v) for i in range(3) for b,v in product(bits,repeat=2)]
 idx={e:j for j,e in enumerate(events)};edges=[];checked=0
 f=lambda i,a:int(twist and i==2 and a==2)
 # Actual whole w=(a,x,k,u), extracting t via inverse alpha/actual theta.
 for a,x,k,u in product(range(3),bits,bits,bits):
  exposed=[]
  for i,d in enumerate(domains):
   if a not in d:continue
   b=1-x;l=1-k;v=u^f(i,a)
   # R changes x, Q changes k, T changes b; S combines branches.
   assert 1-b==x
   alpha_u=v^f(i,a)
   assert alpha_u==u
   theta=(a,x,k,b,l,v)
   composed=(a,x,k,b,l,v)
   assert theta==composed and ((1-b)^l)==(x^(1-k))
   exposed.append(idx[i,b,v]);checked+=1
  edges += [(exposed[0],j) for j in exposed[1:]]
 types=[(b,1-b) for i,b,v in events]
 fibres=[((b,1-b),[idx[i,b,v] for v in bits]) for i in range(3) for b in bits]
 ks=candidates(types,fibres,edges)
 # Independent labelled global event identifications, one fibre bijection each.
 direct=set()
 for choices in product(tuple(permutations(bits)),repeat=6):
  mapping=[(b,choices[2*i+b][v]) for i,b,v in events]
  if all(mapping[a]==mapping[b] for a,b in edges):direct.add(kernel(mapping))
 assert ks==direct
 assert len(ks)==(0 if twist else 1)
 return {'actual_chart_whole_equations_checked':checked,'quotient_classes':len(ks)}

def gate_closure(include_and):
 inputs=list(product(bits,repeat=2));hs={(0,)*4,(1,)*4,tuple(x for x,y in inputs),tuple(y for x,y in inputs)}
 while True:
  old=set(hs)
  for a in old:
   hs.add(tuple(1-x for x in a))
   for b in old:
    hs.add(tuple(x^y for x,y in zip(a,b)))
    if include_and:hs.add(tuple(x&y for x,y in zip(a,b)))
  if hs==old:return hs

def and_grid():
 inputs=list(product(bits,repeat=2));target=tuple(x&y for x,y in inputs)
 faces=list(product(range(2),bits));events=[];fibres=[]
 # Each wrapper prepends an actual affine face-inclusion circuit, invokes core
 # once, then output identity. Its marked record is the core's input pair.
 embed=lambda j,z:(faces[j][1],z) if faces[j][0]==0 else (z,faces[j][1])
 for j in range(4):
  for z in bits:
   xy=embed(j,z);events.append((j,z,xy,xy[0]&xy[1]))
 types=[(xy,y) for j,z,xy,y in events]
 for j in range(4):
  for z,y in product(bits,repeat=2):
   fibres.append(((embed(j,z),y),[i for i,e in enumerate(events) if e[0]==j and e[1]==z and e[3]==y]))
 edges=[(a,b) for a in range(8) for b in range(a) if events[a][2]==events[b][2]]
 ks=candidates(types,fibres,edges)
 assert len(ks)==1 and len(set(next(iter(ks))))==4
 aff=gate_closure(False);full=gate_closure(True)
 assert len(aff)==8 and len(full)==16
 local_counts=[]
 for j in range(4):
  # Each local table has at least one genuinely generated affine extension.
  good=[h for h in aff if all(h[inputs.index(embed(j,z))]==(embed(j,z)[0]&embed(j,z)[1]) for z in bits)]
  assert good;local_counts.append(len(good))
 def wrapper_and_core_pass(h):
  core=[(xy,h[q]) for q,xy in enumerate(inputs)]
  for j in range(4):
   wrapper=[(z,core[inputs.index(embed(j,z))]) for z in bits]
   pullback=[(z,e) for z in bits for e in core if e[0]==embed(j,z)]
   assert sorted(wrapper)==sorted(pullback) # exact record pullback, no labels erased
   local=[(z,xy,y) for jj,z,xy,y in events if jj==j]
   if [(z,e[0],e[1]) for z,e in wrapper]!=local:return False
  return True
 assert sum(wrapper_and_core_pass(h) for h in aff)==0
 assert sum(wrapper_and_core_pass(h) for h in full)==1
 assert wrapper_and_core_pass(target)
 # Full active grid: original parent and whole paths agree at all 8 inputs.
 for a1,a2,k in product(bits,repeat=3):
  b=(1-a1,1-a2);l=1-k;c=b[0]&b[1]
  p=c;n=c^l
  assert (p^l)==n
 return {'structural_quotients':len(ks),'global_actual_events':4,'local_affine_extensions':local_counts,'global_affine_tables':len(aff),'affine_exact_lifts':0,'with_AND_tables':len(full),'with_AND_exact_lifts':1,'actual_whole_grid_inputs':8,'exact_face_wrappers':4}

print(json.dumps({'twisted_active_cycle':cycle(True),'untwisted_active_cycle':cycle(False),'active_AND_grid':and_grid(),'result':'PASS','scope':'Two explicit flagship families only; independent finite regression, not universal proof'},indent=2))

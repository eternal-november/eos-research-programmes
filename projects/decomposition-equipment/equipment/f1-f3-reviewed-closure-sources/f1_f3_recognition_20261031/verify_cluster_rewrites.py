#!/usr/bin/env python3
"""Bounded genuine R/L/UL/UR tree rewriting, not a B3 coherence proof."""
import itertools as I, json, functools, collections
if not __debug__: raise RuntimeError('Assertions required')
C=collections.Counter()
def comps(v):
 if v==0: yield (); return
 for z in range(1,v+1):
  for t in comps(v-z): yield (z,)+t
def rows(s):
 x=0; r=[]
 for z in s: r.append(tuple(range(x,x+z))); x+=z
 return r
def typ(s,U): return tuple(z for row in rows(s) if (z:=len(set(row)&set(U))))
def mat(s,p,n): return tuple(tuple(sum(p[x]==j for x in row) for j in range(n)) for row in rows(s))
def node(s,p,l,r): return ('C',s,tuple(p),l,r)
def leaf(s,unit=False): return ('U' if unit else 'I',s)
def shapes(n):
 if n==1: yield None
 for k in range(1,n):
  for l in shapes(k):
   for r in shapes(n-k): yield (k,l,r)
def build(s,p,n,shape,units):
 if shape is None: return leaf(s,units[0])
 k,l,r=shape; q=tuple(int(j>=k) for j in p)
 U=tuple(x for x,c in enumerate(q) if c==0); V=tuple(x for x,c in enumerate(q) if c==1)
 return node(s,q,build(typ(s,U),tuple(p[x] for x in U),k,l,units[:k]),build(typ(s,V),tuple(p[x]-k for x in V),n-k,r,units[k:]))
@functools.lru_cache(None)
def ev(t):
 if t[0]=='I': return (tuple(0 for _ in range(sum(t[1]))),1)
 if t[0]=='U': assert t[1]==(); return ((),0)
 _,s,p,l,r=t; a,n=ev(l); b,m=ev(r); inds=[0,0]; out=[]
 for c in p:
  out.append((a if c==0 else b)[inds[c]]+(0 if c==0 else n)); inds[c]+=1
 return tuple(out),n+m
@functools.lru_cache(None)
def steps(t):
 if t[0]!='C': return ()
 _,s,p,l,r=t; out=[]
 # Literal binary canonical-placement rule L.
 canon=tuple(c for row in rows(s) for c in ([0]*sum(p[x]==0 for x in row)+[1]*sum(p[x]==1 for x in row)))
 if canon!=p: out.append(('L',node(s,canon,l,r)))
 if l[0]=='U': out.append(('UL',r))
 if r[0]=='U': out.append(('UR',l))
 if l[0]=='C':
  _,ss,pp,a,b=l
  # Flatten just the three corollas to recover actual A/B/C subsets.
  idx=0; tri=[]
  for c in p:
   if c: tri.append(2)
   else: tri.append(pp[idx]); idx+=1
  q=tuple(int(c!=0) for c in tri); V=tuple(x for x,c in enumerate(tri) if c!=0)
  inner=tuple(tri[x]-1 for x in V)
  out.append(('R',node(s,q,a,node(typ(s,V),inner,b,r))))
 for name,u in steps(l): out.append(('left/'+name,node(s,p,u,r)))
 for name,u in steps(r): out.append(('right/'+name,node(s,p,l,u)))
 return tuple(out)
@functools.lru_cache(None)
def normal(t):
 st=steps(t)
 return normal(st[0][1]) if st else t
seen=set()
for v in range(5):
 for s in comps(v):
  for n in range(1,5):
   for p in I.product(range(n),repeat=v):
    empty=[j for j in range(n) if j not in p]
    for unitbits in I.product((False,True),repeat=len(empty)):
     units=[False]*n
     for j,b in zip(empty,unitbits): units[j]=b
     for shape in shapes(n): seen.add(build(s,p,n,shape,units))
# Include every descendant: local rewrites may alter canonical vertex placements.
queue=list(seen)
for t in queue:
 for _,u in steps(t):
  if u not in seen: seen.add(u); queue.append(u)
bysem={}
for t in queue:
 p,n=ev(t); key=(t[1],mat(t[1],p,n),n); nf=normal(t)
 assert ev(nf)[1]==n and mat(t[1],ev(nf)[0],n)==key[1]
 assert key not in bysem or bysem[key]==nf
 bysem[key]=nf
 st=steps(t)
 for name,u in st:
  pu,nu=ev(u)
  assert u[1]==t[1] and nu==n and mat(u[1],pu,nu)==key[1]
  assert normal(u)==nf
  C['rule_steps_'+name.split('/')[-1]]+=1
 for (a,u),(b,w) in I.combinations(st,2):
  assert normal(u)==normal(w)
  C['local_peaks']+=1
  if 'L' in (a.split('/')[-1],b.split('/')[-1]): C['local_peaks_involving_L']+=1
C['trees']=len(seen); C['semantic_normal_forms']=len(bysem)
print(json.dumps({'status':'PASS','bounds':{'vertices':4,'initial_binary_leaf_positions':4,'unit_leaves':'all eligible empty positions','grades':'terminal category','rules':['R','L','UL','UR']},'checks':dict(sorted(C.items())),'not_proved':['B3 O_L/MOut/MIn coherence','all critical overlap templates','decoration rules','nonterminal grade rewrite typing']},sort_keys=True,indent=2))

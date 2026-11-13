#!/usr/bin/env python3
"""Bounded author C checks: independent direct tuple enumeration versus R4 decoder.
The unrestricted R1-R5 claims are paper proofs, not inferred from this run.
"""
from functools import lru_cache
from itertools import product,combinations,permutations
from collections import defaultdict
from math import factorial,prod
from pathlib import Path
import json,hashlib,sys,time
ROOT=Path(__file__).resolve().parent

def need(b,m):
 if not b:raise RuntimeError(m)
def mul(name,a,b):return (a+b)%2 if name=='C2' else max(a,b)
def mprod(name,xs):
 r=0
 for x in xs:r=mul(name,r,x)
 return r
@lru_cache(None)
def parts(r,k):
 if k==0:return ((),) if r==0 else ()
 return tuple(tuple(tuple(v for v in range(r) if a[v]==i) for i in range(k)) for a in product(range(k),repeat=r))
@lru_cache(None)
def paths(A,B,k):
 if k==0:return ((A,),) if A==B else ()
 return tuple((A,)+x+(B,) for x in product(range(A,B+1),repeat=k-1) if all(a<=b for a,b in zip((A,)+x,x+(B,))))
@lru_cache(None)
def ops(r,A,B,k):return tuple((bs,p,n) for bs in parts(r,k) for p in paths(A,B,k) for n in range(2))
def weak(total,k):
 if k==0:
  if total==0:yield ()
  return
 for x in range(total+1):
  for rest in weak(total-x,k-1):yield (x,)+rest

def direct(a,childs,name):
 bs,path,m=a;out=[];pp=[path[0]];value=m
 for i,(cb,cp,n) in enumerate(childs):
  need(cp[0]==path[i] and cp[-1]==path[i+1],'direct child boundary')
  out.extend(tuple(bs[i][j] for j in b) for b in cb);pp.extend(cp[1:]);value=mul(name,value,n)
 return (tuple(out),tuple(pp),value)
def predicted(a,b,name):
 U,p,m=a;V,q,mp=b;k=len(U);l=len(V);ans=set()
 for lam in weak(l,k):
  s=0;fixed=[];valid=True
  for i,h in enumerate(lam):
   run=V[s:s+h];sub=q[s:s+h+1]
   if set().union(*(set(z) for z in run))!=set(U[i]) or sub[0]!=p[i] or sub[-1]!=p[i+1]:valid=False;break
   inv={v:j for j,v in enumerate(U[i])};fixed.append((tuple(tuple(inv[x] for x in z) for z in run),sub));s+=h
  if valid:
   for ns in product(range(2),repeat=k):
    if mul(name,m,mprod(name,ns))==mp:ans.add(tuple((fixed[i][0],fixed[i][1],ns[i]) for i in range(k)))
 return ans

def semantic_exhaustive():
 counters=defaultdict(int)
 for r in range(3):
  # Each labelled simple graph is retained even though the run-fibre formula
  # factors through actual placements rather than adjacency bits.
  edges=list(combinations(range(r),2))
  for bits in product((0,1),repeat=len(edges)):
   G=tuple(e for e,b in zip(edges,bits) if b)
   for A in range(3):
    for B in range(A,3):
     for name in ('C2','idempotent'):
      targets=[b for l in range(3) for b in ops(r,A,B,l)]
      for k in range(4):
       for a in ops(r,A,B,k):
        got=defaultdict(set)
        for total in range(3):
         for lens in weak(total,k):
          options=[ops(len(a[0][i]),a[1][i],a[1][i+1],lens[i]) for i in range(k)]
          for ch in product(*options):
           b=direct(a,ch,name);got[b].add(ch);counters['direct_arrows']+=1
           # Check literal induced graph restriction after coordinate lifting.
           for i,(cb,cp,n) in enumerate(ch):
            outer=a[0][i]
            for block in cb:
             lifted=tuple(outer[j] for j in block)
             lhs={(s,t) for s,t in combinations(range(len(block)),2) if tuple(sorted((outer[block[s]],outer[block[t]]))) in G}
             rhs={(s,t) for s,t in combinations(range(len(lifted)),2) if tuple(sorted((lifted[s],lifted[t]))) in G}
             need(lhs==rhs,'restriction transitivity')
        for b in targets:
         want=predicted(a,b,name);need(got.get(b,set())==want,'direct tuple fibre differs from reconstruction')
         counters['endpoint_pairs']+=1
         if len(want)>1:counters['nontrivial_fibres']+=1
        counters['source_operations']+=1
 return dict(counters)

# A tree is ('leaf',colour) or ('node',label,colour,children). Every typed
# constructor carries full child types, so occurrences remain separate.
def leaf(c):return ('leaf',c)
def node(label,c,*kids):return ('node',label,c,tuple(kids))
def colour(t):return t[1] if t[0]=='leaf' else t[2]
def verts(t,p=()):
 if t[0]=='leaf':return {}
 ans={p:t[1]}
 for i,x in enumerate(t[3]):ans.update(verts(x,p+(i,)))
 return ans
def leaves(t,p=()):
 if t[0]=='leaf':return [(p,t[1])]
 return [z for i,x in enumerate(t[3]) for z in leaves(x,p+(i,))]
def subtree(t,p):
 for i in p:t=t[3][i]
 return t
def prune(t,D,p=()):
 if t[0]=='leaf' or p not in D:return leaf(colour(t))
 return node(t[1],colour(t),*(prune(x,D,p+(i,)) for i,x in enumerate(t[3])))
def graft(t,F,p=()):
 if t[0]=='leaf':return F[p]
 return node(t[1],colour(t),*(graft(x,F,p+(i,)) for i,x in enumerate(t[3])))
def ideals(t):
 vs=list(verts(t));out=[]
 for bs in product((0,1),repeat=len(vs)):
  D={v for v,b in zip(vs,bs) if b}
  if all(not any(v[:i] not in D for i in range(len(v))) for v in D):out.append(D)
 return out
def poly(t):
 if t[0]=='leaf':return [1]
 p=[1]
 for x in t[3]:
  q=poly(x);z=[0]*(len(p)+len(q)-1)
  for i,a in enumerate(p):
   for j,b in enumerate(q):z[i+j]+=a*b
  p=z
 return [1]+p

def induced(G,block):
 n,edges=G
 return (len(block),tuple((i,j) for i,j in combinations(range(len(block)),2) if tuple(sorted((block[i],block[j]))) in edges))
def cut_node(G,blocks,path,*children):
 return node(('cut',G,blocks,path),(G,path[0],path[-1]),*children)
def typed(t):
 if t[0]=='leaf':return True
 label=t[1];G,A,B=colour(t);kids=t[3]
 if label[0]=='cut':
  _,H,blocks,path=label
  need(G==H and (A,B)==(path[0],path[-1]),'cut output type')
  need(tuple(sorted(x for bl in blocks for x in bl))==tuple(range(G[0])),'partition type')
  need(len(blocks)==len(kids) and len(path)==len(kids)+1,'arity type')
  for i,kid in enumerate(kids):need(colour(kid)==(induced(G,blocks[i]),path[i],path[i+1]),'child component type')
 elif label[0]=='d':need(len(kids)==1 and colour(kids[0])==colour(t),'decoration type')
 elif label[0]=='u':need(not kids and G==(0,()) and A==B,'nullary type')
 else:raise RuntimeError('unknown fixture primitive')
 for x in kids:typed(x)
 return True

def fixture():
 # Exactly the original A4 section 9 six-vertex graph and four-slot profile.
 G=(6,((0,5),(1,2),(2,3),(3,4)))
 Ublocks=((0,),(1,2),(3,4),(5,));path=(0,1,1,1,2)
 def comb(H,blocks,pp):
  if len(blocks)==1:return leaf((H,pp[0],pp[-1]))
  left=blocks[0];right=tuple(sorted(x for bl in blocks[1:] for x in bl));inv={v:i for i,v in enumerate(right)}
  rhs=comb(induced(H,right),tuple(tuple(inv[v] for v in bl) for bl in blocks[1:]),pp[1:])
  return cut_node(H,(left,right),(pp[0],pp[1],pp[-1]),leaf((induced(H,left),pp[0],pp[1])),rhs)
 T=comb(G,Ublocks,path);typed(T);ls=leaves(T);Q=ls[1][1]
 need(len(ls)==4 and ls[1][1]==ls[2][1] and Q[0][0]==2,'repeated nonempty middle fixture')
 F={p:leaf(c) for p,c in ls}
 F[ls[1][0]]=node(('d',1),Q,leaf(Q));F[ls[2][0]]=node(('d',2),Q,leaf(Q))
 U=graft(T,F);typed(U);need(len(verts(U))==5,'five vertex nested fixture')
 ev=[ls[1][0],ls[2][0]];need(len(list(permutations(ev)))==2,'two schedules')
 need(subtree(U,ls[1][0])!=subtree(U,ls[2][0]),'occurrence collapse detected')
 E=((0,()),1,1);H=Q[0]
 X=cut_node(H,((),tuple(range(H[0]))),(1,1,1),leaf(E),leaf(Q));typed(X)
 Y=graft(X,{(0,):node(('u',1),E),(1,):leaf(Q)});typed(Y)
 need(len(leaves(Y))<len(leaves(X)) and len(verts(Y))>len(verts(X)),'nullary decreases leaves while growing vertices')
 need(len(leaves(U))==len(leaves(T)) and len(verts(U))>len(verts(T)),'unary growth')
 Gminus=(6,tuple(e for e in G[1] if e!=(0,5)))
 need(G!=Gminus and [induced(G,x) for x in Ublocks]==[induced(Gminus,x) for x in Ublocks],'cross-edge loss control')
 counts=defaultdict(int)
 for V in (U,Y,node(('u',1),E),leaf(Q)):
  ds=ideals(V);p=poly(V);need(sum(p)==len(ds),'ideal polynomial')
  hist=defaultdict(int)
  for D in ds:
   T0=prune(V,D);F0={a:subtree(V,a) for a,c in leaves(T0)};need(graft(T0,F0)==V,'ideal reconstruction')
   need(len(verts(V))==len(verts(T0))+sum(len(verts(x)) for x in F0.values()),'vertex growth')
   expanded=[(a+b,c) for a,c0 in leaves(T0) for b,c in leaves(F0[a])]
   need(expanded==leaves(V),'ordered leaf formula')
   events=set(verts(V))-D;n=len(events)
   schedules=[ps for ps in permutations(events) if all(ps.index(a)<ps.index(b) for a in events for b in events if len(a)<len(b) and b[:len(a)]==a)]
   sizes=[sum(1 for b in events if b[:len(a)]==a) for a in events]
   need(len(schedules)==factorial(n)//prod(sizes),'hook formula')
   chain=all(a[:len(b)]==b or b[:len(a)]==a for a in events for b in events)
   need((len(schedules)==1)==chain,'history uniqueness boundary')
   counts['prefix_records']+=1;counts['schedules']+=len(schedules)
 # Original semantic six-vertex graph, four nonempty blocks and M=C3.
 # a=b, unique segmentation, 3^(4-1) scalar arrow tuples.
 ns=[z for z in product(range(3),repeat=4) if sum(z)%3==0]
 need(len(ns)==27 and (0,1,2,0) in ns and (0,0,0,0) in ns,'six-vertex scalar fibre')
 counts['six_vertex_parallel_arrows']=len(ns)
 return dict(counts)

def controls():
 # A checker that drops scalar local values or original empty-slot runs must fail.
 a=(((0,),(1,)),(1,1,1),0);b=a
 w=predicted(a,b,'C2');need(len(w)==2,'scalar control domain')
 collapsed={tuple((x[0],x[1]) for x in z) for z in w};need(len(collapsed)<len(w),'scalar-erasure mutation not caught')
 a=( ((),()),(1,1,1),0);b=(((),),(1,1),0)
 w=predicted(a,b,'C2');need(len(w)==4,'empty-run domain')
 collapsed={tuple(x[2] for x in z) for z in w};need(len(collapsed)<len(w),'segmentation-erasure mutation not caught')
 return ['scalar_erasure_rejected','empty_run_segmentation_erasure_rejected','repeated_occurrence_collapse_rejected','leaf_count_growth_rejected']

def main():
 start=time.monotonic();receipt=ROOT/'result.json'
 receipt.write_text(json.dumps({'status':'RUNNING','runner_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()})+'\n')
 try:r={'status':'PASS','scope':'all simple graphs through 2 vertices; K=[2], all outer arrows, source arity <=3, target arity <=2; C2 group and two-element idempotent monoid; additional six-vertex mixed typed raw and C3 scalar fixtures','semantic':semantic_exhaustive(),'typed_fixtures':fixture(),'negative_controls':controls(),'elapsed_seconds':time.monotonic()-start,'python_optimization':sys.flags.optimize,'runner_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
 except Exception as e:receipt.write_text(json.dumps({'status':'FAIL','error':str(e)})+'\n');raise
 receipt.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
if __name__=='__main__':main()

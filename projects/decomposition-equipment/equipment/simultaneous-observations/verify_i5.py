#!/usr/bin/env python3
"""Independent finite checks; standard library; output deterministic JSON."""
import hashlib,json,math,pathlib
ROOT=pathlib.Path(__file__).resolve().parent

def canon(keys):
 d={};return [d.setdefault(x,len(d)) for x in keys]
def blocks(p):return len(set(p))
def compose(f,g):return tuple(f[x] for x in g)
def monoid(k):
 e=tuple(range(k));a=(k-1,1)+tuple(range(1,k-1));b=(1,2)+(1,)*(k-2)
 closure={e};todo=[e]
 while todo:
  x=todo.pop()
  for g in (a,b):
   y=compose(x,g)
   if y not in closure:closure.add(y);todo.append(y)
 t=k-1;aa=[e]
 for i in range(t):aa.append(compose(aa[-1],a))
 forms=[('A',i,x) for i,x in enumerate(aa)]+[('B',i,compose(b,x)) for i,x in enumerate(aa)]+[('D',i,compose(compose(b,b),aa[i])) for i in range(t-1)]
 xs=[x for _,_,x in forms];assert len(set(xs))==3*k-2 and set(xs)==closure
 ix={x:i for i,x in enumerate(xs)};names={(s,i):j for j,(s,i,_) in enumerate(forms)}
 mul=[[ix[compose(x,y)] for y in xs] for x in xs]
 def delta(i):return ('D',i) if i<=t-2 else ('A',min(i,t))
 for u,(s,i,_) in enumerate(forms):
  for v,(r,j,_) in enumerate(forms):
   if s=='A': expected=(r,j) if i==0 else ('A',min(i+j,t) if r=='A' else t)
   elif s=='B': expected=('B',min(i+j,t)) if r=='A' else (delta(j) if r=='B' else ('B',j)) if i==0 else ('B',t)
   else:expected=delta(i+j) if r=='A' else ((('B',j) if r=='B' else ('D',j)) if i==0 else ('A',t))
   assert mul[u][v]==names[expected],(k,s,i,r,j,expected)
 return forms,mul,names

def cstep(p,m):
 sig=[set() for _ in p]
 for u,row in enumerate(m):
  for v,x in enumerate(row):sig[x].add((p[u],p[v]))
 return canon((p[i],frozenset(sig[i])) for i in range(len(p)))
def sstep(p,m):return canon((p[i],tuple(p[z] for z in m[i]),tuple(p[row[i]] for row in m)) for i in range(len(p)))
def sat(p,step,m):
 trace=[blocks(p)]
 while True:
  q=step(p,m)
  if q==p:return p,trace
  p=q;trace.append(blocks(p))
def scalar(k):
 fs,m,n=monoid(k);p=canon(i==0 for _,i,_ in fs);h=canon(i for _,i,_ in fs)
 assert sat(p,sstep,m)[0]==p
 q,tr=sat(p,cstep,m);assert q==h
 R=max(2,(k-3).bit_length());assert len(tr)-1==R,(k,tr,R)
 assert tr[1]==3
 for r,count in enumerate(tr[2:],2):assert count==min(k,2**r+2)
 assert m[n['A',1]][n['A',0]]==n['A',1] and m[n['A',1]][n['B',0]]==n['A',k-1]
 assert n['B',k-1] not in m[n['A',1]]
 for row in ('A','B'):
  candidates={u for u in range(len(fs)) if fs[u][1]==1 and any(m[u][v]==n[row,1] for v in range(len(fs)) if fs[v][1]==0)}
  assert candidates=={n[row,1]}
 schedule=[blocks(p)];z=p
 for _ in range(3):
  z,_=sat(z,sstep,m);z,_=sat(z,cstep,m);schedule.append(blocks(z))
 assert schedule==[2,k,2*k,3*k-2],(k,schedule)
 return {'k':k,'order':len(fs),'C_trace':tr,'C_rounds':R,'SC_sweeps':schedule}

def typed_n2(m,seed,contexts=True):
 """All active size types <=2, not a graph enumeration. Exact label templates."""
 n=len(m);types=[(1,),(2,),(1,1)];carriers=[[(i,) for i in range(n)],[(i,) for i in range(n)],[(i,j) for i in range(n) for j in range(n)]]
 index=[{x:i for i,x in enumerate(c)} for c in carriers]
 p=[canon(tuple(seed[x] for x in v) for v in c) for c in carriers]
 # (source, outer, ordered child sorts, grouping)
 cuts=[(0,0,(0,),(0,)),(1,1,(1,),(0,)),(2,1,(2,),(0,0)),(2,2,(0,0),(0,1))]
 records=[]
 import itertools
 for src,outer,children,g in cuts:
  rec=[]
  for ai,a in enumerate(carriers[outer]):
   for bis in itertools.product(*(range(len(carriers[c])) for c in children)):
    b=tuple(x for c,bi in zip(children,bis) for x in carriers[c][bi]);x=tuple(m[a[g[j]]][b[j]] for j in range(len(b)))
    rec.append((index[src][x],ai,bis))
  records.append(rec)
 trace=[[blocks(z) for z in p]]
 while True:
  keys=[[(p[s][i],) for i in range(len(c))] for s,c in enumerate(carriers)]
  for (src,outer,children,g),rec in zip(cuts,records):
   sig=[set() for _ in carriers[src]]
   for x,a,bs in rec:sig[x].add((p[outer][a],)+tuple(p[c][b] for c,b in zip(children,bs)))
   for x in range(len(sig)):keys[src][x]+=(frozenset(sig[x]),)
   if not contexts:continue
   # All one-hole grafts, including a varying WHOLE outer tuple.
   for bs in itertools.product(*(range(len(carriers[c])) for c in children)):
    b=tuple(x for c,bi in zip(children,bs) for x in carriers[c][bi])
    for ai,a in enumerate(carriers[outer]):
     out=index[src][tuple(m[a[g[j]]][b[j]] for j in range(len(b)))];keys[outer][ai]+=(p[src][out],)
   for pos,child in enumerate(children):
    other=[j for j in range(len(children)) if j!=pos]
    for ai,a in enumerate(carriers[outer]):
     for rest in itertools.product(*(range(len(carriers[children[j]])) for j in other)):
      for bi in range(len(carriers[child])):
       bs=dict(zip(other,rest));bs[pos]=bi;b=tuple(x for j,c in enumerate(children) for x in carriers[c][bs[j]])
       out=index[src][tuple(m[a[g[j]]][b[j]] for j in range(len(b)))];keys[child][bi]+=(p[src][out],)
  q=[canon(z) for z in keys]
  if q==p:break
  p=q;trace.append([blocks(z) for z in p])
 return {'active_size_types':types,'carrier_sizes':list(map(len,carriers)),'joint_records':list(map(len,records)),'combined_trace':trace,'final_partitions':p}

def channels():
 fs,m,n=monoid(4);p=len(m);pairs=[(x,y) for x in range(p) for y in range(p)];mm=[[m[a][c]*p+m[b][d] for c,d in pairs] for a,b in pairs]
 seed=canon(fs[x][1]==0 for x,y in pairs);C,tr=sat(seed,cstep,mm);both=canon((seed[i],seed[y*p+x]) for i,(x,y) in enumerate(pairs))
 CT,_=sat(both,cstep,mm);TC=canon((C[i],C[y*p+x]) for i,(x,y) in enumerate(pairs));assert CT==TC
 z=seed;trace=[blocks(z)]
 while True:
  sc=cstep(sstep(z,mm),mm);q=canon((sc[i],sc[y*p+x]) for i,(x,y) in enumerate(pairs))
  if q==z:break
  z=q;trace.append(blocks(z))
 assert blocks(z)==p*p
 # Actual permutation conjugation on 2*k boundary points.
 swap=tuple(range(4,8))+tuple(range(4))
 for x,y in pairs:
  diag=fs[x][2]+tuple(4+v for v in fs[y][2]);reverse=fs[y][2]+tuple(4+v for v in fs[x][2]);assert compose(swap,compose(diag,swap))==reverse
 return {'unary_carrier':p*p,'C_trace':tr,'CT_TC_blocks':blocks(CT),'joint_trace':trace,'block_conjugation_checks':p*p}

def diagnostics():
 # Exact shared-parent obstruction, even though both marginal equations lift.
 fs,m,n=monoid(4);found=None
 for a in range(len(m)):
  for b in range(a+1,len(m)):
   for v in range(len(m)):
    x=m[a][v];y=m[b][v]
    left={u for u in (a,b) if m[u][v]==x};right={u for u in (a,b) if m[u][v]==y}
    if left and right and not left&right:found={'parent_class':[fs[a][:2],fs[b][:2]],'child':fs[v][:2],'sources':[fs[x][:2],fs[y][:2]],'candidate_sets':[sorted(left),sorted(right)]};break
   if found:break
  if found:break
 assert found
 # Six-state equivariance counterexample.
 rel=[{2,5},{3,4},set(),set(),set(),set()];tau=[0,1,2,4,3,5];P=[0,0,1,1,2,2]
 def step(P):return canon((P[i],frozenset(P[j] for j in rel[i])) for i in range(6))
 assert step(P)==P
 T=canon((P[i],P[tau[i]]) for i in range(6));assert T[0]==T[1] and step(T)[0]!=step(T)[1]
 assert all({tau[j] for j in rel[i]}==rel[tau[i]] for i in range(6))
 return {'shared_parent_failure':found,'equivariant_six_state':{'P':P,'T_P':T,'C_T_P':step(T)}}

def extra_checks():
 import itertools
 fs,m,n=monoid(4);p=len(m)
 # All scalar rank-two shared-parent records and literal channel pairing.
 local=[];counts={}
 for a,b,c in itertools.product(range(p),repeat=3):
  src=(m[a][b],m[a][c]);local.append((src,(a,b,c)));counts[src]=counts.get(src,0)+1
 globalcounts={}
 for (sx,wx),(sy,wy) in itertools.product(local,repeat=2):
  src=tuple(zip(sx,sy));w=tuple(zip(wx,wy))
  assert all((m[w[0][0]][w[j][0]],m[w[0][1]][w[j][1]])==src[j-1] for j in (1,2))
  globalcounts[src]=globalcounts.get(src,0)+1
 assert all(globalcounts[tuple(zip(x,y))]==counts[x]*counts[y] for x,y in itertools.product(counts,repeat=2))
 # Active positional composition retains empties; branch multiplication is ordered.
 def graft(parent,children):
  out=[]
  for a,child in zip(parent,children):
   assert a is not None or all(b is None for b in child)
   out.extend(None if b is None else m[a][b] for b in child)
  return tuple(out)
 parent=(None,n['B',0],None,n['A',1]);children=((None,None),(n['A',1],None,n['D',0]),(),(None,n['B',0]))
 output=graft(parent,children)
 assert output==(None,None,n['B',1],None,n['B',0],None,n['A',3])
 # Associativity for every label triple, including a shared parent with two branches.
 for a,b,c,d in itertools.product(range(p),repeat=4):
  assert (m[m[a][b]][c],m[m[a][b]][d])==(m[a][m[b][c]],m[a][m[b][d]])
 # Full profile tags explicitly prohibit identification even with equal empty-erased tuples.
 tag1=('frame0','graph2',(0,1,0,1),'grade-id');tag2=('frame0','graph2',(1,0,1),'grade-id');tag3=('frame1','graph2',(0,1,0,1),'grade-id')
 assert len({(tag, (n['A',0],n['A',0])) for tag in (tag1,tag2,tag3)})==3
 # Nontrivial group quotient with both channels: Z4^2 -> Z2^2.
 pairs=list(itertools.product(range(4),repeat=2));gm=[[( (a+c)%4)*4+(b+d)%4 for c,d in pairs] for a,b in pairs]
 group=typed_n2(gm,canon((a%2,b%2) for a,b in pairs))
 assert group['combined_trace']==[[4,4,16]]
 return {'twochannel_shared_parent_records':len(local)**2,'twochannel_sources':len(globalcounts),'fixed_source_fibre_product_count_checks':len(globalcounts),'empty_position_graft_output':output,'associativity_two_branch_checks':p**4,'distinct_profile_tags':3,'group_twochannel_N2':group}

def modular_control():
 K=[(0,0,0),(0,0,2),(0,1,2),(0,2,0),(2,0,2),(2,1,2),(2,2,0),(2,2,2)]
 ix={v:i for i,v in enumerate(K)};m=[[ix[compose(a,b)] for b in K] for a in K]
 P=canon(i==2 for i in range(8));Q=canon(i in (2,5) for i in range(8));R=canon(zip(P,Q))
 for p in (P,Q):assert sstep(p,m)==p and cstep(p,m)==p
 assert sstep(R,m)==R and cstep(R,m)!=R
 assert m[0][5]==0 and all(m[u][5]!=1 for u in range(8))
 cuts=[typed_n2(m,p,False)['combined_trace'] for p in (P,Q)]
 assert all(tr[1][2]>4 for tr in cuts)
 return {'unary_local_blocks':[blocks(P),blocks(Q)],'combined_blocks':blocks(R),'combined_C_blocks':blocks(cstep(R,m)),'N2_C_traces':cuts,'scope':'local optimum counterexample is unary N1 ONLY; N2 local seeds not stable'}

def main():
 pins={f:hashlib.sha256((ROOT/f).read_bytes()).hexdigest() for f in ['i5_joint_repair_theorem.md', 'concrete_model_gate.md', 'model_and_core_comparison.md', 'monoid_repair_theorem.md', 'profile_schemata_theorem.md', 'repair_calculus.md', 'modular_repair_theorem.md', 'baseline_comparison.md']}
 fs,m,n=monoid(4)
 result={'scope':'finite checks only; active-size templates are not all old graph profiles','source_pins':pins,'extra':extra_checks(),'modular_control':modular_control(),'scalar':[scalar(k) for k in range(4,65)],'scalar_N2':typed_n2(m,canon(i==0 for _,i,_ in fs)),'scalar_N2_C_only':typed_n2(m,canon(i==0 for _,i,_ in fs),False),'channels':channels(),'diagnostics':diagnostics(),'group_N2':typed_n2([[(a+b)%4 for b in range(4)] for a in range(4)],[0,1,0,1])}
 assert result['scalar_N2']['combined_trace'][-1]==[10,10,100]
 print(json.dumps(result,indent=2,sort_keys=True))
if __name__=='__main__':main()

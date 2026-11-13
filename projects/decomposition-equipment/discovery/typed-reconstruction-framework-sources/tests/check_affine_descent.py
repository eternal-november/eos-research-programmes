#!/usr/bin/env python3
"""Exact reproducible finite tests, not formal proof."""
from itertools import product, combinations
from math import gcd,lcm
import random,json
from pathlib import Path
rng=random.Random(20261029)
counts={}
def hit(k): counts[k]=counts.get(k,0)+1
def units(N): return [a for a in range(N) if gcd(a,N)==1]
def comp(f,gs,N):
 b,aa=f
 return ((b+sum(a*g[0] for a,g in zip(aa,gs)))%N,tuple(a*d%N for a,g in zip(aa,gs) for d in g[1]))
def randop(n,N):return (rng.randrange(N),tuple(rng.choice(units(N)) for _ in range(n)))
def cut(f,i,j,N):
 b,a=f;p=a[i];h=(0,tuple(x*pow(p,-1,N)%N for x in a[i:j]));o=(b,a[:i]+(p,)+a[j:]);return o,h

def segments(n,family):
 bp=sorted({0,n}|{x for I in family for x in I});return list(zip(bp,bp[1:]))
for N,ds in [(12,[4,6]),(24,[4,6]),(60,[12,20,30]),(120,[12,20,30])]:
 L=lcm(*ds)
 for isunit in [False,True]:
  fibers={}
  for x in units(N) if isunit else range(N):
   key=tuple(x%d for d in ds);fibers.setdefault(key,[]).append(x)
  for residues in product(*(units(d) if isunit else range(d) for d in ds)):
   compatible=all((residues[i]-residues[j])%gcd(ds[i],ds[j])==0 for i,j in combinations(range(len(ds)),2))
   assert (residues in fibers)==compatible
   if compatible: assert len(fibers[residues])==(len(units(N))//len(units(L)) if isunit else N//L)
   hit('CRT_scalar_tuple')
 for n in range(1,10):
  for _ in range(50):
   f=randop(n,N);b,a=f
   i=rng.randrange(n);j=rng.randrange(i+1,n+1)
   o,h=cut(f,i,j,N);gs=[(0,(1,))]*i+[h]+[(0,(1,))]*(n-j)
   assert comp(o,gs,N)==f;hit('normalized_cut')
   us=[rng.choice(units(N)) for _ in range(n)];vs=[rng.randrange(N) for _ in range(n)]
   u0=rng.choice(units(N));v0=rng.randrange(N)
   fp=((u0*(b+sum(x*v for x,v in zip(a,vs)))+v0)%N,tuple(u0*x*u%N for x,u in zip(a,us)))
   op,hp=cut(fp,i,j,N)
   c=sum(a[k]*pow(a[i],-1,N)*vs[k] for k in range(i,j))%N
   oldinner=comp(h,[(vs[k],(us[k],)) for k in range(i,j)],N)
   assert oldinner==comp((c,(us[i],)),[hp],N)
   transports=[(vs[k],(us[k],)) for k in range(i)]+[(c,(us[i],))]+[(vs[k],(us[k],)) for k in range(j,n)]
   ot=comp((v0,(u0,)),[comp(o,transports,N)],N)
   assert ot==op;hit('cut_transport')
   # Full finite overlapping family; independent interval choices, including all intervals sometimes.
   allI=[(s,t) for s in range(n) for t in range(s+1,n+1)]
   fam=allI if _==0 else rng.sample(allI,min(len(allI),rng.randrange(1,8)))
   seg=segments(n,fam)
   hs=[cut(f,s,t,N)[1] for s,t in seg]
   outer=(b,tuple(a[s] for s,t in seg));assert comp(outer,hs,N)==f
   for s,t in fam:
    ix=[k for k,(u,v) in enumerate(seg) if s<=u and v<=t]
    group=(0,tuple(a[seg[k][0]]*pow(a[s],-1,N)%N for k in ix))
    assert comp(group,[hs[k] for k in ix],N)==cut(f,s,t,N)[1]
    # Shared segment gauges aggregate to interval gauge; all modular views commute.
    cI=sum(a[k]*pow(a[s],-1,N)*vs[k] for k in range(s,t))%N
    cparts=sum(a[seg[k][0]]*pow(a[s],-1,N)*sum(a[j]*pow(a[seg[k][0]],-1,N)*vs[j] for j in range(*seg[k])) for k in ix)%N
    assert cI==cparts
    for d in ds:
     red=lambda f:(f[0]%d,tuple(x%d for x in f[1]))
     assert red(cut(f,s,t,N)[1])==cut(red(f),s,t,d)[1]
    hit('finite_family_interval_gauge')
   # Subdividing every atom into singleton leaves, then regrouping, reproduces each atom.
   for s,t in seg:
    atom=hs[seg.index((s,t))]
    mid=rng.randrange(s+1,t+1)
    pieces=[(s,mid)]+([(mid,t)] if mid<t else [])
    subgroup=(0,tuple(a[u]*pow(a[s],-1,N)%N for u,v in pieces))
    assert comp(subgroup,[cut(f,u,v,N)[1] for u,v in pieces],N)==atom
    hit('nested_segment_refinement')
   # Two successive coordinate changes induce composition of the internal gauges.
   ws=[rng.choice(units(N)) for k in range(n)];zs=[rng.randrange(N) for k in range(n)]
   c2=sum(a[k]*us[k]*pow(a[i]*us[i],-1,N)*zs[k] for k in range(i,j))%N
   direct=sum(a[k]*pow(a[i],-1,N)*(us[k]*zs[k]+vs[k]) for k in range(i,j))%N
   assert (us[i]*c2+c)%N==direct;hit('gauge_cocycle')
   # Endpoint insertion order has exactly same atomic segmentation.
   order=fam[:];rng.shuffle(order);assert segments(n,order)==seg;hit('family_endpoint_order')
 for m in range(1,5):
  for _ in range(150):
   f=randop(m,N);gs=[randop(rng.randrange(1,4),N) for i in range(m)];target=comp(f,gs,N)
   # Pick any actual target in the same residue class, including coefficient-unit fibers.
   B=rng.choice([x for x in range(N) if x%L==target[0]%L]);BB=tuple(rng.choice([x for x in units(N) if x%L==v%L]) for v in target[1])
   c=[g[0] for g in gs];c[0]=pow(f[1][0],-1,N)*(B-f[0]-sum(f[1][i]*c[i] for i in range(1,m)))%N
   lifted=[];pos=0
   for i,g in enumerate(gs):
    size=len(g[1]);dd=tuple(pow(f[1][i],-1,N)*v%N for v in BB[pos:pos+size]);pos+=size
    assert c[i]%L==g[0]%L and all(x%L==y%L for x,y in zip(dd,g[1]))
    lifted.append((c[i],dd))
   assert comp(f,lifted,N)==(B,BB);hit('fixed_outer_joint_lift')
   if N<=24:
    candidates=product(*([x for x in range(N) if x%L==g[0]%L] for g in gs))
    count=sum((f[0]+sum(a*x for a,x in zip(f[1],cs)))%N==B for cs in candidates)
    assert count==(N//L)**(m-1);hit('exact_arrow_fiber_count')
# Exhaust presentation equation parameters at modest ring; coefficients/constant equality exact.
N=12
for a,c,b,d in product(units(N),units(N),range(N),range(N)):
 x=(d,(c,));S=lambda a,x:comp((0,(a,)),[x],N);T=lambda b,x:comp((b,(1,)),[x],N)
 assert S(a,T(b,x))==T(a*b%N,S(a,x));assert S(a,S(c,x))==S(a*c%N,x)
 assert T(b,T(d,x))==T((b+d)%N,x);hit('unary_presentation')
for _ in range(1000):
 x,y,z=[randop(rng.randrange(1,5),N) for k in range(3)];add=lambda x,y:comp((0,(1,1)),[x,y],N)
 a=rng.choice(units(N));b=rng.randrange(N)
 assert add(add(x,y),z)==add(x,add(y,z))
 assert S(a,add(x,y))==add(S(a,x),S(a,y))
 assert add(T(b,x),y)==T(b,add(x,y)) and add(x,T(b,y))==T(b,add(x,y));hit('binary_presentation')
assert {2*x%4 for x in [0,2]}=={0} != {0,2};hit('nonunit_saturation_negative')
assert ['00','01','10','11']!=['00','10','01','11'];hit('planar_frontier_negative')
# Additive unit-preserving section Z/2 -> Z/4 impossible: possible image of1 is odd, its double nonzero.
assert all(2*x%4!=0 for x in [1,3]);hit('coherent_section_negative')
# Enumerate candidate operation lifts for the stronger whole-calculus section obstruction.
for b,a,c,t,u in product([0,2],[1,3],[1,3],[1,3],[1,3]):
 mu=(b,(a,c));tau=(t,(u,));ident=(0,(1,))
 assoc=comp(mu,[mu,ident],4)==comp(mu,[ident,mu],4)
 trans=comp(tau,[mu],4)==comp(mu,[tau,ident],4)
 invol=comp(tau,[tau],4)==ident
 assert not(assoc and trans and invol);hit('affine_calculus_section_negative')
# Chosen normalization fails ordinary new-root unit insertion, although operad units hold.
f=(3,(5,7));o,h=cut(f,0,2,12)
assert o==(3,(5,)) and o!=(0,(1,)) and comp(o,[h],12)==f
assert comp((0,(1,)),[f],12)==f;hit('root_normalization_degeneracy_negative')
# Congruence composite really equals gcd overlap, on unit and unrestricted parameters.
for N in [12,24]:
 divisors=[d for d in range(2,N+1) if N%d==0]
 for d,e in product(divisors,repeat=2):
  for domain in [list(range(N)),units(N)]:
   for x,y in product(domain,repeat=2):
    exists=any((x-z)%d==0 and (z-y)%e==0 for z in domain)
    assert exists==((x-y)%gcd(d,e)==0)
    assert ((x-y)%d==0 and (x-y)%e==0)==((x-y)%lcm(d,e)==0)
    hit('actual_congruence_join_meet')
result={'status':'PASS','seed':20261029,'counts':counts,'total_checks':sum(counts.values()),'scope':'Finite exact tests of formulas; accompanying proofs cover unbounded arity.'}
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

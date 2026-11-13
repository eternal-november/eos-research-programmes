#!/usr/bin/env python3
"""Exact finite equivalence-relation boundary checks; Python standard library only."""
from itertools import product,combinations
from pathlib import Path
import json

def partitions(n):
 def rec(a):
  if len(a)==n:yield tuple(a);return
  for z in range(max(a,default=-1)+2):yield from rec(a+[z])
 yield from rec([])
def rel(labels):return frozenset((i,j) for i in range(len(labels)) for j in range(len(labels)) if labels[i]==labels[j])
def compose(R,S,n):return frozenset((i,k) for i in range(n) for k in range(n) if any((i,j) in R and (j,k) in S for j in range(n)))
def join(R,S,n):
 T=R|S
 while True:
  U=T|compose(T,T,n)
  if U==T:return T
  T=U
def blocks(R,n):
 out=[];seen=set()
 for i in range(n):
  if i not in seen:
   b=frozenset(j for j in range(n) if (i,j) in R);out.append(b);seen|=b
 return out
def crt(Rs,n):
 bs=[blocks(R,n) for R in Rs]
 joins={(i,j):join(Rs[i],Rs[j],n) for i,j in combinations(range(len(Rs)),2)}
 for chosen in product(*bs):
  if all((next(iter(chosen[i])),next(iter(chosen[j]))) in J for (i,j),J in joins.items()):
   if not set.intersection(*(set(b) for b in chosen)):
    return False,[sorted(b) for b in chosen]
 return True,None

n=4;I=rel(tuple(range(n)));T=rel((0,)*n)
# Coordinates (a,b,a xor b): full two-bit witness, even-parity triple view.
Es=[rel(tuple((x>>0)&1 for x in range(n))),rel(tuple((x>>1)&1 for x in range(n))),rel(tuple(((x>>0)^(x>>1))&1 for x in range(n)))]
assert all(compose(E,F,n)==compose(F,E,n)==T for E,F in combinations(Es,2))
assert all(crt([E,F],n)[0] for E,F in combinations(Es,2))
assert not crt(Es,n)[0]
assert all(Es[i]&Es[j]==I for i,j in combinations(range(3),2))
assert Es[0]|I==Es[0]
# M3 distributivity failure E1 meet(E2 join E3) != joins of meets.
assert Es[0] & join(Es[1],Es[2],n) != join(Es[0]&Es[1],Es[0]&Es[2],n)
assert crt(Es+[I],n)[0] # full family can pass while a subfamily fails
# Compatibility with actual additive witness substitution.
for E in Es:
 for a,b,c,d in product(range(n),repeat=4):
  if (a,b) in E and (c,d) in E:assert (a^c,b^d) in E
# Each coordinate kernel has only itself or I as additive-congruence refinements.
repairs=[]
for mask in range(8):
 Rs=[I if (mask>>i)&1 else Es[i] for i in range(3)]
 if crt(Rs,n)[0]:repairs.append(mask)
minimal=[m for m in repairs if not any(k!=m and (k&m)==k for k in repairs)]
assert repairs==list(range(1,8)) and minimal==[1,2,4]
# Pullback along diagonal inclusion of 2 points into a four-point rectangle.
f=[0,3]
def pb(R):return frozenset((i,j) for i in range(2) for j in range(2) if (f[i],f[j]) in R)
assert join(pb(Es[0]),pb(Es[1]),2)!=pb(join(Es[0],Es[1],4))
# Exact sequential criterion for every pairwise-permutable triple of 4-point equivalences.
Ps=[rel(p) for p in partitions(n)];assert len(Ps)==15
checked=passed=failed=0
for A,B,C in product(Ps,repeat=3):
 if not all(compose(E,F,n)==compose(F,E,n) for E,F in [(A,B),(A,C),(B,C)]):continue
 lhs=compose(A&B,C,n);rhs=compose(A,C,n)&compose(B,C,n)
 truth=crt([A,B,C],n)[0]
 assert truth==(lhs==rhs)
 checked+=1;passed+=truth;failed+=not truth
# Planar order: independent labels do not license exchange.
cells=[(0,0),(0,1),(1,0),(1,1)]
row=sorted(cells);col=sorted(cells,key=lambda p:(p[1],p[0]))
assert row!=col
# Actual witness selection and fixed-endpoint refinement lifting differ.
sections=[]
for s0,s1 in product(range(4),repeat=2):
 s=[s0,s1]
 if all(s[x]%2==x for x in range(2)) and s0==0 and all(s[(x+y)%2]==(s[x]+s[y])%4 for x,y in product(range(2),repeat=2)):
  sections.append(s)
assert sections==[]
assert all(any(x%2==y for x in range(4)) for y in range(2))
# Saturation of each actual cut factor map within prescribed forest classes.
def saturated(f,domain_labels,target_labels):
 return all({f[v] for v in range(len(f)) if domain_labels[v]==domain_labels[u]} == {w for w in range(len(target_labels)) if target_labels[w]==target_labels[f[u]]} for u in range(len(f)))
assert not saturated([max(1,u) for u in range(2)], [0,0], [0,0])
assert not any(max(1,u)==0 for u in range(2))
assert all(saturated([(a+u)%4 for u in range(4)], [0,1,0,1], [0,1,0,1]) for a in range(4))
# Exhaustive generator criterion: spanning-chain generators of each target block.
generator_checks=0
for ds,ts in product(range(1,4),repeat=2):
 for dl in partitions(ds):
  for tl in partitions(ts):
   G={(i,j) for b in blocks(rel(tl),ts) for i,j in zip(sorted(b),sorted(b)[1:])}
   G=G|{(j,i) for i,j in G}
   for f in product(range(ts),repeat=ds):
    if not all(dl[u]!=dl[v] or tl[f[u]]==tl[f[v]] for u,v in product(range(ds),repeat=2)):continue
    local=all(any(dl[v]==dl[u] and f[v]==b for v in range(ds)) for u in range(ds) for a,b in G if a==f[u])
    assert local==saturated(f,dl,tl)
    generator_checks+=1
result={'status':'PASS','arithmetic':'finite sets and integers only','pairwise_permutable_triples_checked':checked,'joint_reconstruction_passed':passed,'joint_reconstruction_failed':failed,'parity_bad_block_tuple':crt(Es,n)[1],'all_three_pairwise_reconstructions_pass':True,'adding_identity_view_masks_bad_subfamily':True,'additive_witness_congruences_verified':True,'minimal_additive_repairs':minimal,'no_least_viewwise_repair':True,'inverse_image_join_failure':True,'planar_row_order':row,'planar_column_order':col,'quotient_section_counterexample':True,'fixed_endpoint_refinement_counterexample':True,'group_translation_arrow_lifting':True,'factor_map_generator_checks':generator_checks,'scope':'Boundary tests and exact 4-point relation criterion, not a general typed-calculus reconstruction proof.'}
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

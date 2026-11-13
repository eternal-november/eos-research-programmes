"""Independent finite stress checks, not imported author checkers and not unrestricted proofs."""
from itertools import combinations, permutations, product
from collections import Counter
from math import factorial
from pathlib import Path
import json,sys,hashlib
if not __debug__: raise RuntimeError('Optimized Python is not a verified execution mode')
out={}; nchecks=0

def check(x,msg):
 global nchecks
 nchecks+=1
 if not x: raise AssertionError(msg)

def comps(n,edges):
 rem=set(range(n)); ans=[]
 while rem:
  c={min(rem)}; todo=list(c)
  while todo:
   u=todo.pop()
   for v in list(rem-c):
    if tuple(sorted((u,v))) in edges: c.add(v); todo.append(v)
  rem-=c; ans.append(tuple(sorted(c)))
 return ans

def group(n,parts):
 for rows in product(*(tuple(permutations(c)) for c in parts)):
  g=list(range(n))
  for c,row in zip(parts,rows):
   for u,v in zip(c,row): g[u]=v
  yield tuple(g)

def induced(edges,U):
 return frozenset((i,j) for i in range(len(U)) for j in range(i+1,len(U)) if (U[i],U[j]) in edges)
def active(n,edges,flags):
 return frozenset(e for e in combinations(range(n),2) if flags[int(e in edges)])
def predicted(n,E,flags):
 if flags==(0,0): return True
 if flags==(1,1): return len(E) in (0,n*(n-1)//2)
 C=E if flags==(0,1) else frozenset(set(combinations(range(n),2))-set(E))
 parts=comps(n,C)
 return all(max(c)-min(c)+1==len(c) and all(e in C for e in combinations(c,2)) for c in parts)
# flags=(nonedge,edge). Test R and E for the uniquely forced candidate groups.
regime_cases=0; passed=Counter()
for n in range(6):
 pairs=list(combinations(range(n),2))
 subs=[tuple(i for i in range(n) if mask>>i&1) for mask in range(1<<n)]
 for mask in range(1<<len(pairs)):
  E=frozenset(e for i,e in enumerate(pairs) if mask>>i&1)
  for flags in product((0,1),repeat=2):
   parts=comps(n,active(n,E,flags)); G=tuple(group(n,parts)); Gset=set(G)
   local={U:(induced(E,U),set(group(len(U),comps(len(U),active(len(U),induced(E,U),flags))))) for U in subs}
   ok=True
   for g in G:
    for U in subs:
     gU=tuple(sorted(g[u] for u in U)); Ei,Hi=local[U]
     rank={v:i for i,v in enumerate(gU)}; rho=tuple(rank[g[u]] for u in U)
     if Ei!=induced(E,gU) or rho not in Hi: ok=False; break
    if not ok: break
   if ok:
    for U,(Ei,Hi) in local.items():
     for h in Hi:
      ext=list(range(n))
      for i,u in enumerate(U): ext[u]=U[h[i]]
      if tuple(ext) not in Gset: ok=False; break
     if not ok: break
   check(ok==predicted(n,E,flags),('four regimes',n,E,flags,ok))
   regime_cases+=1
   if ok: passed[str(flags)]+=1
out['four_regime_R_E']={'max_vertices':5,'cases':regime_cases,'passing_by_nonedge_edge_flags':dict(passed),'method':'All ordered simple graphs, forced permutation groups, every subset, every group element; R and E tested independently against structural prediction. Not enumeration of every arbitrary family.'}

# Supporting inversion lemma: generator components contain each permutation.
perm_count=0
for n in range(8):
 for g in permutations(range(n)):
  inv=frozenset((i,j) for i,j in combinations(range(n),2) if g[i]>g[j])
  parts=comps(n,inv)
  check(all(set(g[u] for u in c)==set(c) for c in parts),('inversion containment',g))
  check(all(max(c)-min(c)+1==len(c) for c in parts),('interval component',g))
  perm_count+=1
out['permutation_lemma']={'max_n':7,'permutations':perm_count}

# Occupancy normal forms, interval split/flatten and actual multinomial lift fibres.
cliques=((0,1,2),(3,4),(5,)); graph_edges=frozenset(e for c in cliques for e in combinations(c,2)); recs=Counter()
for labels in product(range(4),repeat=6):
 matrix=tuple(tuple(sum(labels[v]==i for v in c) for i in range(4)) for c in cliques)
 recs[matrix]+=1
cut_checks=0
for A,count in recs.items():
 expected=1
 for row in A: expected*=factorial(sum(row))//__import__('functools').reduce(lambda x,y:x*factorial(y),row,1)
 check(count==expected,('multinomial',A,count,expected))
 for i in range(5):
  for j in range(i,5):
   sums=tuple(sum(row[i:j]) for row in A)
   outer=tuple(row[:i]+(sum(row[i:j]),)+row[j:] for row in A)
   inner=tuple(row[i:j] for row in A if sum(row[i:j]))
   it=iter(inner); rebuilt=[]
   for row,s in zip(outer,sums):
    mid=next(it) if s else (0,)*(j-i)
    rebuilt.append(row[:i]+mid+row[i+1:])
   check(tuple(rebuilt)==A,('cut inversion',A,i,j)); cut_checks+=1
out['principal_cluster_model']={'clique_sizes':[3,2,1],'slots':4,'actual_partitions':4**6,'quotient_records':len(recs),'interval_inverse_checks':cut_checks,'retains_whole_edges':True}

# Actual principal six-vertex different-whole/repeated-occurrence refinement.
E0=frozenset([(0,1),(1,2),(1,3),(2,4),(3,4),(4,5)]); E1=E0|{(0,5)}
U=((0,),(1,3),(2,4),(5,))
check([induced(E0,x) for x in U]==[induced(E1,x) for x in U],'cross-edge observation')
check(induced(E0,U[1])==induced(E0,U[2]),'identical repeated components')
refined=(U[0],(U[1][0],),(U[1][1],),(U[2][1],),(U[2][0],),U[3])
check(refined==((0,),(1,),(3,),(4,),(2,),(5,)),'position-specific substitution')
scalar=lambda x,y: '0' if '0' in (x,y) else ('1' if x==y else 'e')
t1=('1','1','1','1'); t2=('1','e','e','1')
from functools import reduce
check(t1!=t2 and reduce(scalar,t1,'1')==reduce(scalar,t2,'1')=='1','endpoint equality does not equate tuples')
check(scalar('1','0')==scalar('e','0') and '1'!='e','noncancellation obstruction')
out['principal_original_model']={'interfaces':'0 -> 1 -> 1 -> 1 -> 2','whole_edges':[sorted(E0),sorted(E1)],'original_blocks':U,'refined_blocks':refined,'distinct_refinement_tuples':[t1,t2]}

# The all-run transport failure invisible to adjacent primitive pairs.
oldvalues=(0,1,1,0); lifted_sets=({0},{0},{0},{0})
def target_exists(lo,hi): return oldvalues[lo] in lifted_sets[lo] and oldvalues[hi] in lifted_sets[hi]
def fibre_size(lo,hi):
 if not target_exists(lo,hi): return None
 return int(all(oldvalues[i] in lifted_sets[i] for i in range(lo+1,hi)))
check(fibre_size(0,2) is None and fibre_size(1,3) is None,'pair supports empty')
check(fibre_size(0,3)==0,'full path missed witness')
# Noninjective unit: diagonal 2 -> 2x_1 2 misses off diagonals.
check(len([(x,x) for x in range(2)])==2 and len(list(product(range(2),repeat=2)))==4,'nullary diagonal defect')
# Exact evaluated root hides nonexact local stages.
f={0:0}; g={0:0,1:0}
check(len(set(f.values()))!=2 and len(set(g.values()))!=len(g),'stages nonbijective')
check({x:g[f[x]] for x in f}=={0:0},'evaluated composite is identity')
out['transport_and_stage_negatives']={'adjacent_pairs':'empty target and pass vacuously','whole_run':'one old target with no lift','nullary_duplicate_map':'diagonal image 2 of 4','root_only_exactness':'1 -> 2 -> 1 composite identity with both stages nonbijective'}

# Sampled capped-family result and its non-exact quotient boundary.
cap_cases=0
for t in range(2,8):
 for a,b,c in product(range(t+1),repeat=3):
  check(min(t,min(t,a+b)+c)==min(t,a+min(t,b+c)),('cap associativity',t,a,b,c)); cap_cases+=1
 for n in range(t+1):
  possible={n>0} # P1
  truth=n>0
  prev={x:x>0 for x in range(t+1)}
  for m in range(1,2*t+3):
   if m>1: prev={x:any(prev[a] and b>0 and min(t,a+b)==x for a,b in product(range(t+1),repeat=2)) for x in range(t+1)}
   check(prev[n]==(n==t or m<=n),('cap Pm',t,n,m))
 check(min(t,t+1)==t and not any(a+b==t and min(t,a)==t and min(t,b)==1 for a,b in product(range(t+1),repeat=2)),('cap nonexact map',t))
out['sample_I2_capped_monoids']={'t_range':[2,7],'associativity_cases':cap_cases,'Pm_range':'1 through 2t+2','N_to_cap_not_exact':True}

out['status']='PASS'; out['assertion_count']=nchecks
out['trust']='Independent finite Python checks; no imports of author code. Bounded corroboration, not kernel proofs or unrestricted theorem verification.'
out['script_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
p=Path(__file__).with_name('independent_adversarial_results.json');p.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))

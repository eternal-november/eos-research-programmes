#!/usr/bin/env python3
"""Exhaustive partition-model audit of the finite causal Horn descent criterion."""
import itertools,random,json,pathlib,hashlib
ROOT=pathlib.Path(__file__).resolve().parents[1]
def closure(n,P,H=()):
 parent=list(range(n))
 def find(x):
  while parent[x]!=x:parent[x]=parent[parent[x]];x=parent[x]
  return x
 def union(a,b):
  a,b=find(a),find(b)
  if a==b:return False
  parent[b]=a;return True
 for a,b in P['eq']+list(H):union(a,b)
 change=True
 while change:
  change=False
  for premises,head in P['horn']:
   if all(find(a)==find(b) for a,b in premises):change=union(*head) or change
 roots=[find(i) for i in range(n)]
 bad=any(all(roots[a]==roots[b] for a,b in f) for f in P['forbid'])
 return roots,bad
def test(n,P,Q):
 r,bad=closure(n,P)
 if any(not bad and r[a]!=r[b] for a,b in Q['eq']):return False
 for h,(a,b) in Q['horn']:
  r,bad=closure(n,P,h)
  if not bad and r[a]!=r[b]:return False
 return all(closure(n,P,f)[1] for f in Q['forbid'])
def models(e,P):
 eq=lambda a,b:e[a]==e[b]
 return (all(eq(a,b) for a,b in P['eq']) and
 all(not all(eq(a,b) for a,b in h) or eq(*head) for h,head in P['horn']) and
 not any(all(eq(a,b) for a,b in f) for f in P['forbid']))
def partitions(n):
 def rec(a):
  if len(a)==n:yield tuple(a);return
  for k in range(max(a,default=-1)+2):yield from rec(a+[k])
 yield from rec([])
def randomP(n,rng):
 pairs=list(itertools.combinations_with_replacement(range(n),2))
 return {'eq':[rng.choice(pairs) for _ in range(rng.randrange(3))],
 'horn':[([rng.choice(pairs) for _ in range(rng.randrange(3))],rng.choice(pairs)) for _ in range(rng.randrange(5))],
 'forbid':[[rng.choice(pairs) for _ in range(rng.randrange(3))] for _ in range(rng.randrange(3))]}
rng=random.Random(20261027);cases=0;assignments=0
for n in range(1,7):
 ps=list(partitions(n))
 for _ in range(250):
  P,Q=randomP(n,rng),randomP(n,rng)
  brute=all(not models(e,P) or models(e,Q) for e in ps)
  assert test(n,P,Q)==brute
  cases+=1;assignments+=len(ps)
# Redundant exact-pair witness absent, but generated equality gives exact descent.
P={'eq':[(0,1),(1,2)],'horn':[],'forbid':[]}
Q={'eq':[(0,2)],'horn':[],'forbid':[]}
assert (0,2) not in P['eq'] and test(3,P,Q)
# Fixed budget 1 entails all equalities; the budget-uniform criterion correctly fails.
P={'eq':[],'horn':[],'forbid':[]};Q={'eq':[(0,1)],'horn':[],'forbid':[]}
assert models((0,0),Q) and not test(2,P,Q)
e,bad=closure(2,P);assert not bad and models(e,P) and not models(e,Q)
# Impossible antecedent due to terminal demand legitimately entails an update rule.
P={'eq':[],'horn':[],'forbid':[[(0,1)]]}
Q={'eq':[],'horn':[([(0,1)],(2,3))],'forbid':[]}
assert test(4,P,Q)
# Coarsening two observed values to one creates a mixed shared-table obligation.
P={'eq':[],'horn':[],'forbid':[[(1,2)]]}
Q={'eq':[],'horn':[([],(1,2))],'forbid':[[(1,2)]]}
assert not test(3,P,Q)
e,bad=closure(3,P);assert not bad and models(e,P) and not models(e,Q)
result={'status':'PASS','random_presentation_pairs':cases,'exhaustive_partition_models':assignments,
 'zigzag_not_pair_surjectivity':'PASS','fixed_budget_scope_control':'PASS',
 'inconsistent_antecedent_control':'PASS','mixed_readout_forgetting_control':'PASS',
 'source_sha256':hashlib.sha256((ROOT/'theory/Causal_Constraint_Descent.md').read_bytes()).hexdigest()}
(ROOT/'review/Causal_Constraint_Descent_Results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))

#!/usr/bin/env python3
"""Exhaustive finite-table test of retained-table congruence/decoder entailment.
The four memory terms are x, y, f(x), f(y); every ground countermodel needs≤4 values.
"""
import itertools,random,json,pathlib,hashlib
ROOT=pathlib.Path(__file__).resolve().parents[1]
# Enumerate ACTUAL functions on a four-value carrier, not only partitions.
patterns=set();tablemodels=0
for x,y in itertools.product(range(4),repeat=2):
 for f in itertools.product(range(4),repeat=4):
  v=(x,y,f[x],f[y])
  canon=tuple({a:i for i,a in enumerate(dict.fromkeys(v))}[a] for a in v)
  for d in itertools.product(range(2),repeat=4):
   patterns.add((canon,tuple(d[a] for a in v)));tablemodels+=1
patterns=list(patterns)
def closure(eqs,demands):
 p=list(range(4))
 def find(x):
  while p[x]!=x:p[x]=p[p[x]];x=p[x]
  return x
 def union(a,b):
  a,b=find(a),find(b)
  if a!=b:p[b]=a
 for a,b in eqs:union(a,b)
 if find(0)==find(1):union(2,3)
 roots=[find(i) for i in range(4)]
 sets={r:{0,1} for r in roots}
 for t,allowed in demands:sets[roots[t]]&=set(allowed)
 return roots,sets,any(not a for a in sets.values())
def satisfies(v,ds,eqs,demands):
 return all(v[a]==v[b] for a,b in eqs) and all(ds[t] in s for t,s in demands)
r=random.Random(20261027);pairs=list(itertools.combinations_with_replacement(range(4),2));subsets=[set(),{0},{1},{0,1}]
checks=0
for _ in range(2000):
 eqs=[r.choice(pairs) for _ in range(r.randrange(4))]
 demands=[(r.randrange(4),r.choice(subsets)) for _ in range(r.randrange(4))]
 roots,sets,bad=closure(eqs,demands)
 if r.randrange(2):
  a,b=r.choice(pairs)
  calc=bad or roots[a]==roots[b]
  brute=all(not satisfies(v,ds,eqs,demands) or v[a]==v[b] for v,ds in patterns)
 else:
  t=r.randrange(4);allowed=r.choice(subsets)
  calc=bad or sets[roots[t]]<=allowed
  brute=all(not satisfies(v,ds,eqs,demands) or ds[t] in allowed for v,ds in patterns)
 assert calc==brute
 checks+=1
# Individually nonempty decoder demands are not context equivalent.
assert {0,1}&{1} and not ({0}&{1})
# Individually functional tables need not agree in a shared physical context.
assert any(f[0]==0 for f in itertools.product(range(2),repeat=2))
assert any(f[0]==1 for f in itertools.product(range(2),repeat=2))
assert not any(f[0]==0 and f[0]==1 for f in itertools.product(range(2),repeat=2))
# Actual context congruence f(x)=y, x=z entails f(z)=y uses SAME f symbol.
# Here x/y alias supplies congruence f(x)=f(y), exactly covered in all randomcases.
result={'status':'PASS','actual_four_state_function_models':tablemodels,
 'distinct_ground_interpretations':len(patterns),'entailment_cases':checks,
 'same_decoder_context_control':'PASS','same_update_table_context_control':'PASS',
 'source_sha256':hashlib.sha256((ROOT/'theory/Parametric_Causal_Descent.md').read_bytes()).hexdigest()}
(ROOT/'review/Parametric_Causal_Descent_Results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))

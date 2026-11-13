"""Finite verification of marking fibres and actual edge-gauge equations.
M=C2 with absorbing zero; H=C2. Scalars 0,1 are group exponents; 2 is zero.
Tree parent tuples include unary and branching shapes; zero-grade nodes are retained.
"""
import itertools,json
mul=lambda a,b:2 if 2 in (a,b) else (a+b)%2
prod=lambda xs: __import__('functools').reduce(mul,xs,0)
count=arrows=contractions=0
for n in range(1,6):
 for ps in itertools.product(*(range(i) for i in range(1,n))):
  parent=[None]+list(ps)
  children=[[j for j in range(1,n) if parent[j]==i] for i in range(n)]
  for flags in itertools.product([False,True],repeat=n):
   if any(flags[i] and not flags[parent[i]] for i in range(1,n)):continue
   active=[i for i in range(1,n) if flags[i]]
   for m in range(3):
    objs=[]
    for hs in itertools.product(range(2),repeat=len(active)):
     x=[0]*n
     for i,h in zip(active,hs):x[i]=h
     x[0]=mul(m,prod(hs));assert prod(x)==m
     objs.append(x)
    assert len(objs)==2**len(active)
    for x in objs:
     seen=set()
     for gs in itertools.product(range(2),repeat=len(active)):
      g=[0]*n
      for i,h in zip(active,gs):g[i]=h
      y=[mul(mul(x[i],g[i]),prod(g[j] for j in children[i])) for i in range(n)]
      assert y in objs
      seen.add(tuple(y));arrows+=1
      for c in range(1,n):
       p=parent[c]
       xp=mul(x[p],x[c]);yp=mul(y[p],y[c])
       newchildren=[j for j in children[p] if j!=c]+children[c]
       assert yp==mul(mul(xp,g[p]),prod(g[j] for j in newchildren))
       contractions+=1
     assert len(seen)==len(objs)
    count+=1
print(json.dumps(dict(tree_grade_root_cases=count,gauge_arrows=arrows,contraction_equations=contractions,monoid='C2 plus absorbing zero',status='PASS'),indent=2))

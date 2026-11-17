"""Exact finite diagnostics, not a proof of the infinite/native statements."""
from fractions import Fraction as Q
from functools import lru_cache
from collections import defaultdict
from itertools import product
H=('?',)
L=('L',)
P={'L':Q(1,4),'D':Q(3,4),'U':Q(0)}
PAIR={('D','D'):Q(1,2),('D','L'):Q(1,4),('L','D'):Q(1,4)}
@lru_cache(None)
def raw(n):
 if n==0:return (H,)
 prev=raw(n-1)
 return (L,)+tuple(('U',t) for t in prev)+tuple(('D',a,b) for a in prev for b in prev)
def trunc(t,n):
 if n==0:return H
 if t[0]=='L':return L
 if t[0]=='?':return H
 return (t[0],)+tuple(trunc(x,n-1) for x in t[1:])
def done(t):return t[0]!='?' and all(done(c) for c in t[1:])
def push(q,n):
 r=defaultdict(Q)
 for t,p in q.items():r[trunc(t,n)]+=p
 return dict(r)
@lru_cache(None)
def independent(n):
 if n==0:return {H:Q(1)}
 prev=independent(n-1);r={L:P['L']}
 for a,pa in prev.items():
  for b,pb in prev.items():r[('D',a,b)]=P['D']*pa*pb
 return r
@lru_cache(None)
def synchronized(n):
 if n==0:return {H:Q(1)}
 r={L:P['L']}
 for t,p in synchronized(n-1).items():r[('D',t,t)]=P['D']*p
 return r
@lru_cache(None)
def conditional(n,label):
 if n==0:return {H:Q(1)}
 if label=='L':return {L:Q(1)}
 if n==1:return {('D',H,H):Q(1)}
 r=defaultdict(Q)
 for (a,b),p in PAIR.items():
  for ta,pa in conditional(n-1,a).items():
   for tb,pb in conditional(n-1,b).items():r[('D',ta,tb)]+=p*pa*pb
 return dict(r)
def nonextinct_after_branch(n):
 if n==0:return {H:Q(1)}
 r={L:P['L']}
 for t,p in conditional(n,'D').items():r[t]=P['D']*p
 return r
def at(t,address):
 for i in address:
  if t[0]!='D':return None
  t=t[i+1]
 return t
for name,law in [('independent',independent),('depth-synchronized',synchronized),('no-LL-sibling',nonextinct_after_branch)]:
 prev=None
 for n in range(5):
  q=law(n)
  assert sum(q.values())==1
  if prev is not None: assert push(q,n-1)==prev
  for depth in range(n):
   for address in product((0,1),repeat=depth):
    mass=sum(p for t,p in q.items() if at(t,address) is not None)
    bran=sum(p for t,p in q.items() if at(t,address) is not None and at(t,address)[0]=='D')
    assert bran==P['D']*mass
  fin=sum(p for t,p in q.items() if done(t))
  if name=='depth-synchronized':assert fin==1-Q(3,4)**n
  if name=='no-LL-sibling' and n:assert fin==Q(1,4)
  if name=='independent' and n:
   oldfin=sum(p for t,p in prev.items() if done(t));assert fin==Q(1,4)+Q(3,4)*oldfin**2
  prev=q
  print(name,'depth',n,'support',len(q),'complete mass',fin)
 # Explicit complete finite raw carrier includes zero unary paths, not support quotient.
 full={t:law(3).get(t,Q(0)) for t in raw(3)}
 assert len(full)==183 and sum(full.values())==1
 assert full[('U',('U',('U',H)))]==0
 print(name,'all-raw depth3',len(full),'zero atoms',sum(p==0 for p in full.values()))
# Crossing witness: no deterministic raw map from singleton to a fair pair.
for image in (0,1):
 pushed=[Q(int(i==image)) for i in (0,1)]
 assert pushed != [Q(1,2),Q(1,2)]
print('PASS: exact projectivity, ancestry-conditioned primitive tables, completion formulas, zero raw retention, and singleton pushforward obstruction.')

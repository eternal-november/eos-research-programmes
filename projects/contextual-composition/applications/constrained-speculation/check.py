from fractions import Fraction as F
from itertools import product, combinations
import json

def sampler(p,q):
    rho=sum(max(q[i]-p[i],F(0)) for i in range(len(p)))
    atoms=[(('accept',i,i),min(p[i],q[i])) for i in range(len(p))]
    if rho:
        atoms += [(('reject',i,j),max(q[i]-p[i],F(0))*max(p[j]-q[j],F(0))/rho) for i in range(len(p)) for j in range(len(p))]
    return atoms

def marginal(atoms,n):
    return tuple(sum(w for (_,_,y),w in atoms if y==i) for i in range(n))
def distributions(n,d):
    return [tuple(F(x,d) for x in xs) for xs in product(range(d+1),repeat=n) if sum(xs)==d]

count=0
for p in distributions(3,4):
 for q in distributions(3,4):
    a=sampler(p,q)
    assert sum(w for _,w in a)==1 and marginal(a,3)==p
    assert all(w>=0 for _,w in a)
    count+=1

alphabet='ab'
def process(kernels,horizon):
    out={'':F(1)}
    for _ in range(horizon):
        out={h+x:w*p for h,w in out.items() for x,p in zip(alphabet,kernels[h]) if p}
    return out

def transformed(p,horizon,L):
    u={h:F(h in L) for h in map(''.join,product(alphabet,repeat=horizon))}
    for k in range(horizon-1,-1,-1):
      for h in map(''.join,product(alphabet,repeat=k)):
        u[h]=sum(p[h][i]*u[h+x] for i,x in enumerate(alphabet))
    if not u['']: return None
    cond={}; local={}; criterion=True
    for h in p:
      if u[h]==0: continue
      allowed=[u[h+x]>0 for x in alphabet]
      z=sum(p[h][i] for i in range(2) if allowed[i])
      cond[h]=tuple(p[h][i]*u[h+x]/u[h] for i,x in enumerate(alphabet))
      local[h]=tuple(p[h][i]/z if allowed[i] else F(0) for i in range(2))
      # Criterion only at prefixes reached by the conditioned process.
      raw=F(1)
      for j,x in enumerate(h): raw*=p[h[:j]][alphabet.index(x)]
      if raw:
        values={u[h+x] for i,x in enumerate(alphabet) if p[h][i] and allowed[i]}
        criterion &= len(values)==1
    return u,cond,local,criterion

p={'':(F(1,2),F(1,2)),'a':(F(3,4),F(1,4)),'b':(F(1,4),F(3,4))}
L={'aa','ba','bb'}
u,c,l,criterion=transformed(p,2,L)
conditional=process(c,2); masked=process(l,2)
assert conditional=={'aa':F(3,7),'ba':F(1,7),'bb':F(3,7)}
assert masked=={'aa':F(1,2),'ba':F(1,8),'bb':F(3,8)}
assert sum(abs(conditional.get(h,0)-masked.get(h,0)) for h in L)/2==F(1,14)
# Speculative native witness projection commutes with dependent composition.
for target in [c,l]:
    projected={h:marginal(sampler(target[h],(F(3,4),F(1,4))),2) for h in target}
    assert process(projected,2)==process(target,2)
# Different original futures give the same allowed-next-token interface but different target root laws.
p2=dict(p); p2['a']=(F(1,4),F(3,4))
u2,c2,l2,_=transformed(p2,2,L)
assert tuple(bool(u[x]) for x in alphabet)==tuple(bool(u2[x]) for x in alphabet)==(True,True)
assert c['']!=(c2['']) and c2['']==(F(1,5),F(4,5))
# Exhaustive finite regression of the criterion, including zero original probabilities.
checked=0
leaves=['aa','ab','ba','bb']
for rows in product(distributions(2,4),repeat=3):
    kernels=dict(zip(['','a','b'],rows))
    raw=process(kernels,2)
    for bits in product([False,True],repeat=4):
      lang={h for h,b in zip(leaves,bits) if b}
      tr=transformed(kernels,2,lang)
      if tr is None: continue
      u,cond,local,crit=tr
      direct={h:w/u[''] for h,w in raw.items() if h in lang}
      assert process(cond,2)==direct
      assert (process(local,2)==direct)==crit
      checked+=1
print(json.dumps({'sampler_pairs':count,'conditioned_language_cases':checked,'conditional':{k:str(v) for k,v in conditional.items()},'local_mask':{k:str(v) for k,v in masked.items()},'total_variation':'1/14','status':'PASS'},indent=2))

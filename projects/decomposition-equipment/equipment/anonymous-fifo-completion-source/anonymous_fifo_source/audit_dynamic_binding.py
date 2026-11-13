"""Independent finite integration sanity check; not a physical proof."""
from fractions import Fraction as F
import random, sys
from binding_checker import from_windows, verify_positive
rng=random.Random(531)
for trial in range(1000):
 q=rng.randint(2,5); h=rng.randint(2,4); n=q*h; J=F(1); eps=F(1)
 ids=list(range(n)); rng.shuffle(ids); groups=[ids[r*h:(r+1)*h] for r in range(q)]
 owner={i:r for r,g in enumerate(groups) for i in g}
 tau={i:F(100*q*h+rng.randint(-1,1)) for i in ids}
 a={i:tau[i]+F(rng.randrange(5),4) for i in ids}
 lo={i:a[i]-J for i in ids}; hi=a.copy()
 for i in range(n):
  for j in range(i+1,n):
   S=max(hi[i],hi[j])+J; C=lo[i]+lo[j]; assert S<C
   if owner[i]==owner[j]:
    pair=[tau[i],tau[i]+tau[j]]
   else: pair=[tau[i],tau[j]]
   last=max(t+F(rng.randrange(5),4) for t in pair)
   assert (last>(S+C)/2)==(owner[i]==owner[j])
 L=min(lo.values()); U=max(hi.values()); W=U-L
 delta=eps*((h*W+J)//eps+1)
 assert delta>h*W+J and L>(q-1)*delta+h*W+J and (h-1)*eps<L
 windows=[None]*n; reports=[]; bits={i:rng.randrange(2) for i in ids}; roles={i:k for g in groups for k,i in enumerate(g)}
 for r,g in enumerate(groups):
  finish=r*delta
  for k,i in enumerate(g,1):
   release=r*delta+(k-1)*eps; finish=max(finish,release)+tau[i]
   t=finish+F(rng.randrange(5),4)
   windows[i]=(r*delta+k*L,r*delta+k*U+J)
   assert windows[i][0]<=t<=windows[i][1]
   reports.append((t,bits[i],i))
 rng.shuffle(reports) # arbitrary occurrence indexing, no rank input
 timestamps=[x[0] for x in reports]; values=[x[1] for x in reports]
 rolelist=[roles[i] for i in range(n)]
 cert=from_windows(windows,timestamps,rolelist,values)
 assert cert['status']=='CERTIFIED'
 expected={r:0 for r in range(h)}
 for i in range(n): expected[roles[i]]^=bits[i]
 actual={r:(cert['parity_mask']>>k)&1 for k,r in enumerate(cert['role_labels'])}
 assert actual==expected
 edges=[[j for j,t in enumerate(timestamps) if low<=t<=high] for low,high in windows]
 assert verify_positive(edges,rolelist,values,cert)
print('PASS: 1000 exact-rational anonymous acquisition/schedule/binding fixtures, including heterogeneous durations and arbitrary report row order.')

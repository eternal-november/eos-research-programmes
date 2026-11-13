#!/usr/bin/env python3
"""Independent exhaustive fair-bit driver pushforward check."""
from fractions import Fraction as F
from pathlib import Path
from itertools import product
import json
N=1<<20
counts=[0]*200
for u in range(N):counts[(200*u)//N]+=1
assert set(counts)=={5242,5243}
assert counts.count(5243)==176 and counts.count(5242)==24
source_tv=sum(abs(F(n,N)-F(1,200)) for n in counts)/2
assert source_tv==F(33,1638400)
# Check every decile threshold pair, not only the proposed 64-context subset.
for p,q in product(range(11),repeat=2):
 old=[F(0)]*4;new=[F(0)]*4
 for r,n in enumerate(counts):
  a,b=(r//10,r//10) if r<100 else ((r-100)//10,(r-100)%10)
  index=2*int(a<p)+int(b<q)
  old[index]+=F(1,200);new[index]+=F(n,N)
 assert sum(old)==sum(new)==1
 assert sum(abs(x-y) for x,y in zip(old,new))/2<=source_tv
root=Path(__file__).resolve().parents[1]
report=json.loads((root/'examples/weighted_episode_discovery_checks.json').read_text())
old_bound=F(report['weighted_exact_rational']);new_bound=old_bound+2*source_tv
rounded=F(report['bounded_source_J_outward'])
assert new_bound<=rounded==F(43653,1000000)<F(1,20)
print(json.dumps({'status':'PASS','fair_bit_words_checked':N,'threshold_pairs_checked':121,
 'source_TV':str(source_tv),'H2_J_upper':float(new_bound),'outward_J_upper':str(rounded),
 'scope':'Finite exact sampler pushforward; fair-bit and arithmetic capabilities remain declared assumptions'},indent=2))

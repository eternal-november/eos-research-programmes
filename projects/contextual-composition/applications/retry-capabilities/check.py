#!/usr/bin/env python3
"""Exact finite regressions, not a proof of the parameterized theorems."""
from itertools import product, combinations
from fractions import Fraction

def step(seen, counts, k, outcome, evict=False):
    # outcome 0: request lost; 1: effect/duplicate handled, ACK lost; 2: ACK received
    seen=set(seen); counts=list(counts)
    if outcome:
        if k not in seen:
            counts[k]+=1; seen.add(k)
        if evict: seen.discard(k)
    return frozenset(seen),tuple(counts), outcome==2

checks={}; runs=0
for m in range(1,4):
    for length in range(6):
        for word in product(product(range(m),range(3)),repeat=length):
            seen=frozenset(); counts=(0,)*m; acked=set(); delivered=set()
            for k,o in word:
                # arbitrary active replays give stronger safety than Pending-only clients
                seen,counts,ack=step(seen,counts,k,o)
                if o: delivered.add(k)
                if ack: acked.add(k)
                assert counts==tuple(int(k in delivered) for k in range(m))
                assert acked<=delivered
            runs+=1
checks['exhaustive_schedule_runs']=runs
# All distinct seen sets have a one-request distinguishing execution increment.
pairs=0
for m in range(1,8):
    sets=[frozenset(k for k in range(m) if mask>>k&1) for mask in range(2**m)]
    for s,t in combinations(sets,2):
        k=next(iter(s^t))
        assert int(k not in s)!=int(k not in t)
        pairs+=1
checks['distinguished_state_pairs']=pairs
# Lost ACK followed by cache loss then retry repeats the external effect.
s,c,_=step(frozenset(),(0,),0,1)
s=frozenset()
s,c,ack=step(s,c,0,2)
assert c==(2,) and ack
checks['eviction_counterexample']=True
# Retire only after removing all future uses: other-key continuation unaffected.
for m in range(1,5):
  for mask in range(2**m):
    s=frozenset(k for k in range(m) if mask>>k&1)
    for retired in range(m):
      for word in product([k for k in range(m) if k!=retired],repeat=3):
        a=s; b=s-{retired}; ca=cb=(0,)*m
        for k in word:
          a,ca,_=step(a,ca,k,2); b,cb,_=step(b,cb,k,2)
        assert ca==cb
checks['retirement_suffix_check']=True
# Equality of stochastic laws needs the same witness kernels on related states.
def one_step_law(seen, counts, k, kernel):
    law={}
    for o,p in enumerate(kernel(seen)):
        if not p: continue
        _,after,ack=step(seen,counts,k,o)
        observable=(ack,tuple(y-x for x,y in zip(counts,after)))
        law[observable]=law.get(observable,Fraction(0))+p
    return law
full=frozenset({0}); forgotten=frozenset(); counts=(1,0)
constant=lambda s: (Fraction(1,3),Fraction(1,6),Fraction(1,2))
assert one_step_law(full,counts,1,constant)==one_step_law(forgotten,counts,1,constant)
checks['retirement_equal_kernel_law']=True
private=lambda s: (0,0,1) if 0 in s else (1,0,0)
assert one_step_law(full,counts,1,private)=={(True,(0,1)):Fraction(1)}
assert one_step_law(forgotten,counts,1,private)=={(False,(0,0)):Fraction(1)}
checks['retirement_private_kernel_counterexample']=True

# Ordered admission permits prefix state instead of arbitrary subsets.
for m in range(1,9):
  for h in range(m+1):
    for k in range(h+1):
      if k<m:
        assert int(k not in set(range(h)))==int(k==h)
checks['ordered_prefix_control']=True
# Single-key independent losses: D success d, conditional ACK success a.
d,a=Fraction(2,3),Fraction(1,2)
for n in range(1,6):
  prob_exec=prob_done=Fraction(0)
  for outcomes in product(range(3),repeat=n):
    p=Fraction(1)
    for o in outcomes: p*= [1-d,d*(1-a),d*a][o]
    prob_exec+=p*int(any(outcomes))
    prob_done+=p*int(2 in outcomes)
  assert prob_exec==1-(1-d)**n
  assert prob_done==1-(1-d*a)**n
checks['exact_loss_probabilities']=True
import json
print(json.dumps(checks,indent=2))

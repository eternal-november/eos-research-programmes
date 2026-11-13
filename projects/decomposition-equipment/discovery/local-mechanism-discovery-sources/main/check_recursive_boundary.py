"""Exact rational check: instantaneous outgoing signal is not an autonomous interface.
The source has four states (visible output x, internal phase h), positive nonlinear
fresh updates, and a two-valued outgoing signal x. Source and interface share state;
this is not a claim that four extra physical states must be installed.
"""
from fractions import Fraction as F
import json
from pathlib import Path
states=[(x,h) for x in range(2) for h in range(2)]
# Fresh x depends genuinely on both old x and old h. Fresh h has persistent memory.
p_x={(0,0):F(1,5),(0,1):F(3,5),(1,0):F(2,5),(1,1):F(4,5)}
p_h={0:F(1,4),1:F(3,4)}
K=[]
for x,h in states:
    K.append([(p_x[x,h] if y else 1-p_x[x,h])*(p_h[h] if k else 1-p_h[h]) for y,k in states])
assert all(sum(row)==1 and min(row)>0 for row in K)
P=[tuple(i for i,s in enumerate(states) if s[0]==x) for x in range(2)]
stages=[P]
while True:
    new=[]
    for block in P:
        groups={}
        for i in block:
            signature=tuple(sum(K[i][j] for j in target) for target in P)
            groups.setdefault(signature,[]).append(i)
        new.extend(tuple(v) for v in groups.values())
    if len(new)==len(P): break
    P=new; stages.append(P)
assert len(stages[0])==2 and len(P)==4
# Enumerate all set partitions and verify no smaller stable partition refines output x.
def partitions(xs):
    if not xs:
        yield []
        return
    a,*rest=xs
    for p in partitions(rest):
        yield [(a,)]+p
        for j in range(len(p)):
            yield p[:j]+[(a,)+p[j]]+p[j+1:]
def stable(p):
    if any(len({states[i][0] for i in block})>1 for block in p): return False
    return all(len({tuple(sum(K[i][j] for j in target) for target in p) for i in block})==1 for block in p)
accepted=[p for p in partitions(list(range(4))) if stable(p)]
assert min(map(len,accepted))==4
# Coupled pushforward must be q(nextsource); q is now injective, so exact source draw.
# Independent duplicate sampling has positive mismatch probability even with correct marginals.
independent_mismatch=1-sum(v*v for v in K[0])
assert independent_mismatch>0
result={'status':'PASS','source_state_count':4,'instantaneous_signal_count':2,
        'minimal_autonomous_summary_count':4,'refinement_stage_sizes':[len(p) for p in stages],
        'positive_transition_min':str(min(map(min,K))),
        'independent_duplicate_mismatch_probability':str(independent_mismatch),
        'scope':'Exact rational finite fixture; no all-size computational proof; memory credited to source.'}
Path(__file__).with_name('Recursive_Boundary_QA.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))

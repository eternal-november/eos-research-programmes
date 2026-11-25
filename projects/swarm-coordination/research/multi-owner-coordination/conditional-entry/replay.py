from functools import lru_cache
from itertools import product

@lru_cache(None)
def feasible_alloc(r,B,c,strict):
    d=int(strict)
    return any(all(p_i-r_i>=d for p_i,r_i in zip(p,r)) and B-sum(p)>=c+d
               for p in product(range(B+1),repeat=len(r)))

@lru_cache(None)
def continuations(r,B,spent=0):
    # Set of all pure subgame-perfect outcomes under all tie resolutions.
    # (fractional transfers and probabilistic ties are outside this checker).
    # payoff of an owner when grant accepted is toll minus own outside gap;
    # all outside/no-is-final branches are normalized to zero.
    if not r:
        if spent<B:return (spent,)
        if spent==B:return (-1,spent)
        return (-1,)
    moves=[(0,(-1,))]
    for p in range(max(0,B-spent)+1):
        tail=continuations(r[1:],B,spent+p)
        # A complete strategy can select different credible continuations
        # after each offered price. A move need only beat every other
        # move's worst credible continuation to be supportable.
        moves.append((p-r[0],tail))
    floor=max(min((v if x>=0 else 0) for x in xs) for v,xs in moves)
    return tuple(sorted({x for v,xs in moves for x in xs if (v if x>=0 else 0)>=floor}))

allocations=sequential_states=trades=witnesses=0
for m in (1,2,3):
 for rr in product(range(4),repeat=m):
  for B in range(1,9):
   paths=continuations(rr,B)
   assert all(p<0 or 0<=B-p<=1 for p in paths)
   if B>=sum(rr)+m+1:
       assert all(p>=0 for p in paths)
   sequential_states+=len(paths)
   trades+=sum(p>=0 for p in paths)
   for c in range(2,6):
    for strict in (False,True):
     expected=B>=sum(rr)+c+int(strict)*(m+1)
     assert feasible_alloc(rr,B,c,strict)==expected
     allocations+=1
    if feasible_alloc(rr,B,c,True):
     assert all(p<0 or B-p<c for p in paths)
     witnesses+=1
checks=early_only=missing=0
stamps=(0,1,2,3,None)
for r1,r2,g1,g2,D,d in product(stamps,stamps,(0,1,2),(0,1,2),range(7),(1,2)):
 R=(r1,r2); G=(g1,g2)
 for pre in (True,False):
  times=[t for t in range(D+1) if all(r is not None and t>=r+(0 if pre else lag)
          for r,lag in zip(R,G)) and t+d<=D]
  predicted=all(r is not None for r in R) and max(r+(0 if pre else lag) for r,lag in zip(R,G))+d<=D
  assert bool(times)==predicted
  checks+=1
  missing+=any(r is None for r in R) and not predicted
 if r1 is not None and r2 is not None:
  early_only+=max(R)+d<=D<max(r1+g1,r2+g2)+d
print(f'allocations={allocations} subgame_outcomes={sequential_states} accepted_outcomes={trades} costly_preparation_separations={witnesses}')
print(f'timing_checks={checks} timing_positive_only_with_prior_consent={early_only} missing_evidence_rejections={missing}')
assert feasible_alloc((1,2),8,2,True)
assert all(v<0 or 8-v<=1 for v in continuations((1,2),8))
from fractions import Fraction as F
joint_checks=0
for q,r,k,b,c in product((F(0),F(1,4),F(1,2),F(3,4),F(7,8),F(1)),
                           ((0,0),(1,2)), ((0,0),(1,0),(1,1)), range(10), range(4)):
 possible=any(all(q*(pi-ri)>ki for pi,ri,ki in zip(p,r,k)) and q*(b-sum(p))>c
              for p in product(range(b+1),repeat=2))
 formula=q>0 and b>=sum(ri+ki//q+1 for ri,ki in zip(r,k))+c//q+1
 assert possible==formula
 joint_checks+=1
print(f'joint_chance_checks={joint_checks}')

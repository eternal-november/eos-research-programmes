from itertools import combinations
from fractions import Fraction as F
from math import comb

# Exactly one latent label is drawn for the entire mission. Which of these
# fixed laws applies is unknown; law j assigns spare mass w to label j.
def robust_risk(candidates,n,w):
    # independent from the closed expression, enumerate the law choices.
    return max(sum((1-w)/n+(w if i==j else 0) for i in candidates)
               for j in range(n)) if candidates else F(0)

checks=0
for n in range(2,11):
    for k in range(1,n):
        w=F(1,5)
        cap=w+(1-w)*F(k,n)
        profiles=set()
        contiguous_profiles=set()
        for s in combinations(range(n),k):
            S=frozenset(s)
            profile=tuple(robust_risk(S|{q},n,w)<=cap for q in range(n))
            assert profile==tuple(q in S for q in range(n))
            profiles.add(profile)
            if max(s)-min(s)==k-1: contiguous_profiles.add(profile)
            checks+=n
        assert len(profiles)==comb(n,k)
        assert len(contiguous_profiles)==n-k+1
print(checks,"exact robust-risk queries agree with the exposure membership test")
print("n=100 and k=50 minimum code states",comb(100,50),
      "fixed-width bits",(comb(100,50)-1).bit_length())
print("same n and k but contiguous exposure, fixed-width bits",(100-50).bit_length())

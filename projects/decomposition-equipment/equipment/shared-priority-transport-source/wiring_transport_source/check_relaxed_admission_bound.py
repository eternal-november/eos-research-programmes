"""Exhaustive finite check of sequential same-tick first-subset bounds.
No sharpness claim except singleton first subset and hard-safe probability.
"""
from collections import Counter
from itertools import permutations, product
from fractions import Fraction
from math import factorial, comb
import json

def run(max_n=6):
    rows=[]
    for n in range(2,max_n+1):
        for s in range(1,n+1):
            S=set(range(s));orders=Counter()
            for pi in permutations(range(n)):
                a=next(i for i in pi if i in S)
                sigma=(a,)+tuple(i for i in pi if i!=a)
                orders[sigma]+=1
            assert max(orders.values())<=n-s+1
            assert set(orders)=={p for p in permutations(range(n)) if p[0] in S}
            score=0;safe_words=0
            for y in product((0,1),repeat=n):
                vectors=Counter()
                for sigma,multiplicity in orders.items():
                    vector=[0]*n
                    for k,i in enumerate(sigma):vector[i]=y[k]
                    vectors[tuple(vector)]+=multiplicity
                score+=max(vectors.values())
                safe_words+=len(vectors)==1
                k=sum(y)
                assert Fraction(max(vectors.values()),factorial(n))<=min(Fraction(1),Fraction(n-s+1,comb(n,k)))
            success=Fraction(score,factorial(n)*2**n)
            bound=Fraction(sum(min(comb(n,k),n-s+1) for k in range(n+1)),2**n)
            universal=Fraction(max(2*n,n*n-2*n+3),2**n)
            assert success<=bound and success<=universal
            assert Fraction(safe_words,2**n)==Fraction(2**(2 if s==1 else 1),2**n)
            if s==1:assert success==Fraction(n,2**(n-1))
            rows.append(dict(n=n,first_subset_size=s,optimal_average_success=str(success),
                multiplicity_bound=str(bound),universal_bound=str(universal),
                maximum_preimages=max(orders.values()),hard_safe_probability=str(Fraction(safe_words,2**n))))
    return dict(status='ALL CHECKS PASSED',rows=rows)

if __name__=='__main__':print(json.dumps(run(),indent=2))

"""Exact finite-tree checks for the exposure-weighted transfer theorem.
Not a substitute for proof; rational arithmetic, history-dependent kernels,
post-feedback decisions, safe exits and loss exits.
"""
from fractions import Fraction as F
from itertools import product

def evaluate(params):
    # three observable steps; outcome 1 after two previous ones causes loss.
    # History (0,0) is certified safe exit, (1,0) uncovered uncertified exit.
    def terminal(h):
        if h == (0,0): return 0
        if h == (1,0): return 1
        if len(h)==3: return int(sum(h)>=2)
        return None
    def p(h): return params[(len(h)+sum(h))%len(params)][0]
    def q(h): return params[(len(h)+sum(h))%len(params)][1]
    def recur(h):
        v=terminal(h)
        if v is not None: return F(v),F(v),F(0)
        p0,p1,e0=recur(h+(0,)); r0,r1,e1=recur(h+(1,))
        a,b=p(h),q(h)
        return ((1-a)*p0+a*r0, (1-b)*p1+b*r1,
                abs(a-b)+(1-b)*e0+b*e1)
    return recur(())

vals=[F(0),F(1,4),F(1,2),F(3,4),F(1)]
count=0
for numbers in product(vals,repeat=6):
    params=list(zip(numbers[::2],numbers[1::2]))
    true,model,exposure=evaluate(params)
    assert abs(true-model)<=exposure,(params,true,model,exposure)
    count+=1
print(f'PASS: {count} rational history-dependent P/Q pairs; two-sided loss difference <= Q-live exposure')

"""Exact finite decision check after the forced simultaneous service reports.
Calibration does not appear: the interaction-law proof shows it has zero pi information.
Every deterministic output rule on four report pairs is checked; randomization is
its convex hull. Abort/invalid outputs are represented by None.
"""
from fractions import Fraction
from itertools import product

pairs=list(product((0,1), repeat=2))
actions=pairs+[None]
best_avg=Fraction(1)
best_deterministic_worst=Fraction(1)
for rule in product(actions,repeat=4):
    risks=[]
    for reverse in (False,True):
        failures=sum(out != (bits[::-1] if reverse else bits)
                     for bits,out in zip(pairs,rule))
        risks.append(Fraction(failures,4))
    best_avg=min(best_avg,sum(risks)/2)
    best_deterministic_worst=min(best_deterministic_worst,max(risks))
assert best_avg == Fraction(1,4)
assert best_deterministic_worst == Fraction(1,4)
for reverse in (False,True):
    risk=sum(Fraction(out != (bits[::-1] if reverse else bits),8)
             for bits in pairs for out in (bits,bits[::-1]))
    assert risk == Fraction(1,4)
print("PASS: Bayes lower bound 1/4; achievable worst-world risk 1/4.")

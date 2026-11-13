"""Exact independent checks; no empirical physical validation."""
from fractions import Fraction as F

def stopping(v,a,T,b):
    assert min(v,a,T)>=0 and b>0
    return v*T+a*T*T/2+(v+a*T)**2/(2*b)

v,a,b=F(1),F(0),F(1)
assert stopping(v,a,F(0),b)==F(1,2)<F(3,5)
assert stopping(v,a,F(1,5),b)==F(7,10)>F(3,5)
assert F(3,5)-v*F(1,5)==F(2,5)<stopping(v,a,F(0),b)
assert stopping(v,a,F(1,10),b)==F(3,5)<F(13,20)
assert stopping(v,a,F(1,5),b)==F(7,10)>F(13,20)
assert stopping(v,a,F(0),F(1,4))==2
# Acceleration during reaction: omitting it is nonconservative.
assert stopping(F(1),F(1),F(1,5),F(1))==F(47,50)
# Conservative speed quantization matters even without latency.
assert stopping(F(101,100),0,0,1)>F(51,100)>stopping(F(1),0,0,1)
print('PASS: six exact physical-contract counterexample checks')

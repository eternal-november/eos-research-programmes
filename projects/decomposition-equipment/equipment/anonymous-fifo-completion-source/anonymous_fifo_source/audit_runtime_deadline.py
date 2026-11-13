"""Independent actual-clock/headroom regression for the reference controller."""
from fractions import Fraction as F
import reference_pipeline as p
_,(_,caps,ledger,plan,reports)=p.trial(2,2,0)
deadline=plan['ready']+10
reserve=caps.compute+caps.status+caps.tail
result=p.control(plan,reports,caps,deadline,deadline-reserve/F(2))
assert not result['fire'] and not result['deadline_met']
try:
    p.control(plan,reports,caps,deadline,max(t for t,b in reports)-F(1,2))
except p.Refusal as error:
    assert str(error)=='INVALID_PUBLIC_REPORT'
else:
    raise AssertionError('accepted future report')
result=p.control(plan,reports,caps,deadline,deadline-reserve)
assert result['fire'] and result['runtime_ready']==deadline
print('PASS: insufficient reserve refuses; future packet refuses; exact reserve boundary accepts.')

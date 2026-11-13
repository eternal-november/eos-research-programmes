"""Exact finite checks for the three illustrative recovery examples.

Run with Python 3. No external dependencies, randomness or network access.
These are finite model checks, not physical experiments or learned guarantees.
"""
from collections import defaultdict
from fractions import Fraction as F
from itertools import product, combinations

# A miswired latch: identical visible history, two incompatible recovery commands.
def return_latch(theta, command):
    return 'home' if theta == command else 'jammed'
for theta in (0, 1):
    assert return_latch(theta, theta) == 'home'
for command in (0, 1):
    assert any(return_latch(theta, command) == 'jammed' for theta in (0, 1))
for numerator in range(101):
    p=F(numerator,100)
    success=(p,1-p)
    assert min(success)<=F(1,2)
assert min(F(1,2),1-F(1,2))==F(1,2)

# Calibrated router: theta is persistent; z is fresh and independent.
rows=[]
for theta,z in product((0,1), repeat=2):
    c=theta; o=theta^z; selected=c^o
    rows.append({'theta':theta,'z':z,'c':c,'o':o,'selected':selected,'mass':F(1,4)})
assert sum(r['mass'] for r in rows if r['selected']==r['z'])==1
for names in combinations(('c','o','z'),2):
    marginal=defaultdict(F)
    for r in rows:
        marginal[tuple(r[n] for n in names)]+=r['mass']
    assert marginal=={bits:F(1,4) for bits in product((0,1),repeat=2)}
product_marginals_success=sum(F(1,8) for c,o,z in product((0,1),repeat=3) if c^o==z)
assert product_marginals_success==F(1,2)
resampled_mode_success=sum(F(1,8) for theta0,theta1,z in product((0,1),repeat=3) if theta0^(theta1^z)==z)
assert resampled_mode_success==F(1,2)
for selected in (0,1):
    assert sum(r['mass'] for r in rows if selected==r['z'])==F(1,2)
# The journal can expose c,o, but need not reveal raw latent sample coordinates.
assert all(r['selected']==(r['c']^r['o']) for r in rows)

# Returning location does not erase an irreversible notification.
def forward(theta,state):
    location,notice=state
    assert location=='home'
    return ('away',notice|theta)
def compensate(state):
    location,notice=state
    assert location=='away'
    return ('home',notice)
initial=('home',0)
for theta in (0,1):
    final=compensate(forward(theta,initial))
    assert final[0]==initial[0]
assert compensate(forward(0,initial))==initial
notified=compensate(forward(1,initial))
assert notified!=initial and notified[1]==1
assert notified[0]==initial[0] and notified[1]!=initial[1]

# Descent obstruction: merged histories require resource sets of different sizes.
pi={'h0':'same_receipt','h1':'same_receipt'}
resource_sizes={'h0':1,'h1':2}
assert pi['h0']==pi['h1'] and resource_sizes['h0']!=resource_sizes['h1']
print('All exact recovery checks passed.')
print('Latch best worst-model success: 1/2')
print('Router retained-joint success: 1')
print('Router product-marginal success: 1/2')
print('Router resampled-persistent-mode success: 1/2')
print('Location restoration: yes; notification erased: no')
print('Unequal resource fibres do not descend to one shared receipt.')

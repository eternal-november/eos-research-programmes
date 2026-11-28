from fractions import Fraction as F
from pathlib import Path
import json,sys

class Comparator:
    """Retired clock known in physical time. Qualified current reading
    given a first exact alignment, finite affine rate, and read-order."""
    def __init__(self,c,eps):
        self.c=c
        self.rate=(1-eps,1+eps)
    def true_time(self,g,slope):
        return self.c+(g-self.c)/slope
    def constrain(self,r,seen,skew):
        assert self.c<r and self.c<seen and 0<=skew
        # A late current sample can have been from any physical clock cut
        # in [r,r+skew] consistent with these observations.
        a,b=self.rate
        nr=(max(a,(seen-self.c)/(r+skew-self.c)),min(b,(seen-self.c)/(r-self.c)))
        return nr if nr[0]<=nr[1] else None
    def cert(self,stamp,rate,held_end,late_deadline):
        if rate is None:return None
        # Minimum local wait guaranteeing the declared conservative release
        # cut. Derive max actual clock readout at the required physical cut.
        high=self.c+rate[1]*(held_end+1-self.c)
        d=stamp-high
        wait=max(0,-(d.numerator//d.denominator))
        slow=self.true_time(stamp+wait,rate[0])
        fast=self.true_time(stamp+wait,rate[1])
        assert fast>=held_end+1
        if wait:assert self.true_time(stamp+wait-1,rate[1])<held_end+1
        return wait,slow<=late_deadline

def scenario(raw):
    h=raw['hulls'][1][1]; core=raw['cores'][1]
    H=75_000
    a=F(70_000_000); r=F(300_000_000)
    c=Comparator(a,F(1,5000))
    g=F(h+10000)
    # Identical exact equal-cut simultaneous witness: the clocks actually
    # agree at this instant regardless of subsequent legal rate.
    assert all(c.true_time(a,q)==a for q in c.rate)
    real=[c.true_time(g,q) for q in reversed(c.rate)]
    assert core[0]<=real[0]<=core[1] and h<real[1]<=h+H
    # Any possible timely late response is observed identically in the
    # early world and still physically contacts the inner bracket.
    max_late=F(a+c.rate[0]*(h+H-a)-g)
    imax=max_late.numerator//max_late.denominator
    assert imax>=0 and c.true_time(g+imax,c.rate[1])<=core[1]
    wide=c.cert(g,c.rate,h,h+H)
    assert not wide[1]
    good=[]; uncertain=[]
    for q in reversed(c.rate):
        exact=a+(r-a)*q
        law=c.constrain(r,exact,0)
        assert law==(q,q)
        good.append(c.cert(g,law,h,h+H))
        # The current clock is read 120 ms after the historical/source
        # reading. It reports its actual stamp, not a simultaneous delta.
        delayed=a+(r+120_000-a)*q
        weak=c.constrain(r,delayed,120_000)
        assert weak[0]<=q<=weak[1]
        uncertain.append(c.cert(g,weak,h,h+H))
    assert all(z[1] for z in good)
    assert not uncertain[1][1]
    return dict(gate=raw['gate'],same_align_wrong_rate_possible=True,
                safe_wide_wait_gate_us=wide[0],timely_late_last_wait_gate_us=imax,
                two_exact_wait_gate_us=good,skew_bounded_wait_gate_us=uncertain,
                actual_early_and_late_motion_times_us=[str(x) for x in real])
for starting in (Path(sys.argv[1])/'PORTAL.jsonl').read_text().splitlines():
    print(json.dumps(scenario(json.loads(starting)),sort_keys=True))

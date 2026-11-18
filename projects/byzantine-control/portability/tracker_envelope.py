"""Exact budgets for the retained scalar tracking law in TRACKER-ENVELOPE.md.

The constructor checks numerical hypotheses. The integrating-factor proof and
source realization are separate; it never infers a powered tracker from a flag.
"""
from fractions import Fraction as Q


def exact(value):
    if type(value) not in (int,Q):
        raise ValueError("Exact int/Fraction required")
    return Q(value)


def interval(value):
    if type(value) is not tuple or len(value)!=2:
        raise ValueError("An exact ordered endpoint pair is required")
    lo,hi=map(exact,value)
    if lo>hi:
        raise ValueError("Reversed interval")
    return lo,hi


def tracker_envelope(*,command,initial,reference,gain_floor,duration,blocks,
                     command_error,reference_slew,initial_error_bound):
    """Return a conditional finite-time envelope; keep the initial residual."""
    a,b=interval(command);ilo,ihi=interval(initial);rlo,rhi=interval(reference)
    gain=exact(gain_floor);time=exact(duration);delta=exact(command_error)
    slew=exact(reference_slew);error=exact(initial_error_bound)
    if gain<=0 or time<0 or delta<0 or slew<0 or error<0:
        raise ValueError("Invalid gain, duration or error envelope")
    if type(blocks) is not int or blocks<=0:
        raise ValueError("Positive exact block count required")
    range_initial=max(Q(0),a-ilo,ihi-b)
    tracking_initial=max(abs(ilo-rhi),abs(ihi-rlo))
    if error<max(range_initial,tracking_initial):
        raise ValueError("Initial residual omits an admitted endpoint")
    decay=(1+gain*time/blocks)**(-blocks)
    retained=error*decay
    lag=slew/gain
    return dict(command_lower=a,command_upper=b,initial_lower=ilo,initial_upper=ihi,
                reference_lower=rlo,reference_upper=rhi,gain_floor=gain,
                settled_duration=time,blocks=blocks,initial_error_bound=error,
                required_range_initial_error=range_initial,
                required_tracking_initial_error=tracking_initial,
                rational_decay_upper=decay,retained_initial_error=retained,
                output_lower=a-retained,output_upper=b+retained,
                command_error=delta,reference_slew=slew,tracking_lag=lag,
                tracking_error=delta+lag+retained)


def checks():
    params=dict(command=(Q(3,10),Q(9,10)),initial=(-1,1),
                reference=(Q(3,10),Q(9,10)),gain_floor=Q(1,100),duration=10000,
                blocks=10,command_error=Q(4,125),reference_slew=Q(4,10**7),
                initial_error_bound=2)
    point=tracker_envelope(**params)
    assert point['retained_initial_error']==Q(2,11**10)
    assert point['tracking_lag']==Q(1,25000)
    assert point['output_lower']<Q(3,10)<point['output_upper']
    assert point['tracking_error']<Q(1,25)
    rejected=0
    for key,value in [('gain_floor',0),('duration',-1),('blocks',True),
                      ('command_error',0.0),('initial_error_bound',Q(18,10)),
                      ('command',(1,-1)),('reference_slew',-1)]:
        try:tracker_envelope(**(params|{key:value}))
        except ValueError:rejected+=1
        else:raise AssertionError('Malformed or inadequate certificate accepted')
    # Exact affine trajectories: any constant-command RC segment has
    # y_end=c+(y_start-c)*rho, with 0<rho<=1. Different initial states stay
    # distinct for every such finite segment; no last-effect cutoff exists.
    trajectories=0
    for rho in (Q(1),Q(1,2),Q(1,11**10)):
        low=Q(3,10)+(Q(-1)-Q(3,10))*rho
        high=Q(9,10)+(Q(1)-Q(9,10))*rho
        assert low<Q(3,10) and high>Q(9,10)
        for start in (Q(-1),Q(0),Q(1)):
            for command in (Q(3,10),Q(6,10),Q(9,10)):
                end=command+(start-command)*rho
                assert Q(3,10)-2*rho<=end<=Q(9,10)+2*rho
                trajectories+=1
    return dict(malformed_or_insufficient_inputs_rejected=rejected,
                exact_affine_cases=trajectories,
                finite_range_countercase='c=.3,y0=-1: y(t)=.3-1.3*exp(-integral gamma)<.3',
                finite_memory_countercase='same c, distinct y0: difference=initial_difference*exp(-integral gamma)',
                source_reachability_not_asserted=True)

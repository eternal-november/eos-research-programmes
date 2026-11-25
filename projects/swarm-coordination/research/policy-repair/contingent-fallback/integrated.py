"""Connect physically scoped mutation reporting to actual live service.

The optional worker may launch at 2 using the known admitted future
receipt law; it does not observe the later mating outcome at launch.
Neither the authorized dispatcher's cut nor its held trace reveals
a hidden source ID when the local event or ticket is missing.
"""
from scoped import FieldPlant,LocalCheck
from service_run import execute
from live import Trace, released
from itertools import product

def build(delay,with_marker,second_possible,mixed=False,required_approval=True):
    W=[]
    for good,late_fault in product((False,True), (False,True) if second_possible else (False,)):
        p=FieldPlant([2,3]);v=LocalCheck([2,3])
        p.prepare(0,4)                            # command only
        assert p.support(0,1,True) is None
        m=p.support(0,2,good)                     # real transfer at tick 3
        assert (m is not None)==good
        seen=("declined",)
        arrival=3+delay
        if good:
            # This second signal is legitimate only at the receipt cut.
            # The helper's source-specific ticket has small scope and does not
            # reveal whether another unrelated producer is delayed.
            closing=p.close_scope(4,4,6) if with_marker else None
            if arrival<=4:v.deliver(m)
            fresh=v.consume(4,4,6,closing)
            seen=("mate",) if fresh=={0} else ("unconfirmed",)
            # The latter is an indistinguishable source view until a timely
            # complete certification, not a separate outcome indication.
            if seen==("unconfirmed",):seen=();arrival=5
        else:
            # Failed mount has its own positive end-of-probe receipt,
            # omitted when the same interface cannot deliver it in time.
            if not with_marker:seen=();arrival=5
        H=p.R[0].current  # private evaluator input, not controller visible
        assert H==(4 if good else 2)
        # Role 1 actually keeps source 3 across both branches. If the
        # first mate succeeded, the earlier held tail at 2 stays live.
        blocked=frozenset({2,3} if good else {3})
        missing=frozenset({4}) if late_fault and good else frozenset()
        if mixed and not good:arrival=3
        # Installed law requires current source signoff before using the
        # shared relay; the remaining static fallback (0,1) is preapproved.
        # This is an authority constraint, not another physical failure.
        authorized=seen in (("mate",),("declined",)) and arrival<=4
        denied=frozenset({H}) if required_approval and not authorized else frozenset()
        G=(frozenset({0,H}),frozenset({1,H}))
        W.append(Trace(G,blocked,seen,4,arrival,missing,denied))
    return tuple(W)

def live_cut(W,finish):
    # Scope: the optional job starts no later than tick two. This is a
    # budgeted certification event, not a wall-clock runtime estimate.
    # Guarded fallback is installed regardless of compute completion.
    reserve_free=(finish is not None and finish<=2 and 0 in released(W,range(5)))
    return execute(W,reserve_free)

def main():
    H=set(range(5));n=0
    for delay,mark,loss in product(range(3),(False,True),(False,True)):
        W=build(delay,mark,loss)
        can=0 in released(W,H)
        assert can==(delay<=1 and mark and not loss)
        held=execute(W,False);assert held
        optional=execute(W,True)
        assert bool(optional)==can
        assert all(len(x)==(4 if can else 3) for x in (optional or held))
        n+=1
    # In this additional closed selection law, absence of the timely
    # positive cue is perfectly informative about physical mating. This
    # still cannot grant permission to use the unconfirmed replacement.
    a=build(2,True,False,mixed=True,required_approval=False)
    b=build(2,True,False,mixed=True,required_approval=True)
    assert execute(a,True) and not execute(b,True) and execute(b,False)
    print(n+2,"end-to-end scoped source proof and physical service comparisons")
    print("even informative silence cannot supply a required live authorization")
    print("same actual role movement, source 4 certificate gap holds just its optional service")
    print("real prior tail retained, other role remains active even when optional work refused")
    S=build(1,True,False)
    for t in (1,2,3,None):
        assert all(len(x)==(4 if t is not None and t<=2 else 3) for x in live_cut(S,t))
    assert all(len(x)==3 for x in live_cut(build(1,True,True),1))
    print("a preinstalled safe path settles 3 when certification misses launch cut 2")
if __name__=="__main__":main()

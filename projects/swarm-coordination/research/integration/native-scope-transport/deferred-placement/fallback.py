"""Keep the old duty when a late/erased designation cannot rescue both arms."""
from control import BAYS, E, choose, safe_pending

def pending_heading(blocked):
    # Available east if possible; otherwise one turn north/south suffices.
    return next(x for x in BAYS if x!=blocked)

def upon(blocked,needed,clock,heading,travel,deadline):
    if clock==1 and needed is None:
        return ('orient',pending_heading(blocked))
    alternative=choose(blocked,needed)
    if alternative is not None and safe_pending(clock,heading,alternative,travel,deadline):
        return ('place',alternative)
    if clock==2 and heading==pending_heading(blocked) and heading!=blocked:
        assert safe_pending(clock,heading,heading,travel,deadline)
        return ('place',heading)
    return ('retain',None)

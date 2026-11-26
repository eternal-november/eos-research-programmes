"""Frozen rule and exact arithmetic boundary for one settled footprint."""
E,S,W,N=range(4)
BAYS=(E,S,N)
def turn_distance(x,y):
    return min((x-y)%4,(y-x)%4)
def choose(blocked,needed):
    if blocked not in BAYS or needed not in BAYS or blocked==needed:
        return None
    return next(x for x in BAYS if x!=blocked and x!=needed)
def best_delay(blocked,heading,travel,deadline):
    candidates=[x for x in BAYS if x!=blocked]
    return deadline-travel-1-max(turn_distance(heading,x) for x in candidates)
def safe_pending(wait,heading,site,travel,deadline):
    return wait+turn_distance(heading,site)+travel+1<=deadline

"""Independent collision and optimal observation-class calculation (not policy)."""
from fractions import Fraction
from collections import defaultdict

def conflict(world, duration=2):
    # Do not call simulator extraction or step. Solve each plane crossing.
    for x, velocity in world:
        t = Fraction(-x, velocity)
        if 0 <= t < duration:
            return True
    return False

def partition(rows):
    """rows: (world, immutable received controller history)."""
    out = defaultdict(list)
    for world, view in rows:
        out[view].append((world, conflict(world)))
    return dict(out)

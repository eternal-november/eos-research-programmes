"""Fixture-local directed phase contact shared by the two return-seat members."""
from fractions import Fraction


def retiring_side(normal, phase, cam, blend, segment, blend_limit):
    # Three strictly geometric tests; the caller still needs the actual funded
    # sample. The contact makes no primitive assertion about data or readiness.
    if not normal or phase != "NORMAL":
        return None
    if segment<=0 or blend_limit<=0:
        raise ValueError("Invalid installed cam range")
    if not 0<=cam<26*segment or not 0<=blend<=blend_limit:
        return None
    side,stage=divmod(int(cam//segment),13)
    offset=cam%segment
    if stage==9 and Fraction(segment,4)<offset<Fraction(3*segment,4) and blend==(1-side)*blend_limit:
        return side
    return None

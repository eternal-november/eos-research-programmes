#!/usr/bin/env python3
"""Exact scalar endpoint envelopes, checked against an independent lattice optimizer."""
from fractions import Fraction as Q
from itertools import combinations, product
import json


def integrate_piecewise(lines, T, chooser):
    knots = {Q(0), T}
    for (b, m), (d, n) in combinations(lines, 2):
        if m != n:
            t = (d-b)/(m-n)
            if 0 < t < T:
                knots.add(t)
    xs = sorted(knots)
    val = lambda t: chooser(b+m*t for b,m in lines)
    return sum((y-x)*(val(y)+val(x))/2 for x,y in zip(xs,xs[1:]))


def rest_interval(x, v, T, a, V):
    if abs(v) > min(V, a*T):
        return None
    U=integrate_piecewise(((V,0),(v,a),(a*T,-a)),T,min)
    L=integrate_piecewise(((-V,0),(v,-a),(-a*T,a)),T,max)
    return x+L,x+U


def walls(x,v,T,a,V,lo,hi):
    if not lo <= x <= hi:
        return None
    z=rest_interval(x,v,T,a,V)
    b=x+v*abs(v)/(2*a)
    if z is None or not lo <= b <= hi:
        return None
    return max(lo,z[0]),min(hi,z[1])


def lattice(v_int, steps, V_int):
    # Units are 1/8 for time and velocity; integer edge cost is 128*displacement.
    if abs(v_int)>V_int:
        return None
    states = {v_int: (0,0)}
    for _ in range(steps):
        nxt = {}
        for u, (m,M) in states.items():
            for w in (u-1,u,u+1):
                if abs(w)>V_int:
                    continue
                n,N=nxt.get(w,(m+u+w,M+u+w))
                nxt[w]=(min(n,m+u+w),max(N,M+u+w))
        states=nxt
    return tuple(Q(z,128) for z in states[0]) if 0 in states else None


def main():
    checks = 0
    for V_int,steps,v_int in product(range(2,13,2),range(0,33,2),range(-14,15,2)):
        exact=rest_interval(Q(0),Q(v_int,8),Q(steps,8),Q(1),Q(V_int,8))
        assert exact==lattice(v_int,steps,V_int),(V_int,steps,v_int)
        checks += 1
    x=Q(3,2); T=Q(2); a=V=Q(1)
    interval=walls(x,Q(1),T,a,V,Q(0),Q(3))
    other=walls(x,-Q(1),T,a,V,Q(0),Q(3))
    assert interval==(Q(7,4),Q(3)) and other==(Q(0),Q(5,4))
    assert walls(Q(11,4),Q(1),T,a,V,Q(0),Q(3)) is None
    assert walls(Q(3,2),Q(1),T,a,V,Q(0),Q(5,2))==(Q(7,4),Q(5,2))
    assert walls(Q(3,2),Q(1),T,a,V,Q(2),Q(3)) is None
    # Prefix witness: accelerate for one time unit, then coast.
    assert a/2+V==x and a==V
    assert rest_interval(Q(0),Q(0),T,a,V)==(-Q(1),Q(1))
    # At the notice state velocity 1, v=1 through next time unit then brake
    # reaches 3; pure braking and holding reaches 2.
    assert x+V+V*V/(2*a)==3 and x+V*V/(2*a)==2
    print(json.dumps(dict(no_wall_lattice_comparisons=checks,corridor=["0","3"],
        moving_at_cut=[str(z) for z in interval],same_position_reversed_velocity=[str(z) for z in other],
        furthest_total_with_rest_at_cut="2",notice_tick="2",end_tick="4"),indent=2))


if __name__=='__main__':
    main()

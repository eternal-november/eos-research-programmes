"""Exact checks for scalar stop velocity stability and the two A-prime held actuator ports."""
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import subprocess
import sys
from types import ModuleType


HERE = Path(__file__).resolve().parent
SOURCE = "07f29286fcfd570299c7610bf9f9acd6267f2852"
GATE_PATH = "theories-and-designs/byzantine-control/portability/gate_source_completion.py"


def frozen_gate():
    """The same Git object is used before and after integration of this note."""
    code = subprocess.check_output(["git", "show", f"{SOURCE}:{GATE_PATH}"], cwd=HERE)
    name = "_projected_flow_gate_source"
    module = ModuleType(name)
    module.__file__ = str(HERE / "gate_source_completion.py")
    sys.modules[name] = module
    exec(compile(code, module.__file__, "exec"), module.__dict__)
    return module


def held_stop_segments(start, force, duration):
    """Return the exact linear pieces of the unit-interval stop for constant forcing."""
    hit = (1 - start) / force if force > 0 else -start / force if force < 0 else duration
    moving = min(duration, hit)
    pieces = [(moving, force), (duration - moving, Q(0))]
    return [(length, velocity) for length, velocity in pieces if length > 0]


def stop_pair(left, right, rows):
    initial = abs(left - right)
    drifts = velocities = reactions = Q(0)
    for f, g, length in rows:
        left_parts = held_stop_segments(left, f, length)
        right_parts = held_stop_segments(right, g, length)
        times = {Q(0), length, left_parts[0][0], right_parts[0][0]}
        points = sorted(times)
        for start, end in zip(points, points[1:]):
            dt = end - start
            v = left_parts[0][1] if start < left_parts[0][0] else left_parts[-1][1]
            w = right_parts[0][1] if start < right_parts[0][0] else right_parts[-1][1]
            old_distance = abs(left - right)
            left += dt*v
            right += dt*w
            dn = abs((f - v) - (g - w))
            drifts += dt*abs(f - g)
            reactions += dt*dn
            velocities += dt*abs(v - w)
            assert 0 <= left <= 1 and 0 <= right <= 1
            assert abs(left-right) + dt*dn <= old_distance + dt*abs(f-g)
    assert abs(left-right) + reactions <= initial + drifts
    assert velocities <= initial + 2*drifts
    return drifts, reactions, velocities


def stop_checks():
    positions = (Q(0), Q(1, 2), Q(1))
    forces = (Q(-3), Q(-1), Q(0), Q(1), Q(3))
    count = 0
    for x, y, f, g in product(positions, positions, forces, forces):
        stop_pair(x, y, ((f, g, Q(1, 3)), (-g, f, Q(2, 3)), (g, -f, Q(1, 4))))
        count += 1
    # Identical initial states, different first pulses, equal second pulses.
    # The velocity estimate attains its factor two exactly.
    eps = Q(1, 16)
    assert stop_pair(1-eps, 1-eps, ((1, 0, eps), (1, 1, eps))) == (eps, eps, 2*eps)
    return count


def actuator_checks():
    gate = frozen_gate()
    params, _, _ = gate.parameters()
    state = gate.Completion(params)
    clamp = list(state.positions).index("clamp0")
    effort = [Q(0)] * len(state.route)

    def select(side, dest, value):
        assert state.apply(state.capture("local-actuator", side, (dest, value))) == "local-actuator/held-plane"

    def rates():
        return gate.actuator_rates(state, effort)

    select(0, clamp, 68)
    select(1, clamp, 68)
    state.E[:] = [Q(1000), Q(1000)]
    state.positions["clamp0"] = state.limits["clamp0"] - Q(1, 1024)
    free = rates()
    state.positions["clamp0"] = state.limits["clamp0"]
    stopped = rates()
    assert free["velocities"]["clamp0"] == Q(11, 10)
    assert sum(row["draw"] for row in free["banks"]) == Q(1506, 5)
    assert stopped["velocities"]["clamp0"] == 0
    assert [row["draw"] for row in stopped["banks"]] == [1, 1]
    assert stopped["mechanical_dissipation"] == 0

    # Co-located banks can be driven in opposite directions. One backdrives
    # into a full E while the other pays positive conjugate work.
    select(0, clamp, 10)
    select(1, clamp, -68)
    state.E[0] = params["EMAX"]
    state.positions["clamp0"] -= 1
    back = rates()
    a, b = back["banks"]
    assert (a["mechanical_power"], a["returned"], a["draw"], a["overflow_heat"]) == (-11, Q(11,2), 1, Q(9,2))
    assert b["mechanical_power"] == Q(374, 5) and b["draw"] == Q(753, 5)
    assert back["mechanical_dissipation"] == sum(row["mechanical_power"] for row in (a,b))
    assert sum(row["energy_derivative"] + row["heat"] + row["overflow_heat"] for row in (a,b)) + back["mechanical_dissipation"] == 0

    seat = list(state.positions).index("seat0:0")
    carrier = list(state.positions).index("carrier0")
    select(0, seat, 68)
    select(1, carrier, 68)
    state.apply(state.capture("jam", "seat0:0", True))
    jam = rates()
    assert jam["velocities"]["seat0:0"] == jam["velocities"]["carrier0"] == 0
    assert [row["draw"] for row in jam["banks"]] == [1, 1]
    state.E[0] = Q(0)
    empty = rates()["banks"][0]
    assert empty["draw"] == empty["returned"] == empty["force"] == 0

    vmax = Q(11, 10)
    signal_abs = len(state.route)*Q(11, 5)*vmax
    disturbance_abs = state.driven*vmax*vmax
    mechanical_power = signal_abs + disturbance_abs + 2*gate.LOCAL_ACTUATOR_LIMIT*vmax
    assert (len(state.route), state.driven, len(state.positions)) == (14000, 175, 335)
    assert mechanical_power == Q(684827, 20)
    assert mechanical_power + 2*(gate.LOCAL_ACTUATOR_LIMIT*vmax+1) == Q(687859, 20)
    return sum(row["draw"] for row in free["banks"]), mechanical_power


if __name__ == "__main__":
    if not __debug__ or sys.version_info[:2] != (3,12):
        raise SystemExit("Run unoptimized Python 3.12")
    pairs = stop_checks()
    draw, heat = actuator_checks()
    print(f"{pairs} projected trajectory pairs, sharp L1 factor 2")
    print(f"Two actual A-prime ports, gross draw {draw}/q and fixture mechanical dissipation at most {heat}/q")

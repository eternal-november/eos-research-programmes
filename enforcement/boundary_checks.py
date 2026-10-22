"""Exact witnesses for BOUNDARIES.md; no continuous-hardware or novelty claim."""
from fractions import Fraction as F
from itertools import product
import json
from pathlib import Path


def require(condition, explanation):
    if not condition:
        raise RuntimeError(explanation)


def speed(v, torque, brake):
    return max(F(0), F(9, 10) * v + torque - brake)


def heat(h, v, brake):
    return F(9, 10) * h + F(1, 10) * brake * v


def checks():
    V, T, r, b = F(10), F(13, 10), F(6), F(1, 5)
    profiles = tuple(product((0, 1), repeat=3))
    blind_success = []
    rejected_by = {'conduct': 0, 'speed': 0}
    for commands in profiles:
        low_legal = all(c == 0 or F(1) >= r for c in commands)
        high_safe = speed(V, T, b * sum(commands)) <= V
        if low_legal and high_safe:
            blind_success.append(commands)
        if not low_legal:
            rejected_by['conduct'] += 1
        if not high_safe:
            rejected_by['speed'] += 1
    require(not blind_success, 'Blind constant first action unexpectedly solves both worlds')
    informative = {}
    for v in (F(1), V):
        # Adversarial error at each intact local median, including conflicting values.
        outcomes = []
        for errors in product((F(-1, 10), F(0), F(1, 10)), repeat=3):
            cmd = tuple(int(v + error >= F(41, 5)) for error in errors)
            require(all(c == 0 or v >= r for c in cmd), 'Factive conduct failed')
            nxt = speed(v, T, b * sum(cmd))
            require(nxt <= V, 'Timely informative first step failed')
            outcomes.append(nxt)
        informative[str(v)] = {'min_next': str(min(outcomes)), 'max_next': str(max(outcomes))}
    # Full-information physical-authority obstruction: even maximum surviving braking fails.
    trace = [F(1)]
    while trace[-1] <= V and len(trace) < 1000:
        trace.append(speed(trace[-1], T, F(1, 5)))
    require(trace[-1] > V, 'Expected finite authority violation absent')
    delayed = speed(V, T, F(0))
    require(delayed == F(103, 10), 'Delay witness changed')
    joint_safe = []
    for commands in profiles:
        force = b * sum(commands)
        if speed(V, T, force) <= V and heat(F(1), V, force) <= F(1):
            joint_safe.append(commands)
    require(not joint_safe, 'Expected joint heat/speed conflict absent')
    # Algebra establishes exclusion for every real force, not just these binary profiles.
    required_force = T - F(1, 10) * V
    thermal_force = (1 - F(9, 10)) * F(1) / (F(1, 10) * V)
    require(required_force > thermal_force, 'Continuous force interval unexpectedly nonempty')
    # Persistent forcing proof is in prose; this trace is a reproducible member.
    hs = [F(0)]
    while hs[-1] <= 12 and len(hs) < 2000:
        hs.append(F(999, 1000) * hs[-1] + F(1, 50))
    require(hs[-1] > 12, 'Expected persistent heat violation absent')
    # Reviewer counterexample: the normal-torque upper premise cannot be omitted.
    missing_premise = [F(1)]
    while missing_premise[-1] <= V and len(missing_premise) < 1000:
        missing_premise.append(speed(missing_premise[-1], F(2), 3*b))
    require(missing_premise[-1] > V, 'Missing normal-torque premise witness absent')
    # Naive product of two local heat allowances is not a shared-resource theorem.
    composed_heat = F(9, 10)*6 + F(3, 5) + F(3, 5)
    require(composed_heat == F(33, 5) and composed_heat > 6, 'Shared heat witness changed')
    return {
        'scope': 'Exact rational finite witnesses; general quantified arguments are in BOUNDARIES.md',
        'blind_initial_profiles': len(profiles), 'blind_winning_profiles': len(blind_success),
        'blind_rejection_counts_overlapping': rejected_by, 'informative_initial_steps': informative,
        'authority_failure_tick': len(trace)-1, 'authority_failure_speed': str(trace[-1]),
        'unavoidable_delayed_next_speed': str(delayed),
        'heat_speed_binary_winners': len(joint_safe), 'minimum_containment_force': str(required_force),
        'maximum_thermally_allowed_force': str(thermal_force),
        'effective_but_inadmissible_force': str(F(2, 5)),
        'effective_next_speed': str(speed(V, T, F(2, 5))),
        'inadmissible_next_heat': str(heat(F(1), V, F(2, 5))),
        'persistent_heat_failure_tick': len(hs)-1,
        'persistent_heat_context': {'devices': 2, 'delivery_coefficients': [1, 1], 'motor_output_faults': 1, 'hostile_brakes_on_surviving_device': 1, 'beta': '999/1000', 'lower_heat_input': '1/50', 'protected_heat_limit': 12, 'actual_service_floor': 1},
        'missing_normal_torque_bound_failure_tick': len(missing_premise)-1,
        'naive_shared_heat': str(composed_heat),
    }


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = checks()
    rendered = json.dumps(result, indent=2, sort_keys=True) + '\n'
    path = Path(__file__).with_name('boundary_results.json')
    if args.write:
        path.write_text(rendered, encoding='utf-8')
    else:
        require(path.read_text(encoding='utf-8') == rendered, 'Saved boundary results differ')
    print(rendered)

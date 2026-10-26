"""Exact-rational W0 probes; no source admission or closed-loop simulation."""
from fractions import Fraction as F
from itertools import product
from hashlib import sha256
from pathlib import Path
import argparse
import json
import sys

if sys.flags.optimize:
    raise RuntimeError('Unoptimized Python is required')

HERE = Path(__file__).resolve().parent


def require(p, reason):
    if not p:
        raise RuntimeError(reason)


def nominal(x):
    return min(F(9, 10), max(F(3, 10), F(3, 5) + 2 * (x - F(1, 2))))


def support_bound(x, error, bad_fraction):
    # Actual coordinatewise output interval, not a joint global convexity test.
    return ((1 - bad_fraction) * nominal(x - error) - bad_fraction,
            (1 - bad_fraction) * nominal(x + error) + bad_fraction)


def run():
    b, error, disturbance = F(1, 12), F(1, 50), F(1, 25)
    lower, upper = F(7, 20), F(13, 20)
    lower_flow = support_bound(lower, error, b)[1]
    upper_flow = support_bound(upper, error, b)[0]
    service = (1 - b) * F(3, 10) - b
    require(upper_flow > F(3, 5) + disturbance, 'Upper boundary margin fails')
    require(lower_flow < F(3, 5) - disturbance, 'Lower boundary margin fails')
    require(service > F(1, 10), 'Delivered service fails')
    # A full inward collar proves more than a derivative claim at an isolated point.
    collar = F(1, 100)
    upper_collar_flow = support_bound(upper - collar, error, b)[0]
    lower_collar_flow = support_bound(lower + collar, error, b)[1]
    diffusion_outward = 3 * F(1, 50) * collar
    upper_margin = upper_collar_flow - F(3, 5) - disturbance - diffusion_outward
    lower_margin = F(3, 5) - disturbance - lower_collar_flow - diffusion_outward
    require(upper_margin > 0 and lower_margin > 0, 'Uniform collar margin fails')
    inversions = 0
    for x, y in product((lower, F(1, 2), upper), repeat=2):
        for es, ed in product((-error, error), repeat=2):
            s, d = x + y + es, x - y + ed
            require(abs((s + d) / 2 - x) <= error and abs((s - d) / 2 - y) <= error,
                    'Complementary row inversion loses coordinate error bound')
            inversions += 1
    left, right = (F(2, 5), F(3, 5)), (F(3, 5), F(2, 5))
    require(sum(left) == sum(right) and left[0] - left[1] != right[0] - right[1],
            'Complementarity witness fails')
    require(tuple(map(nominal, left)) != tuple(map(nominal, right)), 'Missing row has no response consumer')
    fallback_lo = (1 - b) * F(3, 5) - b
    fallback_hi = (1 - b) * F(3, 5) + b
    full_diffusion = 3 * F(1, 50) * (upper - lower)
    startup_upper_rate = F(3, 5) + disturbance + full_diffusion - fallback_lo
    startup_lower_rate = fallback_hi - F(3, 5) + disturbance + full_diffusion
    tau, entry_quanta = F(1, 250000), 32768 + 81 + 1000
    require(nominal(F(3, 5) - error) >= F(3, 5), 'Mixed upper entry worsens fallback')
    require(nominal(F(2, 5) + error) <= F(3, 5), 'Mixed lower entry worsens fallback')
    require(startup_upper_rate * tau * entry_quanta < F(1, 20), 'Startup escapes upper face')
    require(startup_lower_rate * tau * entry_quanta < F(1, 20), 'Startup escapes lower face')
    require(F(16384) / F(101, 100) > 1000, 'Shortest startup wait fails trial freshness budget')
    # Endpoints suffice for multilinear dependence on output, mix and coefficients.
    mixtures = 0
    for bad, actual, ea, eb, mix in product((F(0), b), (lower, upper),
                                          (-error, error), (-error, error),
                                          (F(0), F(1, 7), F(1, 2), F(1))):
        a, c = nominal(actual + ea), nominal(actual + eb)
        value = (1 - mix) * a + mix * c
        lo, hi = nominal(actual - error), nominal(actual + error)
        require(lo <= value <= hi, 'Coordinatewise mixed output escapes its interval')
        actual_lo, actual_hi = (1 - bad) * value - bad, (1 - bad) * value + bad
        envelope = support_bound(actual, error, bad)
        require(envelope[0] <= actual_lo <= actual_hi <= envelope[1], 'Host aggregation fails')
        mixtures += 1
    # Permission belongs to actual load/isolation, not to a certificate variable.
    coupler = 0
    for force, parasitic, mix in product((F(0), F(1), F(2)),
                                         (F(0), F(1, 5)), (F(9, 10), F(1))):
        old_load = (1 - mix) * force + parasitic
        require(old_load <= F(2, 5), 'Declared coupler cannot unload old side')
        coupler += 1
    same_op = {'permitted_load': F(2, 5), 'prohibited_load': F(6, 5),
               'same_isolation': F(9, 10)}
    require(same_op['permitted_load'] <= 1 < same_op['prohibited_load'], 'Rule lost distinction')
    # Witnesses defeat tempting stronger claims without changing the numeric mission.
    counter = {
        'independent_global_convex_mixing': {'safe_vectors': [[1, 0], [0, 1]],
                                           'coordinatewise_mixture': [1, 1],
                                           'violated_bound': 'u1+u2<=1'},
        'unmodeled_load_path': {'mix': F(1), 'extra_load': F(6, 5),
                               'actual_old_load': F(6, 5)},
        'one_quarter_bad': {'upper_minimum_flow': support_bound(upper, error, F(1, 4))[0],
                           'outward_drift_at_upper': F(3, 5) + disturbance - support_bound(upper, error, F(1, 4))[0]},
        'all_stopped': {'actual_flow': 0, 'required_flow': F(1, 10)},
        'constant_midpoint_control': {'command': F(3, 5), 'admitted_inflow': F(61, 100),
                                      'drift_on_uniform_state': F(1, 100)},
    }
    require(counter['one_quarter_bad']['outward_drift_at_upper'] > 0, 'Bad-support countercase fails')
    return {
        'status': 'passed conditional source probes; source suppliers open',
        'upper_boundary_minimum_flow': upper_flow,
        'lower_boundary_maximum_flow': lower_flow,
        'minimum_delivered_service': service,
        'upper_collar_inward_margin': upper_margin,
        'lower_collar_inward_margin': lower_margin,
        'coordinatewise_mixture_cases': mixtures,
        'load_transfer_cases': coupler,
        'complementary_row_inversion_cases': inversions,
        'same_sum_different_feedback': {'states': [left, right],
                                        'commands': [tuple(map(nominal, left)), tuple(map(nominal, right))]},
        'conditional_commissioning': {'upper_outward_rate': startup_upper_rate,
                                       'lower_outward_rate': startup_lower_rate,
                                       'maximum_entry_quanta': entry_quanta,
                                       'maximum_upper_escape_band_travel': startup_upper_rate * tau * entry_quanta,
                                       'maximum_lower_escape_band_travel': startup_lower_rate * tau * entry_quanta,
                                       'initial_face_margin': F(1, 20)},
        'fixed_rule_distinction': same_op,
        'countercases': counter,
        'inputs': {name: sha256((HERE / name).read_text(encoding='utf-8').replace('\r\n', '\n').encode()).hexdigest()
                   for name in ('source_probe.py', 'INSTANCE.md')},
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--check', action='store_true')
    group.add_argument('--write', action='store_true')
    args = parser.parse_args()
    record = json.loads(json.dumps(run(), default=str))
    path = HERE / 'source_probe_results.json'
    if args.write:
        path.write_text(json.dumps(record, indent=2) + '\n', encoding='utf-8')
    else:
        require(record == json.loads(path.read_text(encoding='utf-8')), 'Source probe record differs')
    print(record['status'])

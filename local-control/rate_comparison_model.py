"""Exact same-adversary comparison of conditional return certificates."""
from __future__ import annotations

import argparse
from fractions import Fraction as F
from hashlib import sha256
import json
from math import floor
from pathlib import Path
import subprocess
import sys

if sys.flags.optimize:
    raise RuntimeError('Unoptimized Python is required')

HERE = Path(__file__).resolve().parent
PREFIX = 'theories-and-designs/byzantine-control/local-control/'
BASE = '1d4732e26c6ff31d69c1e32d542fb13f327acacd'
EXPANDED = '873bfd7f11baa614ff82057a62af1ca9df808027'


def require(ok, message):
    if not ok:
        raise AssertionError(message)


def normalized(raw):
    return raw.decode('utf-8-sig').replace('\r\n', '\n')


def snapshot(commit, name):
    return normalized(subprocess.check_output(['git', 'show', commit + ':' + PREFIX + name], cwd=HERE))


def frozen_record(commit, name):
    raw = snapshot(commit, name)
    record = json.loads(raw)
    for source, digest in record['sources'].items():
        require(sha256(snapshot(commit, source).encode()).hexdigest() == digest,
                'Frozen input manifest differs: ' + source)
    return record, dict(commit=commit, record=name, sha256=sha256(raw.encode()).hexdigest(),
                        checked_source_count=len(record['sources']))


def cover(p, c, burst, rate, H, W):
    require(isinstance(p, int) and isinstance(c, int), 'Incident counts must be integers')
    require(min(p, c, burst, rate, H, W) >= 0, 'Negative envelope parameter')
    return p + c + floor(burst + rate*(H+W))


def threshold_checks():
    cases = 0
    for p in range(3):
        for c in range(3):
            for burst in (F(0), F(1, 2), F(1), F(3)):
                for target in range(10):
                    for H, W in ((F(1), F(1)), (F(3, 2), F(7, 3)), (F(5), F(0))):
                        boundary = (target-p-c+1-burst)/(H+W)
                        for rate in {F(0), F(1, 10), max(F(0), boundary),
                                     max(F(0), boundary-F(1, 100)), max(F(0), boundary+F(1, 100))}:
                            lhs = cover(p, c, burst, rate, H, W) <= target
                            rhs = burst + rate*(H+W) < target-p-c+1
                            require(lhs == rhs, 'Floor threshold equivalence failed')
                            cases += 1
    endpoint = [cover(1, 2, 3, r, 1, 1) for r in (F(49, 100), F(1, 2), F(51, 100))]
    require(endpoint == [6, 7, 7], 'Strict threshold endpoint was lost')
    return dict(rational_cases=cases, lambdaH_probes=['49/100', '1/2', '51/100'], covers=endpoint)


def raw_witness_checks():
    cases = 0
    traces = []
    for burst in (1, 2, 3, 5):
        for rate in (F(0), F(1, 7), F(1), F(7, 3)):
            for length in (F(0), F(1), F(7, 3), F(11)):
                events = [F(0)]*burst
                if rate:
                    events += [F(k)/rate for k in range(1, floor(rate*length)+1)]
                require(len(events) == floor(burst+rate*length), 'Witness not sharp at full window')
                points = sorted({F(0), length, *events})
                points += [(a+b)/2 for a, b in zip(points, points[1:])]
                points = sorted(set(points))
                for a in points:
                    for b in points:
                        if b < a:
                            continue
                        count = sum(a <= t <= b for t in events)
                        require(count <= floor(burst+rate*(b-a)), 'Closed endpoint witness violates raw envelope')
                        cases += 1
                # Two initially held tokens release before the ordered zero-duration acquisitions.
                occupancy = [2, 1, 0]
                for _ in events:
                    occupancy.extend((1, 0))
                require(max(occupancy) == 2, 'Event ordering hides excess occupancy')
                traces.append(dict(burst=burst, rate=rate, window=length, acquisitions=len(events),
                                   raw_distinct_cover=1+2+len(events), direct_occupancy=max(occupancy)))
    return dict(closed_interval_cases=cases, finite_witnesses=traces,
                interpretation='sharp raw token cover; no assertion that physical repair takes its entire upper bound')


def serial(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {k: serial(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [serial(v) for v in value]
    return value


def generate():
    baseline, base_binding = frozen_record(BASE, 'geometry_results.json')
    expanded, expanded_binding = frozen_record(EXPANDED, 'barrier_results.json')
    H0 = F(baseline['timing']['conditional_return_H'])
    H1 = F(expanded['compiler']['return_rebinding']['conditional_H'])
    rate0, rate1 = 1/(10*H0), 1/(10*H1)
    fixed_old_rate = [cover(1, 2, 3, rate0, h, h) for h in (H0, H1)]
    fixed_new_rate = [cover(1, 2, 3, rate1, h, h) for h in (H0, H1)]
    require(fixed_old_rate == [6, 4354] and fixed_new_rate == [6, 6], 'Frozen numerical comparison changed')
    require(H1 > H0 and rate1 < rate0, 'Comparison does not expose the rate tradeoff')
    world_age = expanded['compiler']['timing']['world_observation_to_last_effect']
    require(world_age == baseline['compiler']['processing_certificate']['world_observation_to_last_effect'],
            'Claimed unchanged WORLD age differs')
    result = dict(status='derived fixed-adversary certificate comparison; not source admission or mission impossibility',
        inputs=[base_binding, expanded_binding], threshold=threshold_checks(), raw_witness=raw_witness_checks(),
        comparison=dict(baseline_H=H0, expanded_H=H1, return_bound_ratio=H1/H0,
            baseline_selected_rate=rate0, expanded_selected_rate=rate1, selected_rate_ratio=rate1/rate0,
            baseline_fixed_rate_covers=fixed_old_rate, expanded_fixed_rate_covers=fixed_new_rate,
            selected_dimensionless_loads=[rate0*H0, rate1*H1], certificate_boundary_lambdaH=F(1, 2),
            selected_to_boundary_ratio=5,
            baseline_work_window_over_H=F(baseline['timing']['work'])/H0,
            expanded_work_window_over_H=F(expanded['compiler']['timing']['local_nontransferable_work'])/H1,
            unchanged_world_effect_age=world_age,
            expanded_physical_supplier=expanded['current_cut_binding']['commit'],
            unavailable_claims=['optimal repair time', 'mission failure above selected rate', 'fixed physical plant after m scaling', 'source admission']))
    result['sources'] = {name: sha256(normalized((HERE/name).read_bytes()).encode()).hexdigest()
                         for name in ('RATE-COMPARISON.md', 'rate_comparison_model.py', 'RETURN.md')}
    return serial(result)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    choice = parser.add_mutually_exclusive_group(required=True)
    choice.add_argument('--write', action='store_true')
    choice.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = generate()
    target = HERE/'rate_comparison_results.json'
    if args.write:
        target.write_text(json.dumps(result, indent=2, sort_keys=True)+'\n', encoding='utf-8', newline='\n')
    else:
        require(json.loads(target.read_text(encoding='utf-8-sig')) == result, 'Rate comparison record differs')
    print('rate comparison record ' + ('written' if args.write else 'matches'))


if __name__ == '__main__':
    main()

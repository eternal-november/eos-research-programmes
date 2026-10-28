"""Raw-history cover checks. No algorithm here repairs a domain."""
from dataclasses import dataclass
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from pathlib import Path
import argparse
import json
import os
import re
import subprocess
import sys

if sys.flags.optimize:
    raise RuntimeError('Unoptimized Python is required')

HERE = Path(__file__).resolve().parent
LEAN = Path(os.environ['USERPROFILE']) / '.elan/toolchains/leanprover--lean4---v4.33.0/bin/lean.exe'


def require(p, message):
    if not p:
        raise RuntimeError(message)


@dataclass(frozen=True)
class Episode:
    domain: int
    acquire: F
    release: F


def before(episodes, t):
    return {e.domain for e in episodes if e.acquire < t <= e.release}


def acquisitions(episodes, a, b):
    return {e.domain for e in episodes if a <= e.acquire <= b}


def point_cover(episodes, persistent, debt, t, horizon):
    a = max(F(0), t - horizon)
    return persistent | before(episodes, a) | acquisitions(episodes, a, t) | (debt if t < horizon else set())


def window_cover(episodes, persistent, debt, start, width, horizon):
    a = max(F(0), start - horizon)
    return persistent | before(episodes, a) | acquisitions(episodes, a, start + width) | (debt if start < horizon else set())


def cuts(episodes, start, width, horizon):
    finish = start + width
    points = {start, finish}
    for e in episodes:
        points.update(t for t in (e.acquire, e.acquire + horizon, e.release + horizon)
                      if start <= t <= finish)
    if start <= horizon <= finish:
        points.add(horizon)
    ordered = sorted(points)
    return sorted(points | {(a+b)/2 for a, b in zip(ordered, ordered[1:])})


def check_lean():
    result = subprocess.run([str(LEAN), str(HERE / 'Return.lean')],
                            cwd=HERE, text=True, capture_output=True)
    require(result.returncode == 0, result.stdout + result.stderr)
    reported = re.findall(r"'LocalReturn\.(\w+)' depends on axioms: \[([^]]*)\]", result.stdout)
    expected = {'enlarge_cover', 'rolling_window_cover', 'clipped_window_cover',
                'initial_debt_window', 'strict_return_slack'}
    require({name for name, _ in reported} == expected and len(reported) == 5,
            'Lean declaration inventory changed')
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    for _, ax in reported:
        require({v.strip() for v in ax.split(',') if v.strip()} <= allowed, 'Unexpected proof axiom')
    return [{'declaration': name, 'axioms': [v.strip() for v in ax.split(',') if v.strip()]}
            for name, ax in reported]


def run():
    reports = check_lean()
    first = [Episode(0, F(-1), F(end)) for end in range(5)]
    second = [Episode(1, F(start), F(end)) for start in range(4) for end in range(start, 5)]
    third = [Episode(2, F(start), F(end)) for start in range(1, 4) for end in range(start, 5)]
    traces = windows = checks = 0
    for episodes in product(first, second, third):
        traces += 1
        for H, s, W in product((F(1), F(2), F(4)),
                               (F(0), F(1, 2), F(1), F(2), F(4)),
                               (F(0), F(1, 2), F(1), F(2))):
            windows += 1
            outer = window_cover(episodes, {4}, {3}, s, W, H)
            for t in cuts(episodes, s, W, H):
                inner = point_cover(episodes, {4}, {3}, t, H)
                require(inner <= outer, 'Raw window containment failed')
                checks += 1
    old = (Episode(0, F(-1), F(0)),)
    good = point_cover(old, set(), set(), F(1, 2), F(1))
    # Wrongly sampling AFTER boundary releases and omitting boundary acquisitions.
    incorrect = {e.domain for e in old if e.acquire <= 0 < e.release} | {
        e.domain for e in old if 0 < e.acquire <= F(1, 2)}
    require(good == {0} and incorrect == set(), 'Endpoint omission witness failed')
    unrepaired = point_cover((Episode(0, F(0), F(1)),), set(), set(), F(4), F(2))
    bad_code_still_present = True  # The only raw event wrote bad code; no write/cut occurred afterward.
    require(not unrepaired and bad_code_still_present, 'Bookkeeping was mistaken for a repair operation')
    debt = set(range(6))
    burst = (Episode(6, F(0), F(2)), Episode(7, F(0), F(2)))
    overloaded = point_cover(burst, set(), debt, F(0), F(10))
    require(len(overloaded) == 8 and 7 * F(22, 5) + 1 > 28, 'Initial-debt force witness failed')
    intervals = [(F(20*k), F(20*k+30)) for k in range(8)]
    for t in (F(k, 2) for k in range(281)):
        require(any(a <= t and t+10 <= b for a, b in intervals), 'Local ready-cover witness fails')
    require(not any(a <= 20 and 60 <= b for a, b in intervals), 'A bank unexpectedly covers the attempt')
    return {
        'status': 'passed raw bookkeeping and countermodels; actual return remains unproved',
        'lean': reports,
        'episode_histories': traces,
        'consumer_windows': windows,
        'boundary_and_cell_checks': checks,
        'countermodels': {
            'entry_release_omitted': {'correct_cover': sorted(good), 'incorrect_cover': sorted(incorrect)},
            'no_repair': {'raw_cover_at_4': sorted(unrepaired), 'bad_code_present': bad_code_still_present},
            'initial_debt_plus_new_burst': {'domains': sorted(overloaded), 'seven_host_opposition': '159/5', 'stiction': 28},
            'no_fixed_bank': {'local_work': 10, 'attempt': [20, 60], 'bank_interval_length': 30},
        },
        'inputs': {name: sha256((HERE / name).read_text(encoding='utf-8').replace('\r\n', '\n').encode()).hexdigest()
                   for name in ('RETURN.md', 'Return.lean', 'return_model.py')},
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--check', action='store_true')
    group.add_argument('--write', action='store_true')
    args = parser.parse_args()
    record = run()
    path = HERE / 'return_results.json'
    if args.write:
        path.write_text(json.dumps(record, indent=2) + '\n', encoding='utf-8')
    else:
        require(record == json.loads(path.read_text(encoding='utf-8')), 'Frozen return record differs')
    print(json.dumps({key: record[key] for key in ('status', 'episode_histories', 'consumer_windows', 'boundary_and_cell_checks')}))

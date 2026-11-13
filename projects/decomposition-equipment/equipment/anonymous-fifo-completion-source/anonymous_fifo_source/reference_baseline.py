"""Partition-agnostic reference baselines (standard library; exact arithmetic).

Enumerates every partition of addressed jobs: no true routing is accepted.
The hull relaxation intentionally can refuse schedules that are actually safe.
Strictly distinct releases are required, so an unknown simultaneous FIFO tie
priority is never smuggled into a recurrence. Intended for small n only.
"""
from fractions import Fraction as F


def partitions(n):
    """Canonical restricted-growth strings, each set partition exactly once."""
    if n == 0:
        yield ()
        return
    def rec(prefix):
        if len(prefix) == n:
            yield tuple(prefix)
            return
        for label in range(max(prefix) + 2):
            yield from rec(prefix + [label])
    yield from rec([0])


def _validate(bounds, J, releases):
    if len(bounds) != len(releases) or not bounds:
        raise ValueError('one bound and release per job required')
    if J < 0 or any(lo < 0 or hi <= 0 or lo > hi for lo, hi in bounds):
        raise ValueError('invalid duration or delay bound')
    if len(set(releases)) != len(releases):
        raise ValueError('strict releases required: unknown FIFO ties not modeled')


def robust_windows(bounds, J, releases):
    """Hull of per-job report windows over ALL unknown queue partitions.

    Inputs are only observed duration bounds, trusted jitter bound and chosen
    releases. A job's duration is enclosed independently, conservatively even
    when repeated operation durations would impose additional correlations.
    """
    bounds = [(F(lo), F(hi)) for lo, hi in bounds]
    releases, J = list(map(F, releases)), F(J)
    _validate(bounds, J, releases)
    n = len(bounds)
    hulls = [None] * n
    for routing in partitions(n):
        busy = {}
        for i in sorted(range(n), key=lambda k: releases[k]):
            q = routing[i]
            blo, bhi = busy.get(q, (releases[i], releases[i]))
            lo = max(releases[i], blo) + bounds[i][0]
            hi = max(releases[i], bhi) + bounds[i][1]
            busy[q] = lo, hi
            report = lo, hi + J
            old = hulls[i]
            hulls[i] = report if old is None else (min(old[0], lo), max(old[1], hi + J))
    return hulls



def robust_windows_hull(bounds, J, releases):
    """Same marginal hull as exhaustive partitions, in O(n log n).

    The earliest endpoint is attained with this job alone on a queue. The
    latest endpoint is attained when ALL jobs share one FIFO: inserting every
    earlier release and increasing every duration to its upper bound cannot
    advance a completion in the max-plus FIFO recurrence. Distinct releases
    fix that FIFO order. Different jobs' extrema need not be jointly attained;
    hence this is a marginal overapproximation, not an exact matching model.
    """
    bounds = [(F(lo), F(hi)) for lo, hi in bounds]
    releases, J = list(map(F, releases)), F(J)
    _validate(bounds, J, releases)
    result, busy = [None] * len(bounds), min(releases)
    for i in sorted(range(len(bounds)), key=lambda k: releases[k]):
        busy = max(busy, releases[i]) + bounds[i][1]
        result[i] = (releases[i] + bounds[i][0], busy + J)
    return result

def global_stagger(bounds, J, Q, spacing=None):
    """Choose all-address grid staggering, then certify without routing truth.

    The default spacing exceeds each solo-window width plus jitter; this is
    only a candidate, not a guarantee against hidden queue contention. Returns
    overlap status and robust worst-case completion envelope honestly.
    """
    Q, J = F(Q), F(J)
    if Q <= 0:
        raise ValueError('clock quantum must be positive')
    width = max(F(hi) - F(lo) for lo, hi in bounds) + J
    spacing = (width // Q + 1) * Q if spacing is None else F(spacing)
    if spacing <= 0 or spacing % Q:
        raise ValueError('positive grid spacing required')
    releases = [i * spacing for i in range(len(bounds))]
    windows = robust_windows_hull(bounds, J, releases)
    disjoint = all(a[1] < b[0] or b[1] < a[0]
                   for i, a in enumerate(windows) for b in windows[i + 1:])
    return {'releases': releases, 'windows': windows,
            'unique_timestamp_binding': disjoint,
            'report_drain_bound': max(hi for _, hi in windows),
            'method': 'all-partitions marginal hull via monotonicity'}


def serial_and_drain(bounds, J, Q=1, physical_tail=0):
    """Available serial baseline using each acquired upper bound, including lag.

    All reports at a bound endpoint are processed before the next release.
    Grid rounding and a supplied physical tail are charged after each job.
    This baseline needs no partition; safe no-actuation calibration is separate.
    """
    Q, J, physical_tail = F(Q), F(J), F(physical_tail)
    if Q <= 0 or J < 0 or physical_tail < 0:
        raise ValueError('invalid capability bound')
    releases, windows, now = [], [], F(0)
    for lo, hi in bounds:
        lo, hi = F(lo), F(hi)
        if lo < 0 or hi <= 0 or lo > hi:
            raise ValueError('invalid duration bound')
        releases.append(now)
        windows.append((now + lo, now + hi + J))
        drained = now + hi + max(J, physical_tail)
        now = -((-drained) // Q) * Q
    return {'releases': releases, 'windows': windows, 'drain_cost': now}


if __name__ == '__main__':
    # Near-homogeneous truth is NOT input. Learned intervals alone are input.
    narrow = [(F(99), F(100))] * 4
    candidate = global_stagger(narrow, 1, 1)
    assert not candidate['unique_timestamp_binding']  # unknown routing matters
    spaced = global_stagger(narrow, 1, 1, spacing=102)
    assert spaced['unique_timestamp_binding']       # baseline can also succeed
    assert serial_and_drain(narrow, 1)['drain_cost'] == 404
    assert len(list(partitions(4))) == 15
    import random
    rng = random.Random(731)
    for n in range(1, 7):
        for _ in range(20):
            b = [(F(rng.randrange(1, 10)), F(10 + rng.randrange(10))) for _ in range(n)]
            r = list(map(F, rng.sample(range(50), n)))
            assert robust_windows(b, F(3), r) == robust_windows_hull(b, F(3), r)
    print('reference_baseline self-tests: PASS (120 exhaustive-hull equivalence fixtures)')

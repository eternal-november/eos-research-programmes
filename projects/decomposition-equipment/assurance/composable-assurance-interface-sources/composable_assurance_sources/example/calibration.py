"""Observable width-two residual calibration; no latent-noise/world access.

Frozen assumptions: rows are prospectively fixed, synchronized DISJOINT width-two
windows, independent across rows. Columns are channels with unknown partition;
within a block their source errors are identical; blocks are independent. Each
primitive sign is negative with one COMMON unknown p in [0.01, 0.03]. Category
values {-1,0,+1} are averaged residual / e, not primitive noise observations.
Physical reference error <=1/128 and e=1/32 allow exact category decoding.
N is fixed before observations; repeated epochs need fresh confidence allocation.
No statistical claim is made under drift, adaptive stopping, overlapping rows,
misaligned windows, a wrong decoder error envelope, or unmodeled noise.
"""
from __future__ import annotations
import hashlib
import math
import numpy as np

E = 1 / 32
REFERENCE_ERROR = 1 / 128
P_CLASS = (0.01, 0.03)
FROZEN_N = 1_000_000


def decode_categories(residuals, *, amplitude=E, error_bound=REFERENCE_ERROR):
    """Decode measured report minus averaged physical reference.

    Caller proves actual averaging/capture interpretation and reference bound.
    Raises on ambiguous/off-class observations rather than rounding regardless.
    """
    if not (0 <= error_bound < amplitude / 2):
        raise ValueError('Need strict category spacing > twice total error')
    a = np.asarray(residuals)
    if not np.all(np.isfinite(a)):
        raise ValueError('Residuals must be finite')
    decoded = np.rint(a / amplitude)
    if np.any(np.abs(decoded) > 1) or np.any(np.abs(a - decoded * amplitude) > error_bound + 1e-14):
        raise ValueError('Residual outside the stated three-category error envelope')
    return decoded.astype(np.int8)


def mismatch_probability(p):
    """Two independent width-two category draws differ, common primitive rate p."""
    return 1 - ((1-p)**4 + (2*p*(1-p))**2 + p**4)


def sufficient_samples(n_channels, delta_rate=.002, delta_block=.002,
                       target_upper=.025, reference_true_p=.02):
    """Prospective bounds, not access to a hidden realized rate.

    `reference_true_p` is a planning assumption only. Rate count ensures that,
    on the simultaneous Hoeffding event, every channel upper bound is at most
    target_upper when the true rate <= reference_true_p. It uses TWO radii.
    """
    if n_channels < 1 or not 0 < delta_rate < 1 or not 0 < delta_block < 1:
        raise ValueError('Invalid channel count or confidence allocation')
    pairs = n_channels * (n_channels - 1) // 2
    qmin = mismatch_probability(P_CLASS[0])
    block = 0 if pairs == 0 else math.ceil(math.log(pairs / delta_block) / -math.log1p(-qmin))
    margin = target_upper - reference_true_p
    rate = None if margin <= 0 else math.ceil(2 * math.log(2*n_channels/delta_rate) / margin**2)
    return {'block_min_N': block, 'rate_sufficient_N': rate,
            'q_min': qmin, 'rate_planning_true_upper': reference_true_p,
            'rate_target_upper': target_upper}


def calibrate(observed_categories, delta_rate=.002, delta_block=.002):
    """Return inferred groups, simultaneous COMMON-p interval and diagnostics.

    At most delta_block probability of a false merge over all pairs, when the
    deterministic sample sufficiency threshold holds. Shared columns cannot
    split under the model. If insufficient, groups is None; equality_classes
    remain descriptive evidence, not an identified partition.

    Rate confidence uses one [0,1] variable per channel/window: (1-category)/2.
    Across-channel dependence is allowed; union bound across channels then
    intersect their simultaneous intervals because p is common. Prior clipping
    uses supplied class bounds only. Empty intersection is model/inference
    inconsistency, NOT a fabricated point estimate.
    """
    a = np.asarray(observed_categories)
    if a.ndim != 2 or min(a.shape) <= 0:
        raise ValueError('Expected nonempty N-by-channel category matrix')
    if not 0 < delta_rate < 1 or not 0 < delta_block < 1:
        raise ValueError('Confidence allocations must lie in (0,1)')
    if not np.all((a == -1) | (a == 0) | (a == 1)):
        raise ValueError('Categories must be encoded -1, 0, +1')
    N, n = a.shape
    # Hash for search only; full equality verification prevents hash assumptions.
    buckets = {}
    groups = []
    for j in range(n):
        col = np.ascontiguousarray(a[:, j], dtype=np.int8)
        key = hashlib.sha256(col.tobytes()).digest()
        match = None
        for gi in buckets.get(key, []):
            if np.array_equal(a[:, groups[gi][0]], col):
                match = gi
                break
        if match is None:
            groups.append([j])
            buckets.setdefault(key, []).append(len(groups)-1)
        else:
            groups[match].append(j)
    estimates = (1 - a.mean(axis=0, dtype=np.float64)) / 2
    radius = math.sqrt(math.log(2*n/delta_rate) / (2*N))
    low = max(P_CLASS[0], float(np.max(estimates-radius)))
    high = min(P_CLASS[1], float(np.min(estimates+radius)))
    consistent = low <= high
    needed = sufficient_samples(n, delta_rate, delta_block)
    partition_certified = N >= needed['block_min_N']
    pairs = n*(n-1)//2
    log_bound = -math.inf if pairs == 0 else math.log(pairs)+N*math.log1p(-needed['q_min'])
    # Preserve log bound even when floating-point exponential underflows.
    probability_bound = min(1., math.exp(log_bound)) if log_bound > -745 else 0.
    return {
        'groups': groups if partition_certified else None,
        'equality_classes': groups,
        'p_interval': [low, high] if consistent else None,
        'status': ('model_or_confidence_inconsistent' if not consistent else
                   'certified' if partition_certified else 'partition_unresolved'),
        'diagnostics': {'N': N, 'n_channels': n, 'fixed_N_required': True,
            'frozen_N': FROZEN_N, 'matches_frozen_N': N == FROZEN_N,
            'delta_rate': delta_rate, 'delta_block': delta_block,
            'total_training_exclusion_bound': delta_rate+delta_block,
            'p_class': list(P_CLASS), 'common_p_assumption': True,
            'per_channel_p_estimate': estimates.tolist(), 'hoeffding_radius': radius,
            'partition_certified': partition_certified,
            'false_merge_log_union_bound': log_bound,
            'false_merge_union_bound_float': probability_bound,
            'false_merge_float_underflow': log_bound <= -745,
            **needed}}


def unit_test():
    # Deterministic software fixtures only, not a calibration experiment.
    physical = np.array([-E, 0., E])
    assert np.array_equal(decode_categories(physical + REFERENCE_ERROR), [-1, 0, 1])
    for bad in [np.array([E*2]), np.array([E/2])]:
        try:
            decode_categories(bad)
            raise AssertionError('Invalid category accepted')
        except ValueError:
            pass
    # Separate distributions with identical empirical p; matching columns group.
    N = 2000
    first = np.ones(N, dtype=np.int8)
    first[:80] = 0  # p estimate .02 from observable zero-category rate .04.
    second = np.roll(first, 100)
    data = np.stack([first, first, second], axis=1)
    result = calibrate(data)
    assert result['groups'] == [[0, 1], [2]]
    assert result['p_interval'][0] <= .02 <= result['p_interval'][1]
    tiny = calibrate(np.ones((1, 2), dtype=np.int8))
    assert tiny['groups'] is None and tiny['status'] == 'partition_unresolved'
    assert sufficient_samples(30)['rate_sufficient_N'] <= FROZEN_N
    return {'software_tests': 'pass', 'tests_are_not_statistical_outcomes': True}


if __name__ == '__main__':
    print(unit_test())

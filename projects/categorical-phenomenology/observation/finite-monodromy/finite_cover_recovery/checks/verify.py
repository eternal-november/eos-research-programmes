#!/usr/bin/env python3
"""Finite algebraic checks and seeded simulation, not a proof of a theorem.
Requires Python >=3.10 and NumPy >=1.24. Counts are exact IID sufficient-
statistic draws; long trajectories need not be explicitly materialized.
"""
import hashlib
import json
import math
from pathlib import Path
import sys
import numpy as np

SEED = 202611040032


def compose(a, b):
    """a after b, for index arrays representing permutations."""
    return np.asarray(a)[np.asarray(b)]


def inverse(a):
    return np.argsort(a)


def product_permutation(edges):
    out = np.arange(len(edges[0]))
    for edge in edges:
        out = compose(edge, out)
    return out


def cycle_type(a):
    seen = set()
    lengths = []
    for start in range(len(a)):
        if start in seen:
            continue
        current, count = start, 0
        while current not in seen:
            seen.add(current)
            count += 1
            current = int(a[current])
        lengths.append(count)
    return sorted(lengths)


def distance(a, b):
    return np.max(np.abs(a[:, None, ...] - b[None, ...]), axis=tuple(range(2, a.ndim + 1)))


def match(a, b, delta):
    relation = distance(a, b) < delta / 2
    if not (np.all(relation.sum(axis=0) == 1) and np.all(relation.sum(axis=1) == 1)):
        return None
    return np.argmax(relation, axis=1)


def cluster(samples, delta):
    adjacent = distance(samples, samples) < delta / 2
    remaining = set(range(len(samples)))
    groups = []
    while remaining:
        component = {min(remaining)}
        frontier = set(component)
        while frontier:
            neighbors = set(np.flatnonzero(np.any(adjacent[list(frontier)], axis=0)))
            frontier = neighbors - component
            component |= frontier
        remaining -= component
        groups.append(sorted(component))
    return np.array([np.mean(samples[g], axis=0) for g in groups]), groups


def polygon(theta, p, amplitude=0.125):
    angle = theta / p + 2 * np.pi * np.arange(p) / p
    v = np.full((p, 4), 0.25)
    v[:, 0] += amplitude * np.cos(angle)
    v[:, 1] -= amplitude * np.cos(angle)
    v[:, 2] += amplitude * np.sin(angle)
    v[:, 3] -= amplitude * np.sin(angle)
    return v


def design(p, alpha=0.05, eta_fraction=0.0, periodic=False, upper_p=None):
    amplitude = 0.125
    delta = math.sqrt(2) * amplitude * math.sin(math.pi / p)
    speed = amplitude / p
    vertices = max(3, math.ceil(8 * speed * 2 * math.pi / delta))
    w0 = 1 / p if upper_p is None else 1 / upper_p
    count_p = p if upper_p is None else upper_p
    restarts = math.ceil(math.log(2 * vertices * count_p / alpha) / w0)
    eta = delta * eta_fraction
    if not 0 <= eta < delta / 8:
        raise ValueError("Corruption allowance must be below delta/8.")
    coordinates = 4 * (p if periodic else 1)
    length = math.ceil(math.log(4 * vertices * restarts * coordinates / alpha)
                       / (2 * (delta / 8 - eta) ** 2))
    coverage = vertices * count_p * math.exp(-restarts * w0)
    noise = 2 * vertices * restarts * coordinates * math.exp(-2 * length * (delta / 8 - eta) ** 2)
    assert coverage <= alpha / 2 and noise <= alpha / 2
    assert speed * 2 * math.pi / vertices <= delta / 8
    return dict(p=p, alpha=alpha, delta=delta, speed=speed, vertices=vertices,
                restarts=restarts, length=length, w0=w0, eta=eta,
                coverage_failure_bound=coverage, frequency_failure_bound=noise,
                union_failure_bound=coverage + noise)


def verify_labels(estimates, truths, edges):
    labels = [np.argmin(distance(e, t), axis=1) for e, t in zip(estimates, truths)]
    p = len(labels[0])
    assert all(len(set(a)) == p for a in labels)
    for i, edge in enumerate(edges):
        next_label = labels[(i + 1) % len(labels)][edge]
        expected = labels[i] if i + 1 < len(labels) else (labels[i] + 1) % p
        assert np.array_equal(next_label, expected)
    recovered = product_permutation(edges)
    true_in_estimated_labels = compose(inverse(labels[0]), (labels[0] + 1) % p)
    assert np.array_equal(recovered, true_in_estimated_labels)
    return labels, recovered


def held_trial(config, rng, keep=False):
    p, vertices, count, n = (config[x] for x in ("p", "vertices", "restarts", "length"))
    delta, eta = config["delta"], config["eta"]
    truths, estimates = [], []
    good, exact_clusters = True, True
    coverage_good, frequency_good = True, True
    max_error = 0.0
    max_corruption = 0.0
    for i in range(vertices):
        truth = polygon(2 * math.pi * i / vertices, p)
        labels = rng.integers(p, size=count)
        empirical = np.array([rng.multinomial(n, truth[a]) / n for a in labels])
        deviation = np.max(np.abs(empirical - truth[labels]))
        coverage_good &= len(set(labels)) == p
        frequency_good &= deviation <= delta / 8 - eta
        good &= deviation <= delta / 8 - eta and len(set(labels)) == p
        max_error = max(max_error, float(deviation))
        reported = empirical.copy()
        if eta:
            # Bounded, adversarial label/vertex-dependent corruption.
            shift = eta * np.where((labels + i) % 2, 1, -1)
            reported[:, 0] += shift
            reported[:, 1] -= shift
            assert np.min(reported) >= 0 and np.max(np.abs(reported.sum(axis=1) - 1)) < 1e-12
            max_corruption = max(max_corruption, float(np.max(np.abs(reported - empirical))))
        estimate, groups = cluster(reported, delta)
        exact_clusters &= len(groups) == p and all(len(set(labels[g])) == 1 for g in groups)
        truths.append(truth)
        estimates.append(estimate)
    if any(len(e) != p for e in estimates):
        assert not good
        return dict(success=False, good_event=bool(good), cluster_failure=True,
                    coverage_good=bool(coverage_good), frequency_good=bool(frequency_good))
    edges = [match(estimates[i], estimates[(i + 1) % vertices], delta) for i in range(vertices)]
    if any(e is None for e in edges):
        assert not good
        return dict(success=False, good_event=bool(good), edge_failure=True,
                    coverage_good=bool(coverage_good), frequency_good=bool(frequency_good))
    permutation = product_permutation(edges)
    success = cycle_type(permutation) == [p]
    if good:
        assert exact_clusters and success
        assert all(np.max(np.min(distance(e, t), axis=1)) <= delta / 8 + 1e-12
                   for e, t in zip(estimates, truths))
        verify_labels(estimates, truths, edges)
    result = dict(success=bool(success), good_event=bool(good), max_uncorrupted_error=max_error,
                  coverage_good=bool(coverage_good), frequency_good=bool(frequency_good),
                  max_corruption=max_corruption, recovered_permutation=permutation.tolist(),
                  recovered_cycle_type=cycle_type(permutation))
    if keep:
        result["data"] = (estimates, truths, edges)
    return result


def relabeling_check(data, rng):
    estimates, truths, edges = data
    original = product_permutation(edges)
    p = len(original)
    relabel = [rng.permutation(p) for _ in estimates]
    relabel[0] = np.array([1, 0, 2])  # Changes the raw three-cycle representative.
    changed = [e[r] for e, r in zip(estimates, relabel)]
    # Delta may be recovered conservatively from this known fixture.
    delta = design(p)["delta"]
    new_edges = [match(changed[i], changed[(i + 1) % len(changed)], delta) for i in range(len(changed))]
    assert all(e is not None for e in new_edges)
    for i, edge in enumerate(new_edges):
        expected = compose(inverse(relabel[(i + 1) % len(changed)]), compose(edges[i], relabel[i]))
        assert np.array_equal(edge, expected)
    new = product_permutation(new_edges)
    assert np.array_equal(new, compose(inverse(relabel[0]), compose(original, relabel[0])))
    assert not np.array_equal(new, original)
    assert cycle_type(new) == cycle_type(original) == [3]
    assert cycle_type(np.arange(3)) != cycle_type(original)
    return dict(original=original.tolist(), relabeled=new.tolist(), cycle_type=[3],
                both_three_cycle_and_identity_have_positive_sign=True,
                raw_labels_are_not_invariant=True)


def periodic_trial(rng):
    cfg = design(3, periodic=True)
    p, m, d = 3, 3, 4
    vertices, count, t = (cfg[x] for x in ("vertices", "restarts", "length"))
    delta = cfg["delta"]
    truths, estimates, latent_zero_vertices = [], [], []
    offset_histogram = np.zeros(m, dtype=int)
    retained_histogram = np.zeros(p, dtype=int)
    total_symbols = 0
    good = True
    for i in range(vertices):
        theta = 2 * math.pi * i / vertices
        v = polygon(theta, p)
        profiles = np.array([np.array([v[(a + r) % p] for r in range(m)]) for a in range(p)])
        angle = theta / p + 2 * np.pi * np.arange(p) / p
        weights = (1 + np.cos(angle)) / p
        weights /= weights.sum()
        if np.min(weights) < 1e-14:
            latent_zero_vertices.append(i)
        initial = rng.choice(p, size=count, p=weights)
        offsets = rng.integers(m, size=count)
        effective = (initial + offsets) % p
        offset_histogram += np.bincount(offsets, minlength=m)
        retained_histogram += np.bincount(effective, minlength=p)
        # Original prefixes are drawn and discarded; the retained profile
        # counts are exact sufficient statistics for the required experiment.
        observed = []
        for a, u in zip(initial, offsets):
            for r in range(int(u)):
                rng.choice(d, p=v[(a + r) % p])
            observed.append(np.array([rng.multinomial(t, v[(a + u + r) % p]) / t for r in range(m)]))
            total_symbols += int(u) + m * t
        observed = np.array(observed)
        good &= len(set(effective)) == p and np.max(np.abs(observed - profiles[effective])) <= delta / 8
        estimate, groups = cluster(observed, delta)
        if good:
            assert len(groups) == p and all(len(set(effective[g])) == 1 for g in groups)
        estimates.append(estimate)
        truths.append(profiles)
    assert good and latent_zero_vertices
    edges = [match(estimates[i], estimates[(i + 1) % vertices], delta) for i in range(vertices)]
    assert all(e is not None for e in edges)
    _, monodromy = verify_labels(estimates, truths, edges)
    advances = [match(np.roll(e, -1, axis=1), e, delta) for e in estimates]
    assert all(a is not None for a in advances)
    for i, advance in enumerate(advances):
        assert np.array_equal(product_permutation([advance] * m), np.arange(p))
        assert np.array_equal(compose(edges[i], advance), compose(advances[(i + 1) % vertices], edges[i]))
    assert np.array_equal(compose(monodromy, advances[0]), compose(advances[0], monodromy))
    assert total_symbols <= vertices * count * (m * t + m - 1)

    # Initial weights above descend on the nontrivial cover: endpoint weights
    # and emissions obey the same cyclic gluing, unlike a fixed phase label.
    wstart = (1 + np.cos(2 * np.pi * np.arange(p) / p)) / p
    wend = (1 + np.cos(2 * np.pi / p + 2 * np.pi * np.arange(p) / p)) / p
    assert np.allclose(wend, np.roll(wstart, -1))
    assert np.allclose(sum(np.roll(wstart, r) for r in range(m)) / m, np.ones(p) / p)
    assert np.allclose(sum(np.roll(wend, r) for r in range(m)) / m, np.ones(p) / p)
    # Without offsets, a zero-weight phase at theta=pi cannot be observed.
    midpoint = vertices // 2
    mid_weights = (1 + np.cos(math.pi / p + 2 * np.pi * np.arange(p) / p)) / p
    assert mid_weights[1] == 0
    without_offset = rng.choice(p, size=count, p=mid_weights / mid_weights.sum())
    assert 1 not in without_offset
    # Marginally uniform offsets are insufficient if correlated with S.
    initial_balanced = np.tile(np.arange(p), 100)
    correlated_offsets = (-initial_balanced) % p
    assert np.array_equal(np.bincount(correlated_offsets), [100] * p)
    assert set((initial_balanced + correlated_offsets) % p) == {0}
    return dict(config=cfg, good_event=True, monodromy=monodromy.tolist(),
                phase_advance=advances[0].tolist(), phase_advance_order=3,
                transports_commute_with_advance=True,
                vertices_with_zero_initial_phase_weight=latent_zero_vertices,
                observed_original_symbols=total_symbols,
                worst_case_original_symbol_budget=vertices * count * (m * t + m - 1),
                offset_histogram=offset_histogram.tolist(), retained_phase_histogram=retained_histogram.tolist(),
                no_offset_control="A zero-mass phase is absent at the midpoint vertex.",
                correlated_offset_control="Uniform marginal offsets correlated as U=-S retain only phase zero.")


def boundary_controls():
    delta = 0.5
    true = np.array([[0.25, 0.75], [0.75, 0.25]])
    left = true - np.array([0.125, -0.125])
    right = true + np.array([0.125, -0.125])
    # Lh=0, r=delta/4: the strict deterministic hypothesis is at equality.
    assert np.max(np.abs(left - true)) == delta / 4
    assert match(left, right, delta) is None
    same_atom = np.array([left[0], right[0]])
    assert len(cluster(same_atom, delta)[1]) == 2
    # A half-twist can be hidden entirely in an unobserved closing arc.
    p, vertices = 2, 18
    exact = [polygon(0, p) for _ in range(vertices)]
    delta = design(p)["delta"]
    edges = [match(exact[i], exact[(i + 1) % vertices], delta) for i in range(vertices)]
    recovered = product_permutation(edges)
    assert np.array_equal(recovered, [0, 1])  # Hidden true monodromy is (01).
    gap = 2 * math.pi / vertices
    speed = 0.125 * math.pi / gap
    assert speed * gap > delta / 8
    try:
        design(2, eta_fraction=1 / 8)
    except ValueError:
        pass
    else:
        raise AssertionError("The corruption boundary must not be accepted.")
    # Without the upper support-size promise, transportation closeness cannot
    # imply exact support count: split one atom into nearby positive subatoms.
    epsilon = 2 ** -16
    mu = np.array([[0.25, 0.75], [0.75, 0.25]])
    nu = np.array([[0.25 - epsilon, 0.75 + epsilon],
                   [0.25 + epsilon, 0.75 - epsilon], [0.75, 0.25]])
    # Coupling sends the first atom equally to the first two estimates.
    transport_cost = (distance(mu, nu)[0, 0] + distance(mu, nu)[0, 1]) / 4
    assert len(nu) == len(mu) + 1
    assert transport_cost == epsilon / 2
    assert transport_cost < 0.5 * 0.1
    # At W1=w0*r, an estimate exactly at distance r is not in the open ball.
    radius = 0.125
    nu_boundary = mu.copy()
    nu_boundary[0] += [radius, -radius]
    exact_boundary_cost = 0.5 * distance(mu, nu_boundary)[0, 0]
    assert exact_boundary_cost == 0.5 * radius
    assert np.min(distance(mu, nu_boundary)[0]) == radius
    return dict(strict_matching_equality="True-match distance equals threshold; no bijection.",
                excessive_clustering_error="One latent atom splits into two clusters at r=delta/4.",
                hidden_gap_twist="All queried unordered fibers agree with the trivial cover; true closing arc swaps sheets.",
                hidden_twist_violates_required_mesh_bound=True,
                eta_equal_delta_over_8_rejected=True,
                strict_transportation_boundary="At W1=w0*r, a paired estimate may lie exactly at distance r rather than below r.",
                transportation_support_control="An arbitrarily close three-atom measure need not match a two-atom measure without the at-most-p promise.")


def lower_bound_checks():
    delta, w = math.sqrt(2) / 8, 1 / 10
    amplitude = delta / math.sqrt(2)
    largest_kl, largest_ratio = 0.0, 0.0
    baseline = polygon(0, 2, amplitude)
    for theta in np.linspace(0, 2 * math.pi, 1001):
        changed = polygon(theta, 2, amplitude)
        assert changed.min() >= 1 / 8 - 1e-14
        each_kl = np.sum(baseline * np.log(baseline / changed), axis=1)
        assert each_kl.max() <= 32 * delta ** 2 + 1e-12
        weighted = w * float(each_kl.sum())
        assert weighted <= 64 * w * delta ** 2 + 1e-12
        largest_kl = max(largest_kl, weighted)
        largest_ratio = max(largest_ratio, weighted / (64 * w * delta ** 2))
    restarts, symbols = 10, 100
    return dict(rare_weight=w, separation=delta,
                largest_augmented_one_symbol_KL_on_grid=largest_kl,
                largest_ratio_to_claimed_KL_bound=largest_ratio,
                restart_error_lower_bound_at_S10=0.5 * (1 - 2 * w) ** restarts,
                symbol_error_lower_bound_at_B100=0.25 * math.exp(-64 * w * delta ** 2 * symbols),
                note="Grid checks sanity-check constants, not the adaptive-experiment chain rule or a lower-bound proof.")


def main():
    rng = np.random.default_rng(SEED)
    source = Path(__file__).resolve().parents[1] / "finite_cover_recovery.tex"
    runs = {}
    saved_data = None
    for p in (2, 3):
        cfg = design(p)
        results = []
        for j in range(300):
            trial = held_trial(cfg, rng, keep=(p == 3 and saved_data is None))
            if "data" in trial:
                saved_data = trial.pop("data")
            results.append(trial)
        runs[str(p)] = dict(config=cfg, trials=len(results),
                           successes=sum(r["success"] for r in results),
                           good_events=sum(r["good_event"] for r in results),
                           coverage_failure_trials=sum(not r["coverage_good"] for r in results),
                           frequency_failure_trials=sum(not r["frequency_good"] for r in results),
                           largest_uncorrupted_error=max(r.get("max_uncorrupted_error", 0) for r in results),
                           expected_cycle_type=[p],
                           symbol_budget_per_trial=cfg["vertices"] * cfg["restarts"] * cfg["length"])
    unknown = design(3, upper_p=4)
    unknown_result = held_trial(unknown, rng, keep=True)
    unknown_estimates, _, _ = unknown_result.pop("data")
    inferred_p = len(unknown_estimates[0])
    assert all(len(e) == inferred_p for e in unknown_estimates)
    assert inferred_p == 3
    assert unknown_result["success"] and unknown_result["good_event"]
    corruption = design(3, eta_fraction=1 / 16)
    corrupted = held_trial(corruption, rng)
    assert corrupted["success"] and corrupted["good_event"]
    result = dict(all_checks_passed=True, seed=SEED, python=sys.version.split()[0],
                  numpy=np.__version__, source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                  held_mixture_simulations=runs,
                  unknown_p=dict(config=unknown, recovered_p=inferred_p, result=unknown_result),
                  bounded_corruption=dict(config=corruption, result=corrupted),
                  relabeling_and_conjugacy=relabeling_check(saved_data, rng),
                  periodic_randomized_offsets=periodic_trial(rng),
                  boundary_negative_controls=boundary_controls(),
                  lower_bound_constant_checks=lower_bound_checks(),
                  scope="Seeded finite simulations and deterministic checks. They are not proofs or finite-data certification of model promises. No counterexample satisfying all theorem assumptions was found.")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()

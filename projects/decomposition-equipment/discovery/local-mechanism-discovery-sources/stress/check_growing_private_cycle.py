"""Four-bundle member of the growing private-factor cycle family.

Only bounded observable tensors are passed to reconstruction. The oracle's
256-state model generates exact laws and is not a learner input. Each bundle
contains a private factor not isolated by ANY static overlap.
"""
import itertools
import json
from pathlib import Path
import numpy as np
from check_hidden_patch_discovery import recover_three_view, support_components


def run(n=4, fair_private=None, seed=6142):
    rng = np.random.default_rng(seed)
    m = 10
    # Oracle's state order is a0,b0,a1,b1,...; all labels/incidence hidden.
    states = np.array(list(itertools.product(range(2), repeat=2*n)))
    ns = len(states)
    probs = np.empty((ns, 2*n))
    for i in range(n):
        a, b, c = states[:, 2*i], states[:, 2*i+1], states[:, 2*((i+1)%n)+1]
        probs[:, 2*i] = .12+.04*a+.06*b+.08*c+.03*a*b+.02*a*c+.01*b*c
        prev_a = states[:, 2*((i-1)%n)]
        probs[:, 2*i+1] = .20+.15*b+.20*prev_a+.10*b*prev_a
    if fair_private is not None:
        probs[:, 2*fair_private] = .5
    transition = np.ones((ns, ns))
    for j in range(2*n):
        transition *= np.where(states[None, :, j], probs[:, j, None], 1-probs[:, j, None])
    pi = np.full(ns, 1/ns)
    for _ in range(10000):
        nxt = pi @ transition
        if max(abs(nxt-pi)) < 2e-16:
            pi = nxt
            break
        pi = nxt
    patches = list(range(n))
    rng.shuffle(patches)
    z, es, estimates = [], [], []
    for i in patches:
        perm = rng.permutation(8)
        z.append(perm[4*states[:, 2*i]+2*states[:, 2*i+1]+states[:, 2*((i+1)%n)+1]])
        views = []
        for _ in range(3):
            e = rng.gamma(1.2, 1., size=(m, 8))+.15
            e /= e.sum(axis=0)
            views.append(e)
        es.append(views)
        weights = np.bincount(z[-1], weights=pi, minlength=8)
        raw = np.einsum('z,az,bz,cz->abc', weights, *views)
        recovered, _, error = recover_three_view(raw, rng)
        assert error < 1e-9
        estimates.append(recovered)
    overlaps = []
    for p in range(n):
        for q in range(p+1, n):
            actual = np.zeros((8, 8))
            np.add.at(actual, (z[p], z[q]), pi)
            raw = es[p][0] @ actual @ es[q][0].T
            recovered = np.linalg.pinv(estimates[p][0]) @ raw @ np.linalg.pinv(estimates[q][0]).T
            count, lp, lq = support_components(recovered)
            if count > 1:
                assert count == 2
                overlaps.append((p, q, {p: lp, q: lq}))
    assert len(overlaps) == n
    temporal_count = 0
    max_raw_entries = m**3

    def observed_temporal(target, sources):
        nonlocal temporal_count, max_raw_entries
        f = np.ones((ns, 1))
        for p in sources:
            sensor = es[p][0][:, z[p]].T
            f = (f[:, :, None]*sensor[:, None, :]).reshape(ns, -1)
        future = es[target][0][:, z[target]].T
        raw = ((f.T*pi) @ transition @ future).reshape((m,)*(len(sources)+1))
        temporal_count += 1
        max_raw_entries = max(max_raw_entries, raw.size)
        return raw

    reports = []
    for p in range(n):
        # Context discovery is over observed bundle names, not latent factors.
        choices = []
        for size in range(3):
            for sources in itertools.combinations(range(n), size):
                raw = observed_temporal(p, sources)
                letters, output = 'abc', 'ijk'
                terms = [letters[:size+1]]
                arrays = [raw]
                for j, patch in enumerate(sources+(p,)):
                    terms.append(output[j]+letters[j])
                    arrays.append(np.linalg.pinv(estimates[patch][0]))
                table = np.einsum(','.join(terms)+'->'+output[:size+1], *arrays)
                assert table.min() > -1e-8
                table = np.maximum(table, 0)
                table /= table.sum()
                flat = table.reshape(-1, 8)
                masses = flat.sum(axis=1)
                supported = masses > 1e-7
                rows = flat[supported]/masses[supported, None]
                entropy = float(-np.sum(flat[supported]*np.log(np.maximum(rows, 1e-300))))
                choices.append((entropy, sources, rows))
        hmin = min(c[0] for c in choices)
        best = min([c for c in choices if c[0]<hmin+1e-8], key=lambda c: len(c[1]))
        incident = [item[2][p] for item in overlaps if p in item[2]]
        assert len(incident) == 2
        shared_index = 2*incident[0]+incident[1]
        fibers = [np.flatnonzero(shared_index == c) for c in range(4)]
        assert all(len(x) == 2 for x in fibers)
        candidates = []
        for flips in itertools.product(range(2), repeat=4):
            amap = np.zeros(8, dtype=int)
            for c, flip in enumerate(flips):
                amap[fibers[c]] = np.array([0, 1]) ^ flip
            arrays = np.zeros((len(best[2]), 2, 2, 2))
            for zz in range(8):
                arrays[:, amap[zz], incident[0][zz], incident[1][zz]] = best[2][:, zz]
            ma = arrays.sum(axis=(2,3))
            mb = arrays.sum(axis=(1,3))
            mc = arrays.sum(axis=(1,2))
            product = ma[:, :, None, None]*mb[:, None, :, None]*mc[:, None, None, :]
            error = float(np.max(abs(arrays-product)))
            candidates.append(error)
        accepted = sum(e < 1e-8 for e in candidates)
        expected = 16 if patches[p] == fair_private else 2
        assert accepted == expected
        reports.append({
            'observed_bundle': p,
            'learned_patch_rank': estimates[p][0].shape[1],
            'learned_shared_cardinalities': [2,2],
            'learned_private_cardinality': len(fibers[0]),
            'selected_past_bundles': list(best[1]),
            'tested_private_charts': len(candidates),
            'accepted_private_charts': accepted,
            'largest_accepted_product_error': max(e for e in candidates if e < 1e-8),
            'smallest_rejected_product_error': min((e for e in candidates if e >= 1e-8), default=None)
        })
    return {
        'bundles': n,
        'actual_hidden_output_factors': 2*n,
        'oracle_only_whole_states': ns,
        'fair_private_factor_oracle_only': fair_private,
        'observable_tensor_max_entries': max_raw_entries,
        'temporal_tensors_queried': temporal_count,
        'reports': reports,
        'status': 'PASS',
        'scope': 'Immediate-coupling exact-law fixture. Counts are locally product-compatible charts, not globally budget-certified architectures. Its raw tensors have 1000 entries; the delayed analytic family may need 10000.'
    }


if __name__ == '__main__':
    result = {'generic': run(), 'fair_ambiguity': run(fair_private=1)}
    Path(__file__).with_name('Growing_Private_Cycle_QA.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))

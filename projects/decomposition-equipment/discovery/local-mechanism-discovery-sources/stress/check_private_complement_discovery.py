"""Dynamics distinguishes unknown private complements invisible to overlap.

Patch cover {a,b},{b,c}; all patch and component labels are hidden, and every
sensor alphabet has ten symbols and strictly positive noise. The learner uses
three-view patch tensors, an overlap matrix, and bounded temporal tensors.
"""
import itertools
import json
from pathlib import Path
import numpy as np
from check_hidden_patch_discovery import recover_three_view, support_components, kernel


def run(fair_private=False, seed=5521):
    rng = np.random.default_rng(seed)
    states = np.array(list(itertools.product(range(2), repeat=3)))
    m, ns = 10, 8
    patches = [(0, 1), (1, 2)]
    local = [kernel([2, 2, 2], i) for i in range(3)]
    if fair_private:
        local[0][:] = .5
    k = np.ones((ns, ns))
    for i in range(3):
        k *= local[i][states[:, i, None], states[:, (i-1) % 3, None], states[None, :, i]]
    pi = np.full(ns, 1/ns)
    for _ in range(10000):
        nxt = pi @ k
        if max(abs(nxt-pi)) < 1e-16:
            pi = nxt
            break
        pi = nxt
    z, emissions, learned, errors = [], [], [], []
    for i, j in patches:
        perm = rng.permutation(4)
        z.append(perm[2*states[:, i]+states[:, j]])
        es = []
        for _ in range(3):
            e = rng.gamma(1.2, 1., size=(m, 4)) + .15
            e /= e.sum(axis=0)
            es.append(e)
        emissions.append(es)
        w = np.bincount(z[-1], weights=pi, minlength=4)
        tensor = np.einsum('z,az,bz,cz->abc', w, *es)
        eh, _, error = recover_three_view(tensor, rng)
        learned.append(eh)
        errors.append(error)
    latent_pair = np.zeros((4, 4))
    np.add.at(latent_pair, (z[0], z[1]), pi)
    observed_pair = emissions[0][0] @ latent_pair @ emissions[1][0].T
    pair = np.linalg.pinv(learned[0][0]) @ observed_pair @ np.linalg.pinv(learned[1][0]).T
    count, b0, b1 = support_components(pair)
    assert count == 2
    assert all(sum(b == a) == 2 for b in [b0, b1] for a in range(2))
    bmaps = [b0, b1]
    old_valid = pair > 1e-7
    assert old_valid.sum() == 8

    results = []
    for p in range(2):
        # All conditional-next patch rows are learned from raw sensor laws.
        f0 = emissions[0][0][:, z[0]].T
        f1 = emissions[1][0][:, z[1]].T
        future = emissions[p][0][:, z[p]].T
        raw = np.einsum('xy,xa,xb,yc->abc', pi[:, None]*k, f0, f1, future, optimize=True)
        latent = np.einsum('abc,ia,jb,kc->ijk', raw,
                           np.linalg.pinv(learned[0][0]),
                           np.linalg.pinv(learned[1][0]),
                           np.linalg.pinv(learned[p][0]))
        rows = latent[old_valid]
        rows /= rows.sum(axis=1, keepdims=True)
        # Every complement compatible with the shared b projection. No
        # private coordinate alphabet or complement labels were supplied.
        fibers = [np.flatnonzero(bmaps[p] == b) for b in range(2)]
        candidates = []
        for flip0, flip1 in itertools.product(range(2), repeat=2):
            private = np.zeros(4, dtype=int)
            for b, flip in enumerate([flip0, flip1]):
                private[fibers[b]] = np.array([0, 1]) ^ flip
            tables = np.zeros((len(rows), 2, 2))
            for zstate in range(4):
                tables[:, private[zstate], bmaps[p][zstate]] = rows[:, zstate]
            products = tables.sum(axis=2)[:, :, None] * tables.sum(axis=1)[:, None, :]
            error = float(np.max(abs(tables-products)))
            candidates.append({'private_map': private.tolist(), 'product_error': error,
                               'accepted': error < 1e-8})
        results.append(candidates)
    accepted = [sum(c['accepted'] for c in cs) for cs in results]
    expected = [4 if fair_private else 2, 2]
    assert accepted == expected

    # Statewise XOR change of coordinates, globally invertible. It always
    # preserves every observation law when sensor kernels are transported.
    # It preserves independent next-factor noise iff private a is fair here.
    transformed = np.array([[a ^ b, b, c] for a, b, c in states])
    indices = [int(4*a+2*b+c) for a, b, c in transformed]
    permutation = np.eye(8)[:, indices]
    assert np.max(abs(permutation.T @ permutation-np.eye(8))) == 0
    transformed_k = permutation.T @ k @ permutation
    transformed_pi = pi @ permutation
    e_all = np.einsum('xa,xb->xab', emissions[0][0][:, z[0]].T,
                      emissions[1][0][:, z[1]].T).reshape(8, -1)
    e_transformed = permutation.T @ e_all
    old_observable_pair = e_all.T @ (pi[:, None]*k) @ e_all
    new_observable_pair = e_transformed.T @ (transformed_pi[:, None]*transformed_k) @ e_transformed
    obs_error = float(np.max(abs(old_observable_pair-new_observable_pair)))
    # Positive product decomposition of every transformed next-state row.
    rows3 = transformed_k.reshape(8, 2, 2, 2)
    ma = rows3.sum(axis=(2, 3))
    mb = rows3.sum(axis=(1, 3))
    mc = rows3.sum(axis=(1, 2))
    prod = ma[:, :, None, None]*mb[:, None, :, None]*mc[:, None, None, :]
    twisted_error = float(np.max(abs(rows3-prod)))
    assert (twisted_error < 1e-10) == fair_private
    assert obs_error < 1e-14
    return {
        'fair_private_source': fair_private,
        'learned_patch_cardinalities': [x[0].shape[1] for x in learned],
        'learned_shared_factor_cardinality': count,
        'conditional_context_rows': int(old_valid.sum()),
        'private_complement_candidates_per_patch': 4,
        'accepted_complements_per_patch': accepted,
        'candidates': results,
        'threeview_max_reconstruction_error': max(errors),
        'xor_transport_observation_pair_error': obs_error,
        'xor_transformed_kernel_product_error': twisted_error,
        'maximum_raw_tensor_entries': m**3,
        'status': 'PASS',
        'scope': 'Exact-law fixture. Counts are locally product-compatible charts; tighter global parent or resource budgets require separate checks.'
    }


if __name__ == '__main__':
    result = {'nondegenerate': run(), 'ambiguous_fair_private': run(True)}
    Path(__file__).with_name('Private_Complement_QA.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))

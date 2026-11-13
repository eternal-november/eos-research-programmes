"""Exact-law QA for unsupplied local-state/patch-incidence discovery.

The finite global chain below is used ONLY to generate an exact test oracle.
The learner consumes bounded observable tensors, never that transition matrix,
the latent cardinalities, patch incidence, or latent labels.
"""
from __future__ import annotations
import itertools
import json
from pathlib import Path
import numpy as np


def softmax(a):
    v = np.exp(a - np.max(a))
    return v / v.sum()


def kernel(cards, i):
    qi, qp = cards[i], cards[(i - 1) % len(cards)]
    base = np.arange(1, qi + 1, dtype=float)
    base /= base.sum()
    out = np.empty((qi, qp, qi))
    for a in range(qi):
        for b in range(qp):
            score = np.array([
                .8 * np.cos((y + 1) * (a + 1))
                + .7 * np.sin((y + 1) * (b + 1))
                + 1.1 * ((a + b) % qi == y)
                + .4 * ((a * b + 1) % qi == y)
                for y in range(qi)
            ])
            # Genuine nonlinear coupling, uniformly positive. Each of two
            # parent influences is <= .30, giving a Dobrushin bound <= .60.
            out[a, b] = .70 * base + .30 * softmax(score)
    return out


def recover_three_view(t, rng):
    m12 = t.sum(axis=2)
    u, s, vt = np.linalg.svd(m12, full_matrices=False)
    rank = int(np.sum(s > 1e-11))
    u, v = u[:, :rank], vt[:rank].T
    middle = u.T @ m12 @ v
    inv = np.linalg.inv(middle)
    ops = [u.T @ t[:, :, k] @ v @ inv for k in range(t.shape[2])]
    best = None
    for _ in range(40):
        h = rng.normal(size=t.shape[2])
        op = sum(w * x for w, x in zip(h, ops))
        vals, vec = np.linalg.eig(op)
        if max(np.max(np.abs(vals.imag)), np.max(np.abs(vec.imag))) > 1e-8:
            continue
        vals, vec = vals.real, vec.real
        gap = min(abs(x - y) for j, x in enumerate(vals) for y in vals[j+1:])
        if best is None or gap > best[0]:
            best = (gap, vec)
    assert best is not None
    vec = best[1]
    a = u @ vec
    a /= a.sum(axis=0, keepdims=True)
    vinv = np.linalg.inv(vec)
    c = np.array([np.diag(vinv @ op @ vec) for op in ops])
    weighted_bt = np.linalg.pinv(a) @ m12
    weights = weighted_bt.sum(axis=1)
    b = (weighted_bt / weights[:, None]).T
    reconstruction = np.einsum('z,az,bz,cz->abc', weights, a, b, c)
    assert min(a.min(), b.min(), c.min(), weights.min()) > -1e-8
    return [a, b, c], weights, float(np.max(abs(reconstruction - t)))


def support_components(joint, threshold=1e-7):
    ka, kb = joint.shape
    adj = [[] for _ in range(ka + kb)]
    for a, b in zip(*np.nonzero(joint > threshold)):
        adj[a].append(ka + b)
        adj[ka + b].append(a)
    labels = np.full(ka + kb, -1, dtype=int)
    count = 0
    for start in range(ka + kb):
        if labels[start] >= 0:
            continue
        labels[start] = count
        stack = [start]
        while stack:
            x = stack.pop()
            for y in adj[x]:
                if labels[y] < 0:
                    labels[y] = count
                    stack.append(y)
        count += 1
    return count, labels[:ka], labels[ka:]


def run(seed=2731, delay=1):
    rng = np.random.default_rng(seed)
    # Oracle-only parameters. All fifteen sensor alphabets have size TEN,
    # so observed alphabet size does not specify patch/atom cardinalities.
    cards = [2, 3, 3, 2, 2] if delay == 1 else [2, 2, 3, 2]
    n, m = len(cards), 10
    states = np.array(list(itertools.product(*(range(q) for q in cards))))
    ns = len(states)
    local = [kernel(cards, i) for i in range(n)]
    if delay == 1:
        transition = np.ones((ns, ns))
        for i in range(n):
            transition *= local[i][states[:, i, None], states[:, (i-1) % n, None], states[None, :, i]]
        assert np.max(abs(transition.sum(axis=1)-1)) < 1e-12
        stationary = np.full(ns, 1/ns)
        for _ in range(10000):
            nxt = stationary @ transition
            if np.max(abs(nxt-stationary)) < 2e-16:
                stationary = nxt
                break
            stationary = nxt
        assert np.max(abs(stationary @ transition-stationary)) < 1e-14
    else:
        assert delay == 2
        # Axes: previous output, current output, new output. The true hidden
        # Markov state is a pair of output configurations, not supplied to learner.
        transition = np.ones((ns, ns, ns))
        for i in range(n):
            transition *= local[i][states[None, :, i, None], states[:, None, (i-1) % n, None], states[None, None, :, i]]
        assert np.max(abs(transition.sum(axis=2)-1)) < 1e-12
        stationary_history = np.full((ns, ns), 1/ns**2)
        for _ in range(10000):
            nxt = np.einsum('ab,abc->bc', stationary_history, transition)
            if np.max(abs(nxt-stationary_history)) < 2e-16:
                stationary_history = nxt
                break
            stationary_history = nxt
        joint_history_next = stationary_history[:, :, None] * transition
        assert np.max(abs(joint_history_next.sum(axis=0)-stationary_history)) < 1e-14
        stationary = stationary_history.sum(axis=0)
    true_patches = [(i, (i+1) % n) for i in range(n)]
    rng.shuffle(true_patches)
    z, true_emissions = [], []
    for i, j in true_patches:
        k = cards[i] * cards[j]
        perm = rng.permutation(k)
        z.append(perm[states[:, i]*cards[j]+states[:, j]])
        views = []
        for _ in range(3):
            a = rng.gamma(1.2, 1., size=(m, k)) + .15
            a /= a.sum(axis=0, keepdims=True)
            views.append(a)
        true_emissions.append(views)

    # Learner stage 1: only one-patch, three-view observable tensors.
    learned, tensor_errors, ranks = [], [], []
    for p in range(n):
        k = true_emissions[p][0].shape[1]
        pi = np.bincount(z[p], weights=stationary, minlength=k)
        tensor = np.einsum('z,az,bz,cz->abc', pi, *true_emissions[p])
        es, _, err = recover_three_view(tensor, rng)
        learned.append(es)
        tensor_errors.append(err)
        ranks.append(es[0].shape[1])

    # Learner stage 2: only two-patch, one-view observable matrices.
    atoms, overlap_error, zero_error, min_support = [], 0., 0., 1.
    for p in range(n):
        for q in range(p+1, n):
            kp, kq = true_emissions[p][0].shape[1], true_emissions[q][0].shape[1]
            jpq = np.zeros((kp, kq))
            np.add.at(jpq, (z[p], z[q]), stationary)
            observed = true_emissions[p][0] @ jpq @ true_emissions[q][0].T
            recovered = np.linalg.pinv(learned[p][0]) @ observed @ np.linalg.pinv(learned[q][0]).T
            overlap_error = max(overlap_error, float(abs(recovered.sum()-1)))
            zero_error = max(zero_error, float(np.max(abs(recovered[abs(recovered)<1e-7]))) if np.any(abs(recovered)<1e-7) else 0.)
            min_support = min(min_support, float(recovered[recovered>1e-7].min()))
            count, lp, lq = support_components(recovered)
            if count > 1:
                atoms.append({'patches': (p, q), 'maps': {p: lp, q: lq}, 'q': count})
    assert len(atoms) == n
    for p in range(n):
        incident = [a for a in atoms if p in a['maps']]
        assert len(incident) == 2
        pairs = set(zip(incident[0]['maps'][p], incident[1]['maps'][p]))
        assert len(pairs) == ranks[p] == incident[0]['q'] * incident[1]['q']

    # Decode *statistical moments*, not individual noisy observations.
    def decoder(atom_id, view):
        a = atoms[atom_id]
        p = min(a['patches'])
        projection = np.eye(a['q'])[:, a['maps'][p]]
        return p, projection @ np.linalg.pinv(learned[p][view])

    max_raw_entries = m**3
    count_temporal_tables = 0
    def joint_for(target, sources):
        nonlocal max_raw_entries, count_temporal_tables
        seen = {}
        src_observations, ds = [], []
        for atom_id, lag in sources:
            p = min(atoms[atom_id]['patches'])
            view = seen.get((p, lag), 0)
            seen[(p, lag)] = view+1
            assert view < 3
            p, d = decoder(atom_id, view)
            ds.append(d)
            src_observations.append(true_emissions[p][view][:, z[p]].T)
        p, dt = decoder(target, 0)
        target_observation = true_emissions[p][0][:, z[p]].T
        if delay == 1:
            features = np.ones((ns, 1))
            for o in src_observations:
                features = (features[:, :, None] * o[:, None, :]).reshape(ns, -1)
            raw = (features.T * stationary) @ transition @ target_observation
            raw = raw.reshape((m,)*(len(sources)+1))
        else:
            features = {0: np.ones((ns, 1)), 1: np.ones((ns, 1))}
            order = []
            for lag in [1, 0]:
                for j, ((_, ell), o) in enumerate(zip(sources, src_observations)):
                    if ell == lag:
                        features[lag] = (features[lag][:, :, None]*o[:, None, :]).reshape(ns, -1)
                        order.append(j)
            raw = np.einsum('abc,au,bv,cw->uvw', joint_history_next, features[1], features[0], target_observation, optimize=True)
            raw = raw.reshape((m,)*(len(sources)+1))
            order.append(len(sources))
            raw = raw.transpose(np.argsort(order))
        max_raw_entries = max(max_raw_entries, raw.size)
        count_temporal_tables += 1
        # Each decoder contracts its independent noisy sensor coordinate.
        letters = 'abcd'
        outletters = 'wxyz'
        specs = [letters[:len(sources)+1]]
        args = [raw]
        for j, d in enumerate(ds+[dt]):
            specs.append(outletters[j]+letters[j])
            args.append(d)
        equation = ','.join(specs)+'->'+outletters[:len(sources)+1]
        table = np.einsum(equation, *args)
        assert table.min() > -1e-7
        table = np.maximum(table, 0)
        table /= table.sum()
        return table

    learned_kernels, learned_parents, entropy_gaps = [], [], []
    candidate_parents = [(a, lag) for a in range(n) for lag in range(delay)]
    for target in range(n):
        choices = []
        for s in range(3):
            for sources in itertools.combinations(candidate_parents, s):
                table = joint_for(target, sources)
                mass = table.sum(axis=-1, keepdims=True)
                conditional = table / mass
                entropy = float(-np.sum(table * np.log(conditional)))
                choices.append((entropy, sources, conditional))
        hmin = min(x[0] for x in choices)
        winners = [x for x in choices if x[0] < hmin+1e-8]
        winner = min(winners, key=lambda x: len(x[1]))
        learned_parents.append(winner[1])
        learned_kernels.append(winner[2])
        wrong = [x[0] for x in choices if x[1] != winner[1]]
        entropy_gaps.append(min(wrong)-winner[0])

    # Oracle-only validation: identify learned factors with true coordinates.
    atom_to_true, learned_state = [], []
    emission_errors = []
    for a in atoms:
        p, q = a['patches']
        actual = set(true_patches[p]) & set(true_patches[q])
        assert len(actual) == 1
        i = actual.pop()
        atom_to_true.append(i)
        # Match tensor columns only for reporting error, never for discovery.
        costs = np.linalg.norm(learned[p][0][:, :, None] - true_emissions[p][0][:, None, :], axis=0)
        old_from_new = np.argmin(costs, axis=1)
        assert len(set(old_from_new)) == ranks[p]
        emission_errors.append(float(costs[np.arange(ranks[p]), old_from_new].max()))
        new_from_old = np.argsort(old_from_new)
        vals = a['maps'][p][new_from_old[z[p]]]
        for x in range(cards[i]):
            assert len(set(vals[states[:, i] == x])) == 1
        learned_state.append(vals)
    state_array = np.array(learned_state).T
    reconstructed_transition = np.ones_like(transition)
    for a, parent_ids in enumerate(learned_parents):
        i = atom_to_true[a]
        assert {(atom_to_true[j], lag) for j, lag in parent_ids} == {(i, 0), ((i-1) % n, delay-1)}
        q = learned_kernels[a]
        if delay == 1:
            for x in range(ns):
                row = q[tuple(state_array[x, j] for j, _ in parent_ids)]
                reconstructed_transition[x] *= row[state_array[:, a]]
        else:
            for old in range(ns):
                for cur in range(ns):
                    row = q[tuple(state_array[cur if lag == 0 else old, j] for j, lag in parent_ids)]
                    reconstructed_transition[old, cur] *= row[state_array[:, a]]
    max_kernel_error = float(np.max(abs(reconstructed_transition-transition)))
    max_row_tv = float(np.max(np.sum(abs(reconstructed_transition-transition), axis=-1)/2))
    assert max_row_tv < 2e-7

    # Delayed interface/source-memory relocation, pathwise exhaustive check.
    # State A: source current u, boundary register z=previous u, receiver v.
    # State B: source pair (u,z), memoryless boundary wire carrying z, receiver v.
    # Same positive update law; storage ownership alone changes.
    astates = list(itertools.product(range(2), repeat=3))
    bstates = [(pair, v) for v in range(2) for pair in itertools.product(range(2), repeat=2)]
    ka, kb, phi = np.zeros((8, 8)), np.zeros((8, 8)), np.zeros((8, 8))
    for ia, (u, zold, v) in enumerate(astates):
        ib = bstates.index(((u, zold), v))
        phi[ia, ib] = 1
        for unew, vnew in itertools.product(range(2), repeat=2):
            pu = (.2+.5*u) if unew else (1-(.2+.5*u))
            pv = .15+.2*v+.3*zold+.1*v*zold
            pv = pv if vnew else 1-pv
            ka[ia, astates.index((unew, u, vnew))] = pu*pv
    for ib, ((u, old), v) in enumerate(bstates):
        for newpair, newv in bstates:
            unew, stored = newpair
            if stored != u:
                continue
            p_source = [.8-.5*u, .2+.5*u][unew]
            p_receiver = [.85-.2*v-.3*old-.1*v*old, .15+.2*v+.3*old+.1*v*old][newv]
            kb[ib, bstates.index((newpair, newv))] = p_source*p_receiver
    assert np.all(phi.sum(axis=0) == 1) and np.all(phi.sum(axis=1) == 1)
    relocation_error = float(np.max(abs(ka @ phi - phi @ kb)))
    assert relocation_error < 1e-14
    # Pairwise marginals alone cannot guarantee a common joint state law.
    # Three binary pairs each demand disagreement with probability .75;
    # a triple has at most two disagreeing pairs on every sample.
    pairwise_disagreement_sum = 3*.75
    assert pairwise_disagreement_sum > 2

    return {
        'seed': seed,
        'maximum_candidate_delay': delay,
        'fixture_hidden_components': n,
        'fixture_global_markov_states_for_oracle_only': ns**delay,
        'sensor_alphabet_size_all_views': m,
        'learned_patch_cardinalities': ranks,
        'learned_component_cardinalities': [a['q'] for a in atoms],
        'learned_patch_overlap_edges': [list(a['patches']) for a in atoms],
        'true_component_index_for_validation_only': atom_to_true,
        'learned_parent_component_indices': [list(s) for s in learned_parents],
        'threeview_max_reconstruction_error': max(tensor_errors),
        'sensor_column_max_alignment_error': max(emission_errors),
        'overlap_normalization_error': overlap_error,
        'overlap_recovered_zero_error': zero_error,
        'minimum_recovered_overlap_positive_mass': min_support,
        'minimum_wrong_parent_conditional_entropy_gap': min(entropy_gaps),
        'temporal_tables_used': count_temporal_tables,
        'maximum_raw_observable_tensor_entries': max_raw_entries,
        'full_kernel_validation_max_entry_error': max_kernel_error,
        'full_kernel_validation_max_row_tv': max_row_tv,
        'memory_relocation_pathwise_probability_error': relocation_error,
        'incompatible_pair_disagreement_total': pairwise_disagreement_sum,
        'status': 'PASS',
        'scope': 'Exact probability-law numerical QA; not a finite-data theorem or production learner.'
    }


if __name__ == '__main__':
    result = {'memoryless': run(), 'delayed': run(seed=3929, delay=2)}
    path = Path(__file__).with_name('Hidden_Patch_Discovery_QA.json')
    path.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))

"""Polynomial parity-invariance checker for an OVERAPPROXIMATION graph.
No tags/ranks are inferred: packet indices are arbitrary input row identities.
Standard library only. Roles are arbitrary hashable labels; payloads are bits.
"""
from collections import deque


def perfect_matching(edges):
    n = len(edges)
    match, owner = [-1] * n, [-1] * n
    for start in range(n):
        q, prev, seen = deque([start]), {}, {start}
        end = None
        while q and end is None:
            i = q.popleft()
            for v in edges[i]:
                if v in prev:
                    continue
                prev[v] = i
                if owner[v] < 0:
                    end = v
                    break
                j = owner[v]
                if j not in seen:
                    seen.add(j)
                    q.append(j)
        if end is None:
            return None
        v = end
        while v >= 0:
            i = prev[v]
            old = match[i]
            match[i], owner[v] = v, i
            v = old
    return match


def sccs(adj):
    n = len(adj)
    rev = [[] for _ in adj]
    for i, row in enumerate(adj):
        for j in row:
            rev[j].append(i)
    seen, order = set(), []
    for r in range(n):
        if r in seen:
            continue
        seen.add(r)
        stack = [(r, iter(adj[r]))]
        while stack:
            i, it = stack[-1]
            j = next(it, None)
            if j is None:
                order.append(i)
                stack.pop()
            elif j not in seen:
                seen.add(j)
                stack.append((j, iter(adj[j])))
    groups, seen = [], set()
    for r in reversed(order):
        if r in seen:
            continue
        group, stack = [], [r]
        seen.add(r)
        while stack:
            i = stack.pop()
            group.append(i)
            for j in rev[i]:
                if j not in seen:
                    seen.add(j)
                    stack.append(j)
        groups.append(group)
    return groups, rev


def parity(match, role_masks, bits):
    result = 0
    for i, v in enumerate(match):
        if bits[v]:
            result ^= role_masks[i]
    return result


def nonzero_simple_cycle(walk, weight):
    """Decompose a closed directed walk; select a nonzero simple cycle."""
    stack, pos = [walk[0]], {walk[0]: 0}
    for v in walk[1:]:
        if v not in pos:
            pos[v] = len(stack)
            stack.append(v)
            continue
        k = pos[v]
        cycle = stack[k:] + [v]
        total = 0
        for a, b in zip(cycle, cycle[1:]):
            total ^= weight(a, b)
        if total:
            return cycle
        for x in stack[k + 1:]:
            del pos[x]
        stack = stack[:k + 1]
    raise AssertionError('nonzero closed walk must contain a nonzero cycle')


def check(edges, roles, bits):
    """Return CERTIFIED, UNRESOLVED, or NO_GRAPH_MATCHING, plus a witness.

    CERTIFIED is conditional on the true physical assignment belonging to edges.
    UNRESOLVED never asserts two physical worlds exist.
    NO_GRAPH_MATCHING flags incompatible evidence/model, NOT vacuous success.
    """
    n = len(roles)
    if len(edges) != n or len(bits) != n or any(b not in (0, 1) for b in bits):
        raise ValueError('requires n jobs, n reports and binary payloads')
    edges = [sorted(set(row)) for row in edges]
    if any(not isinstance(v, int) or not 0 <= v < n for row in edges for v in row):
        raise ValueError('packet index out of range')
    labels = list(dict.fromkeys(roles))
    index = {r: k for k, r in enumerate(labels)}
    masks = [1 << index[r] for r in roles]
    m = perfect_matching(edges)
    if m is None:
        return {'status': 'NO_GRAPH_MATCHING'}
    owner = {v: i for i, v in enumerate(m)}
    adj = [[] for _ in roles]
    for j, row in enumerate(edges):
        for v in row:
            adj[owner[v]].append(j)
    def weight(i, j):
        return (masks[i] ^ masks[j]) if bits[m[i]] else 0
    groups, rev = sccs(adj)
    potentials = [0] * n
    bad_walk = None
    for group in groups:
        allowed, root = set(group), group[0]
        # Concrete directed root-to-vertex paths and vertex-to-root paths.
        out, back = {root: [root]}, {root: [root]}
        q = deque([root])
        while q:
            i = q.popleft()
            for j in adj[i]:
                if j in allowed and j not in out:
                    out[j] = out[i] + [j]
                    potentials[j] = potentials[i] ^ weight(i, j)
                    q.append(j)
        q = deque([root])
        while q:
            i = q.popleft()
            for j in rev[i]:
                if j in allowed and j not in back:
                    back[j] = [j] + back[i]
                    q.append(j)
        back_weights = {}
        for i in group:
            value = 0
            for a, b in zip(back[i], back[i][1:]):
                value ^= weight(a, b)
            back_weights[i] = value
            if value != potentials[i]:
                bad_walk = out[i] + back[i][1:]
                break
        if bad_walk is not None:
            break
        for i in group:
            for j in adj[i]:
                if j in allowed and potentials[i] ^ weight(i, j) ^ potentials[j]:
                    bad_walk = out[i] + [j] + back[j][1:]
                    break
            if bad_walk is not None:
                break
        if bad_walk is not None:
            break
    base = {'matching': m, 'role_labels': labels, 'parity_mask': parity(m, masks, bits)}
    if bad_walk is None:
        return dict(base, status='CERTIFIED', components=groups, potentials=potentials)
    cycle = nonzero_simple_cycle(bad_walk, weight)
    other = m.copy()
    for i, j in zip(cycle, cycle[1:]):
        other[j] = m[i]
    assert len(set(other)) == n and all(v in edges[i] for i, v in enumerate(other))
    other_parity = parity(other, masks, bits)
    assert other_parity != base['parity_mask']
    return dict(base, status='UNRESOLVED', other_matching=other,
                other_parity_mask=other_parity, directed_cycle=cycle)


def from_windows(windows, timestamps, roles, bits):
    """Closed rational/integer windows; use exact numbers, not noisy float tests.
    The caller certifies that the learned-window construction covers truth.
    Timestamp ties are allowed. No timestamp sorting or stable rank is used.
    """
    if len(windows) != len(roles) or len(timestamps) != len(bits):
        raise ValueError('dimension mismatch')
    if any(lo > hi for lo, hi in windows):
        raise ValueError('inverted window')
    edges = [[v for v, t in enumerate(timestamps) if lo <= t <= hi]
             for lo, hi in windows]
    return check(edges, roles, bits)


def verify_positive(edges, roles, bits, certificate):
    """Independently check a positive witness; recompute SCCs, never trust them."""
    try:
        n = len(roles)
        if len(edges) != n or len(bits) != n or any(b not in (0, 1) for b in bits):
            return False
        m = certificate['matching']
        labels = list(dict.fromkeys(roles))
        if certificate['status'] != 'CERTIFIED' or certificate['role_labels'] != labels:
            return False
        if len(m) != n or set(m) != set(range(n)):
            return False
        if any(v not in edges[i] for i, v in enumerate(m)):
            return False
        masks = [1 << labels.index(r) for r in roles]
        if certificate['parity_mask'] != parity(m, masks, bits):
            return False
        p = certificate['potentials']
        if len(p) != n or any(not isinstance(x, int) or not 0 <= x < (1 << len(labels)) for x in p):
            return False
        owner = {v: i for i, v in enumerate(m)}
        adj = [[] for _ in roles]
        for j, row in enumerate(edges):
            for v in row:
                adj[owner[v]].append(j)
        groups, _ = sccs(adj)
        component = {i: k for k, group in enumerate(groups) for i in group}
        for i, row in enumerate(adj):
            for j in row:
                if component[i] == component[j]:
                    w = (masks[i] ^ masks[j]) if bits[m[i]] else 0
                    if p[i] ^ p[j] != w:
                        return False
        return True
    except (KeyError, TypeError, IndexError, ValueError):
        return False

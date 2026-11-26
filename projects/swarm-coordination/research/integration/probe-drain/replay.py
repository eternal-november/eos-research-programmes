"""Exact sequential model and independent periodic construction."""
from collections import deque
from itertools import combinations
import json


def reaches(h, n, c, q):
    """Find any q-quiet block in a bi-infinite freshness-valid trace.

    States start with all legal abstract prehistories of ages admitting an
    infinite past. Compute that set by deleting states with no incoming edge,
    then similarly remove states with no infinite continuation. Search all
    remaining states from quiet age zero, so the q states count forward slots.
    """
    from itertools import product
    states = set(product(range(h), repeat=n))
    actions = [ix for k in range(min(n, c) + 1)
               for ix in combinations(range(n), k)]
    edges = {}
    for ages in states:
        nxt = []
        for ix in actions:
            nxt_ages = tuple(0 if j in ix else a + 1 for j, a in enumerate(ages))
            if max(nxt_ages, default=0) < h:
                nxt.append((nxt_ages, not ix))
        edges[ages] = nxt
    while True:
        outgoing = {s for s in states if any(t in states for t, _ in edges[s])}
        incoming = {t for s in states for t, _ in edges[s]}
        keep = outgoing & incoming & states
        if keep == states:
            break
        states = keep
    seen = {(s, 0) for s in states}
    todo = deque(seen)
    while todo:
        s, age = todo.popleft()
        if age == q:
            return True
        for t, isquiet in edges[s]:
            node = (t, age + 1 if isquiet else 0)
            if t in states and node not in seen:
                seen.add(node)
                todo.append(node)
    return False


def constructive(h, n, c, q):
    if n == 0:
        return True
    if c == 0 or (n + c - 1) // c > h:
        return False
    slots = tuple(tuple(range(i * c, min(n, (i + 1) * c))) for i in range(h))
    trace = slots * (3 + q // h)
    for i in range(len(trace) - h + 1):
        assert set().union(*map(set, trace[i:i + h])) == set(range(n))
    return any(not any(trace[i:i + q]) for i in range(len(trace) - q + 1))


def watchdog(phases, h=4, q=3, steps=24):
    age, settled, trace = 0, None, []
    for t in range(steps):
        # While degraded, a stale/timeout cycle asks for a diagnostic.
        # After settlement the external freshness law uses qualified read-only updates.
        probes = sum(t % h == p for p in phases) if settled is None else 0
        age = 0 if probes else age + 1
        if settled is None and age >= q:
            settled = t
        trace.append((probes, age))
    return settled, trace[:12]


checked = 0
for h in range(1, 6):
    for n in range(5):
        for c in range(4):
            for q in range(h + 3):
                bound = n <= c * max(0, h - q)
                assert reaches(h, n, c, q) == constructive(h, n, c, q) == bound
                checked += 1
single, opposite, aligned = (watchdog(p) for p in [(0,), (0, 2), (0, 0)])
assert (single[0], opposite[0], aligned[0]) == (3, None, 3)
# Both legal opposite-phase local streams are kept fresh, but their probes reset a
# joint fixture. The periodic schedule model continues intrusive reads after
# settling; this additional trace models supervised transition to read-only mode.



def transient_direct(h, ages, c, s, q):
    states = {ages}
    n = len(ages)
    active = [tuple(ix) for k in range(min(n, c) + 1)
              for ix in combinations(range(n), k)]
    for tick in range(1, s+q+1):
        next_states = set()
        for state in states:
            for ix in active if tick <= s else [()]:
                child = tuple(0 if j in ix else a + 1
                              for j, a in enumerate(state))
                if max(child, default=0) < h:
                    next_states.add(child)
        states = next_states
    return bool(states)


def transient_cut(h, ages, c, s, q):
    due = sorted(min(s, h-a) for a in ages if h-a <= s+q)
    return all(k <= c * d for k, d in enumerate(due, 1))


from itertools import product
transient_count = 0
for h in range(1, 6):
    for n in range(4):
        for ages in product(range(h), repeat=n):
            for c in range(3):
                for s in range(h):
                    for q in range(1, h-s+1):
                        assert transient_direct(h, ages, c, s, q) == transient_cut(h, ages, c, s, q)
                        transient_count += 1
assert transient_cut(4, (3,0), 2, 1, 3)
assert not transient_cut(4, (3,2,1), 2, 0, 3)
assert not transient_cut(4, (3,2,1), 2, 1, 3)
assert not transient_cut(4, (3,2), 2, 0, 3)
assert transient_cut(4, (0,0), 2, 0, 3)
print(json.dumps(dict(periodic_checked=checked, transient_checked=transient_count, single=single, opposite=opposite, aligned=aligned), indent=2))

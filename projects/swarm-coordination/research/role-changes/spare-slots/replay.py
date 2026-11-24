"""Exact, offline checker for synthetic unit-slot maintenance role changes."""
from itertools import combinations, product
from pathlib import Path
import json


def subsets(xs):
    xs = tuple(sorted(xs))
    for n in range(len(xs) + 1):
        yield from map(frozenset, combinations(xs, n))


def matching(edges, slots):
    """Factored direct augmenting-path baseline, returns job -> slot."""
    owner = {}

    def augment(job, seen):
        for slot in sorted(edges[job] & slots):
            if slot in seen:
                continue
            seen.add(slot)
            if slot not in owner or augment(owner[slot], seen):
                owner[slot] = job
                return True
        return False

    for job in sorted(edges):
        augment(job, set())
    return {j: s for s, j in owner.items()}


def direct(old, new, slots):
    assert old.keys().isdisjoint(new.keys())
    ed = old | new
    return len(matching(ed, slots)) == len(ed)


def occupied(edges, slots):
    """Independent slot-first exhaustive exact capacity relation."""
    if not slots:
        return frozenset({frozenset()})
    s = min(slots)
    rem = slots - {s}
    ans = set(occupied(edges, rem))
    for j, nbr in edges.items():
        if s in nbr:
            ans.update(p | {s} for p in occupied({k: v for k, v in edges.items() if k != j}, rem))
    return frozenset(ans)


def assemble(left, right):
    return frozenset(s | t for s in left for t in right if not s & t)


def spare(rel, n, slots):
    return frozenset(t for t in subsets(slots)
                     if any(len(p) == n and not p & t for p in rel))


def from_spare(free, n, slots):
    return frozenset(t for f in free if len(f) == len(slots) - n
                     for t in subsets(slots - f))


def rho(free, t):
    return max(len(f & t) for f in free)


def query(free, new):
    return any(len(matching(new, f)) == len(new) for f in free)


def intersection(worlds):
    assert all(w.keys() == worlds[0].keys() for w in worlds)
    return {j: frozenset.intersection(*(w[j] for w in worlds)) for j in worlds[0]}


def timeline(pocket, b_delayed, slots, plan, new):
    """Event-level check; validates actual admissions and service, not ranking."""
    trace, pending = [], {}
    epoch, gate = -1, None

    def install(t, candidate):
        nonlocal gate, epoch
        epoch += 1
        gate = candidate
        trace.append((t, 'gate_install', candidate, epoch))

    def accept(t, actor, proposed_epoch, job):
        ok = (actor, proposed_epoch) == (gate, epoch) and job not in pending
        trace.append((t, 'admission', actor, proposed_epoch, job, ok))
        if ok:
            pending[job] = t
        return ok

    install(0, 'A')
    assert accept(0, 'A', 0, 'first-tote')
    trace.append((0, 'coverage', ['D']))
    trace.append((0, 'closure_authorized', 'first-tote', 'D', 'evidence after intake'))
    install(1, 'B')
    trace.append((1, 'coverage', ['C', 'D']))
    assert accept(1, 'B', 1, 'second-tote')
    assert set(pending) == {'first-tote', 'second-tote'}
    trace.append((1, 'closure_authorized', 'second-tote', 'D', 'scheduled inspection'))
    trace.append((2, 'public_missing_health_report', 'B'))
    trace.append((2, 'certified_intake_state', pocket))
    install(2, 'C')
    # The same in-flight B request reaches the independent interlock even if B
    # has since stopped. The old grant cannot acquire new authority.
    assert not accept(2, 'B', 1, 'stale-new-request')
    if new:
        assert accept(2, 'C', 2, 'new-tote')
    else:
        trace.append((2, 'declined_before_acceptance', 'new-tote'))
    assert len(plan) == len(set(plan.values()))
    assert set(plan.values()) <= slots
    expected = {'first-tote', 'second-tote', 'relay2', 'relay3'}
    assert set(plan) == expected | ({'new-tote'} if new else set())
    permits = {'first-tote': {'A', 'D'} if pocket == 'intact' else {'D'},
               'second-tote': {'D'}, 'new-tote': {'C'}}
    due = {'first-tote': 2, 'second-tote': 3, 'new-tote': 2}
    for t in (2, 3):
        for j, s in sorted(plan.items()):
            if s[1] != str(t):
                continue
            actor = s[0]
            if j.startswith('relay'):
                assert t == int(j[-1])
                assert (actor in {'C', 'D'} or (actor == 'B' and t == 2 and b_delayed))
                trace.append((t, 'coverage', [actor]))
            else:
                assert t == due[j] and actor in permits[j]
                assert pending.pop(j) <= t
                trace.append((t, 'physical_discharge', j, actor))
        assert any(x[0] == t and x[1] == 'coverage' for x in trace)
    assert not pending
    return trace


def edges_for(pocket, b_delayed):
    return {
        'first-tote': frozenset({'A2', 'D2'} if pocket == 'intact' else {'D2'}),
        'second-tote': frozenset({'D3'}),
        'relay2': frozenset({'C2', 'D2'} | ({'B2'} if b_delayed else set())),
        'relay3': frozenset({'C3', 'D3'}),
    }


def concrete():
    slots = frozenset({'A2', 'B2', 'C2', 'D2', 'C3', 'D3'})
    new = {'new-tote': frozenset({'C2'})}
    result = {}
    for pocket in ('intact', 'damaged'):
        sample = [edges_for(pocket, delayed) for delayed in (False, True)]
        old = intersection(sample)
        candidate = matching(old | new, slots)
        positive = pocket == 'intact'
        assert direct(old, new, slots) == positive
        assert len(candidate) == len(old | new) if positive else len(candidate) < len(old | new)
        if positive:
            action = candidate
        else:
            action = matching(old, slots)
            assert len(action) == len(old)
            cut = {'first-tote', 'relay2', 'new-tote'}
            assert set.union(*(set((old | new)[j]) for j in cut)) == {'C2', 'D2'}
        assert direct(sample[1], new, slots)  # omniscient delayed report world
        assert not direct(sample[0], new, slots) if not positive else direct(sample[0], new, slots)
        result[pocket] = {'admit': positive, 'schedule': action,
                          'trace_healthy_delayed': timeline(pocket, True, slots, action, positive),
                          'trace_failed': timeline(pocket, False, slots, action, positive)}
    return result


def exhaustive():
    slots = frozenset('ABC')
    nbrs = tuple(subsets(slots))
    families, checked = set(), 0
    for a, b, c in product(nbrs, repeat=3):
        one, two, three = {'a': a}, {'b': b}, {'c': c}
        x, y, z = (occupied(g, slots) for g in (one, two, three))
        joined = assemble(x, y)
        assert joined == occupied(one | two, slots)
        assert assemble(joined, z) == assemble(x, assemble(y, z)) == occupied(one | two | three, slots)
        f = spare(joined, 2, slots)
        if not f:
            assert not direct(one | two, {}, slots)
            assert not spare(assemble(joined, z), 3, slots)
            continue
        families.add(f)
        f1, f2 = spare(x, 1, slots), spare(y, 1, slots)
        assert assemble(from_spare(f1, 1, slots), from_spare(f2, 1, slots)) == joined
        for t in nbrs:
            formula = len(t) - 2 + len(matching(one | two, slots - t))
            assert rho(f, t) == formula
            probes = {s: frozenset({s}) for s in t}
            assert query(f, probes) == direct(one | two, probes, slots) == (t in f)
        for p, q in product(nbrs, repeat=2):
            new = {'u': p, 'v': q}
            assert query(f, new) == direct(one | two, new, slots)
            assert query(f, new) == all(
                rho(f, frozenset().union(*(new[j] for j in u))) >= len(u)
                for u in subsets(new))
            checked += 1
    # A second check with a larger slot universe where two optional jobs can fit.
    slots = frozenset('ABCD')
    nbrs = tuple(subsets(slots))
    for a, b in product(nbrs, repeat=2):
        old = {'a': a, 'b': b}
        f = spare(occupied(old, slots), 2, slots)
        for p, q in product(nbrs, repeat=2):
            new = {'u': p, 'v': q}
            assert direct(old, new, slots) == query(f, new) == (
                bool(f) and all(rho(f, frozenset().union(*(new[j] for j in u))) >= len(u)
                                   for u in subsets(new)))
            checked += 1
    return {'three_slot_union_tuples': 512, 'distinct_spare_families_three_slots_two_duties': len(families),
            'admission_oracle_checks': checked}


def marginal_trap():
    slots = frozenset('ABCD')
    x = {'a': frozenset('AB'), 'b': frozenset('CD')}
    y = {'a': frozenset('AC'), 'b': frozenset('BD')}
    fx, fy = (spare(occupied(g, slots), len(g), slots) for g in (x, y))
    assert rho(fx, slots) == rho(fy, slots) == 2
    assert all(rho(fx, {s}) == rho(fy, {s}) == 1 for s in slots)
    p = {s: frozenset({s}) for s in 'AB'}
    assert not query(fx, p) and query(fy, p)
    return {'same_singleton_and_total_rank': True, 'joint_probe': 'AB', 'x': False, 'y': True}


def strict_recourse():
    slots = frozenset({'D2', 'C3', 'D3'})
    core = {'relay2': frozenset({'D2'})}
    worlds = [core | {'closure': frozenset({s})} for s in ('C3', 'D3')]
    assert not direct(intersection(worlds), {}, slots)
    # Histories agree until time 2; public test before time 3 selects branch.
    assert all(matching(w, slots)['relay2'] == 'D2' for w in worlds)
    assert all(len(matching(w, slots)) == len(w) for w in worlds)
    return [matching(w, slots) for w in worlds]


if __name__ == '__main__':
    import argparse
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument('--verify', action='store_true')
    args = cli.parse_args()
    out = json.dumps({'finite_scope': exhaustive(), 'physical_trace': concrete(),
                      'strict_recourse': strict_recourse(), 'marginal_trap': marginal_trap()}, indent=2, sort_keys=True) + '\n'
    if args.verify:
        assert out == Path(__file__).with_name('results.json').read_text()
    print(out, end='')

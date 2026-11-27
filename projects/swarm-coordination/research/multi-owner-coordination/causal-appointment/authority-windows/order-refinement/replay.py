"""Frozen cut certificates under dependency refinement. Standard library only."""
import itertools
import json
import random


def ideals(pred):
    return [x for x in range(1 << len(pred))
            if all(not x >> i & 1 or (x & p) == p for i,p in enumerate(pred))]


def inside(x, l, u):
    return x & l == l and x & u == x


def extrema(cuts):
    if not cuts:
        return None
    l = u = cuts[0]
    for x in cuts[1:]:
        l &= x
        u |= x
    return l, u


def restrict(ideals_new, old, summary, newbox):
    if summary is None:
        return []
    return [x for x in ideals_new if inside(x & old, *summary) and inside(x, *newbox)]


def close_required(pred, initial):
    result = initial
    for i in reversed(range(len(pred))):
        if result >> i & 1:
            result |= pred[i]
    return result


def propagated(pred, old, summary, box):
    if summary is None:
        return None
    l,u = summary
    m,h = box
    forbidden = (old ^ u) | (((1 << len(pred))-1) ^ h)
    low = close_required(pred,l|m)
    for i,p in enumerate(pred):
        if forbidden & p:
            forbidden |= 1<<i
    if low & forbidden:
        return None
    return low, ((1 << len(pred))-1) ^ forbidden


def paired_change():
    # Bits: 0 old withdrawal, 1 new appointment, 2 gate commit.
    # Gate commit has appointment as predecessor. The replacement strengthens
    # the appointment input by requiring it to observe withdrawal too.
    historical = (0, 0)
    enlarged = (0, 0, 2)
    learned = (0, 1, 3)
    # Each standalone authority still admits some old or extended cut.
    rescue = (4, 7)
    old_receipt = (0, 2)
    frozen = extrema([x for x in ideals(historical) if inside(x, *old_receipt)])
    a = restrict(ideals(enlarged), 3, frozen, rescue)
    b = restrict(ideals(learned), 3, frozen, rescue)
    assert a == [6] and not b
    assert [x for x in ideals(learned) if inside(x,*rescue)] == [7]
    # If a dependency is removed, unequal original authority rules can share
    # the same cached interval under the old order but differ after replacement.
    raw1, raw2 = (2,3),(3,3)
    old = (0,1)
    weaker = (0,0)
    old1, old2 = (extrema([x for x in ideals(old) if inside(x,*g)])
                  for g in (raw1,raw2))
    assert old1 == old2 == (3,3)
    assert [x for x in ideals(weaker) if inside(x,*raw1)] == [2,3]
    assert [x for x in ideals(weaker) if inside(x,*raw2)] == [3]
    return dict(fresh_cut=a, discovered_old_dependency_cut=b,
                lost_edge_witness=2)


def audit():
    rng = random.Random(656072)
    incompatible = newly_blocked = fiber_checks = negative_witnesses = 0
    for _ in range(8192):
        n = 6
        base = [rng.getrandbits(i) for i in range(n)]
        weaker = [p & rng.getrandbits(i) for i,p in enumerate(base)]
        stronger = [p | rng.getrandbits(i) for i,p in enumerate(base)]
        # Keep a mixed separator in general, not necessarily a prefix of the
        # simulated event schedule. Induced order includes transitive paths.
        oldmask = rng.randrange(1, 1<<n)
        small = sorted({x & oldmask for x in ideals(base)})
        more = ideals(stronger)
        l = rng.getrandbits(n) & oldmask
        u = (rng.getrandbits(n) | l) & oldmask
        m = rng.getrandbits(n)
        h = rng.getrandbits(n) | m
        summary = extrema([x for x in small if inside(x,l,u)])
        complete = [x for x in more if inside(x&oldmask,l,u) and inside(x,m,h)]
        assert complete == restrict(more, oldmask, summary, (m,h))
        assert extrema(complete) == propagated(stronger, oldmask, summary, (m,h))
        incompatible += not complete
        newly_blocked += bool(summary) and not complete
        for cuts in (complete, [x for x in more if inside(x,m,h)]):
            if not cuts:
                continue
            low, hi = extrema(cuts)
            projection = {x & oldmask for x in cuts}
            valid_old = {x & oldmask for x in more}
            assert projection == {x for x in valid_old if inside(x,low&oldmask,hi&oldmask)}
            for y in projection:
                fiber = [x for x in cuts if x & oldmask == y]
                lo2, hi2 = extrema(fiber)
                assert fiber == [x for x in more if inside(x,lo2,hi2)]
                fiber_checks += 1
        lost = sorted(set(ideals(weaker)) - set(ideals(base)))
        if lost:
            y = lost[0]
            d, allbits = y, (1<<n)-1
            lower = extrema([x for x in ideals(base) if inside(x,d,allbits)])[0]
            assert lower != y
            before1 = [x for x in ideals(base) if inside(x,d,allbits)]
            before2 = [x for x in ideals(base) if inside(x,lower,allbits)]
            assert before1 == before2
            assert inside(y,d,allbits) and not inside(y,lower,allbits)
            negative_witnesses += 1
    return dict(instances=8192, incompatible=incompatible,
                blocked_after_conjunction=newly_blocked, fibers=fiber_checks,
                weakened_order_witnesses=negative_witnesses)


if __name__ == '__main__':
    print(json.dumps(dict(example=paired_change(), audit=audit()), sort_keys=True, indent=2))

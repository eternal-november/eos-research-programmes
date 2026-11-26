"""Exact historical grant compatibility for a fixed finite causal history."""
import itertools as it
import json
import random


def le(x, y):
    return all(a <= b for a, b in zip(x, y))


def cap(xs, op):
    return tuple(map(op, zip(*xs)))


def closed(x, floors):
    return all(le(floors[i][v], x) for i, v in enumerate(x))


def closure(lower, floors):
    return cap([lower] + [floors[i][v] for i, v in enumerate(lower)], max)


def interval(l, h, floors):
    first = closure(l, floors)
    if not le(first, h):
        return None
    # A prefix is includable iff its entire causal past fits h.
    last = tuple(max(v for v in range(hi + 1) if le(floors[i][v], h))
                 for i, hi in enumerate(h))
    assert closed(last, floors) and le(first, last)
    return first, last


def join(a, b):
    if a is None or b is None:
        return None
    first, last = cap([a[0], b[0]], max), cap([a[1], b[1]], min)
    return (first, last) if le(first, last) else None


def fixture():
    # A's v2 carries an actual cross-ledger dependency on B's v1.
    independent = [[(0, 0)] * 3, [(0, 0)] * 2]
    dependent = [[(0, 0), (0, 0), (0, 1)], [(0, 0)] * 2]
    old = ((0, 0), (2, 0))   # old permit not yet withdrawn at B
    new = ((2, 0), (2, 1))   # next issue requires A's new appointment
    cases = []
    for dep, access, clear in it.product((0, 1), repeat=3):
        world = dependent if dep else independent
        a, b = (interval(*p, world) for p in [old, new])
        result = join(a, b)
        # Both isolated claims hold; the common cut may not.
        assert a is not None and b is not None
        assert (result is not None) == (not dep)
        effect = bool(result and access and clear)
        cases.append(dict(dependency=dep, access=access, clear=clear,
                          historical_cut=None if result is None else result[0],
                          modeled_rescue=effect))
    return cases


def audit():
    rng = random.Random(655031)
    successes = failures = pair_only_failure = 0
    for _ in range(20480):
        n, m = 3, 5
        tokens = [i for i in range(n) for _ in range(m-1)]
        rng.shuffle(tokens)
        floors = [[(0,)*n] for _ in range(n)]
        for i in tokens:
            floor = list(floors[i][-1])
            for j in range(n):
                if j != i and rng.randrange(3) == 0:
                    v = rng.randrange(len(floors[j]))
                    floor = list(cap([floor, floors[j][v]],max))
                    floor[j] = max(floor[j],v)
            floors[i].append(tuple(floor))
        windows = []
        for _ in range(rng.randrange(1,7)):
            bounds = [sorted(rng.choices(range(m), k=2)) for j in range(n)]
            windows.append(tuple(zip(*bounds)))
        direct = [x for x in it.product(range(m),repeat=n)
                  if closed(x,floors) and all(le(l,x) and le(x,h) for l,h in windows)]
        summaries = [interval(l,h,floors) for l,h in windows]
        fold = ((0,)*n,(m-1,)*n)
        for s in summaries:
            fold = join(fold,s)
        true_bounds = (cap(direct,min),cap(direct,max)) if direct else None
        assert fold == true_bounds
        assert bool(direct) == (all(s is not None for s in summaries) and
                                all(join(a,b) is not None for a,b in it.combinations(summaries,2)))
        successes += bool(direct)
        failures += not direct
        pair_only_failure += not direct and all(s is not None for s in summaries)
    return dict(satisfiable=successes, infeasible=failures,
                unsatisfiable_with_all_individually_valid=pair_only_failure)


def regrant():
    sizes = list(range(2, 257))
    for m in sizes:
        # Cooperative issuers share just one relevant reference ledger.
        # Grant i accepts every version except the excluded amendment i.
        masks = [((1<<m)-1) ^ (1<<i) for i in range(m)]
        blank = (1<<m)-1
        pre, post = [blank], [blank]
        for p in masks:
            pre.append(pre[-1] & p)
        for p in reversed(masks):
            post.append(post[-1] & p)
        assert pre[-1] == 0
        assert all(pre[i] & post[m-i-1] == 1<<i for i in range(m))
    return dict(smallest=sizes[0], largest=sizes[-1], families=len(sizes))


if __name__ == '__main__':
    print(json.dumps(dict(fixtures=fixture(), audit=audit(), regrant=regrant()),
                     indent=2, sort_keys=True))


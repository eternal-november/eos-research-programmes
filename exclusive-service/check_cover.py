"""Independent finite checks of the blocker synthesis, timing certificate and policy boundary."""
from itertools import combinations

from cover import Blocked, RouteTime, certify, deadline_profile, minimal_blockers, project_windows


def subsets(items):
    items = tuple(items)
    for size in range(len(items) + 1):
        for group in combinations(items, size):
            yield frozenset(group)


def check():
    alphabet = tuple(subsets(range(3)))
    comparisons = 0
    for routes in subsets(alphabet):
        frontier = minimal_blockers(routes)
        direct = {mask for mask in alphabet if all(mask & route for route in routes)}
        assert frontier == {mask for mask in direct if not any(other < mask for other in direct)}
        price = {route: 2 * len(route) + sum(route) for route in routes}
        scheduled = [RouteTime(route, tick) for route, tick in price.items()]
        for mask in alphabet:
            candidates = [route for route in routes if not route & mask]
            try:
                result, choices = deadline_profile(scheduled, [mask])
            except Blocked as exc:
                assert not candidates and exc.mask == mask
                assert set(dict(exc.hits)) == routes
                assert all(hit in mask and hit in route for route, hit in exc.hits)
            else:
                assert candidates and choices[mask].route in candidates
                assert result == min(price[route] for route in candidates)
            comparisons += 1
    # The same later control state can have different earlier denial histories.
    def split(_):
        return [("common", {"P"}), ("common", {"Q"})]
    def advance(state):
        return [(state, set())]
    masks = project_windows(("start",), (split, advance))
    assert set(masks) == {frozenset({"P"}), frozenset({"Q"})}
    assert all(path[0].after == path[1].before for path in masks.values())
    try:
        project_windows(("start",), (lambda _: (),))
    except ValueError as exc:
        assert "stall" in str(exc)
    else:
        raise AssertionError("A stopped source prefix vanished from the positive domain")
    # The positive uses below exercise all routes under a single installed local policy.
    # If only one route can be chosen on an identical input view, the quantifiers change.
    hidden = [frozenset({"P"}), frozenset({"Q"})]
    binary_routes = [{"P"}, {"Q"}]
    assert len(certify(binary_routes, hidden)) == 2
    assert not any(all(route.isdisjoint(mask) for mask in hidden) for route in binary_routes)
    # A shared transaction cannot mint two outcome records.
    good = {(1, 0), (0, 1)}
    for enlarged in (good | {(0, 0)}, good | {(1, 1)}):
        assert all({p[i] for p in good} == {p[i] for p in enlarged} for i in range(2))
        assert not all(sum(p) == 1 for p in enlarged)
    assert min(sum(p) for p in good) == 1
    assert sum(min(p[i] for p in good) for i in range(2)) == 0
    print(f"{comparisons} route-family/mask pairs; minimal blockers and deadline profiles matched "
          "direct enumeration; hidden-choice and joint-credit boundaries reproduced.")


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Run without Python optimization")
    check()

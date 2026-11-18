"""Design-time certificates for alternative opportunities within one joint window.

The caller supplies the finite routes and admissible denial envelopes. A member
can represent several source histories only if it bounds all their relevant
denials. A certificate identifies a proof witness, never an extra runtime read.
"""
from collections.abc import Hashable, Iterable
from dataclasses import dataclass
from typing import TypeVar

I = TypeVar("I", bound=Hashable)


class Blocked(ValueError):
    """This envelope intersects every sufficient route. Its physical reachability is separate."""

    def __init__(self, mask, hits):
        self.mask = mask
        self.hits = tuple(hits)
        super().__init__(f"All {len(self.hits)} routes are hit by {mask!r}")


def distinct_families(family: Iterable[Iterable[I]]) -> tuple[frozenset[I], ...]:
    return tuple(dict.fromkeys(frozenset(entry) for entry in family))


def certify(routes: Iterable[Iterable[I]], masks: Iterable[Iterable[I]]) -> dict[frozenset[I], frozenset[I]]:
    alternatives = distinct_families(routes)
    envelopes = distinct_families(masks)
    if not envelopes:
        raise ValueError("A positive source application needs an inhabited fault-window grade")
    witnesses = {}
    for mask in envelopes:
        for route in alternatives:
            if route.isdisjoint(mask):
                witnesses[mask] = route
                break
        else:
            raise Blocked(mask, [(route, next(iter(route & mask))) for route in alternatives])
    return witnesses


def minimal_blockers(routes: Iterable[Iterable[I]]) -> frozenset[frozenset[I]]:
    """All inclusion-minimal denials that meet every route, before restricting fault histories."""
    frontier = {frozenset()}
    for route in distinct_families(routes):
        candidates = set()
        for blocker in frontier:
            if blocker & route:
                candidates.add(blocker)
            else:
                candidates.update(blocker | {element} for element in route)
        frontier = {c for c in candidates if not any(b < c for b in candidates)}
    return frozenset(frontier)


@dataclass(frozen=True)
class RouteTime:
    route: frozenset
    commit_by: int


def deadline_profile(route_times: Iterable[RouteTime], masks: Iterable[Iterable[I]]):
    """Earliest guaranteed issue bound available from the supplied route certificates, by mask."""
    schedule = list(route_times)
    if any(type(spec.commit_by) is not int or spec.commit_by < 0 for spec in schedule):
        raise ValueError("Route times must be nonnegative integral ticks")
    schedule.sort(key=lambda spec: spec.commit_by)
    earliest = {}
    for spec in schedule:
        earliest.setdefault(frozenset(spec.route), spec.commit_by)
    choices = certify(earliest, masks)
    profile = {mask: RouteTime(route, earliest[route]) for mask, route in choices.items()}
    return max(spec.commit_by for spec in profile.values()), profile


@dataclass(frozen=True)
class WindowStep:
    before: Hashable
    after: Hashable
    denied: frozenset


def project_windows(initial_states, stages):
    """Project a finite, total layered source relation, retaining one witness per joint mask.

    Each stage(state) yields (next_state, directly denied opportunities) alternatives.
    Merging requires that the declared state and accumulated mask suffice for all
    remaining stages. A genuine early terminal may be encoded by an absorbing suffix.
    """
    paths = {(state, frozenset()): () for state in initial_states}
    if not paths:
        raise ValueError("Empty initial window")
    for index, stage in enumerate(stages):
        successors = {}
        for (before, prefix), path in paths.items():
            advanced = False
            for after, labels in stage(before):
                denied = frozenset(labels)
                key = after, prefix | denied
                if key not in successors:
                    successors[key] = path + (WindowStep(before, after, denied),)
                advanced = True
            if not advanced:
                raise ValueError(f"Unclassified terminal or stall at stage {index} in state {before!r}")
        paths = successors
    witnesses = {}
    for (_, mask), path in paths.items():
        witnesses.setdefault(mask, path)
    return witnesses

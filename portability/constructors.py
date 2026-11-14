"""Finite design-time constructors for the portability program.

These functions manipulate explicit finite certificates. Their mathematical
soundness and source-realization obligations are stated in CONSTRUCTORS.md.
They neither synthesize a complete controller nor certify the RP0-RP6 mission.
All arithmetic is exact; output size/work limits are explicit input capacities.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations
from typing import Hashable, Iterable, Mapping, Sequence

Q = Fraction


class CertificateFailure(ValueError):
    """A named sufficient-certificate failure, not source impossibility."""


def require(condition: bool, reason: str) -> None:
    if not condition:
        raise CertificateFailure(reason)


def exact(value: object, name: str) -> Q:
    require(type(value) in (int, Q), f"{name} must be an exact int or Fraction")
    return Q(value)


def natural(value: object, name: str, positive: bool = False) -> int:
    require(type(value) is int and value >= (1 if positive else 0), f"{name} must be a {'positive' if positive else 'nonnegative'} integer")
    return value


def projected_support(
    tokens: Iterable[Hashable],
    footprints: Mapping[Hashable, Mapping[Hashable, frozenset[Hashable]]],
    consumer: Hashable,
) -> frozenset[Hashable]:
    """Union actual token footprints; never quotient tokens by execution host."""
    result: set[Hashable] = set()
    for token in tokens:
        require(token in footprints, f"Unspecified incident token: {token!r}")
        require(consumer in footprints[token], f"Unspecified consumer projection: {consumer!r}")
        result.update(footprints[token][consumer])
    return frozenset(result)


def matrix_rank(rows: Sequence[Sequence[Q]], width: int) -> int:
    natural(width, "State width", positive=True)
    require(all(len(row) == width for row in rows), "Row dimension mismatch")
    a = [[exact(x, "Row coefficient") for x in row] for row in rows]
    rank = 0
    for col in range(width):
        pivot = next((r for r in range(rank, len(a)) if a[r][col]), None)
        if pivot is None:
            continue
        a[rank], a[pivot] = a[pivot], a[rank]
        value = a[rank][col]
        a[rank] = [x / value for x in a[rank]]
        for r in range(len(a)):
            if r != rank and a[r][col]:
                value = a[r][col]
                a[r] = [x - value*y for x, y in zip(a[r], a[rank])]
        rank += 1
        if rank == width:
            break
    return rank


@dataclass(frozen=True)
class BundleCertificate:
    rows: tuple[int, ...]
    width: int
    support_pairs_checked: int
    candidates_checked: int


def separating_bundle(
    rows: Sequence[Sequence[Q]],
    supports: Sequence[frozenset[int]],
    width: int,
    max_rows: int,
    max_candidates: int,
) -> BundleCertificate:
    """Find a bundle separating any two explanations in the supplied family.

    This is exact noiseless separation. No bounded-error precision, availability,
    code-execution, timing or dynamic truth claim is inferred from the result.
    """
    require(bool(supports), "Admitted support family must be nonempty")
    natural(max_candidates, "Search capacity", positive=True)
    natural(max_rows, "Row capacity", positive=True)
    natural(width, "State width", positive=True)
    require(all(len(row) == width for row in rows), "Row dimension mismatch")
    rows = tuple(tuple(exact(x, "Row coefficient") for x in row) for row in rows)
    for support in supports:
        for index in support:
            natural(index, "Support row index")
    universe = set(range(len(rows)))
    require(all(set(s) <= universe for s in supports), "Support names an absent row")
    pairs = tuple((a, b) for i, a in enumerate(supports) for b in supports[i:])
    tried = 0
    for size in range(1, min(max_rows, len(rows)) + 1):
        for selected in combinations(range(len(rows)), size):
            tried += 1
            require(tried <= max_candidates, "Bundle enumeration capacity exhausted")
            if all(matrix_rank([rows[i] for i in selected if i not in a | b], width) == width
                   for a, b in pairs):
                return BundleCertificate(selected, width, len(pairs), tried)
    raise CertificateFailure("No separating bundle within the declared row/search class")


@dataclass(frozen=True)
class PhaseEdge:
    source: str
    target: str
    elapsed: Q
    work: Q
    realization: str


@dataclass(frozen=True)
class PhaseCertificate:
    entry: str
    time_bound: Q
    work_bound: Q
    remaining_time: Mapping[str, Q]
    remaining_work: Mapping[str, Q]
    dependencies: tuple[str, ...]
    ranks: tuple[tuple[str, int], ...]
    terminal: frozenset[str]
    edges: tuple[PhaseEdge, ...]


def phase_budget(
    ranks: Mapping[str, int],
    terminal: frozenset[str],
    edges: Sequence[PhaseEdge],
    entry: str,
) -> PhaseCertificate:
    """Demonic longest-path bound on a finite strictly-ranked phase relation.

    Edges are source-realized bounded local phase steps, including all admitted
    failure/abort branches. Their completeness and elapsed/work bounds remain
    open realization obligations; this function does not verify their names.
    """
    require(entry in ranks, "Entry phase absent")
    require(bool(terminal) and terminal <= ranks.keys(), "Terminal phase absent")
    require(all(type(r) is int and r >= 0 for r in ranks.values()), "Invalid phase rank")
    outgoing: dict[str, list[PhaseEdge]] = {name: [] for name in ranks}
    for edge in edges:
        require(edge.source in ranks and edge.target in ranks, "Edge names absent phase")
        require(edge.source not in terminal, "Terminal has an outgoing edge")
        require(ranks[edge.target] < ranks[edge.source], "Nondecreasing phase rank")
        elapsed = exact(edge.elapsed, "Phase elapsed bound")
        debit = exact(edge.work, "Phase work bound")
        require(elapsed >= 0 and debit >= 0, "Negative phase cost")
        require(bool(edge.realization.strip()), "Missing local realization dependency")
        outgoing[edge.source].append(edge)
    require(all(name in terminal or outgoing[name] for name in ranks), "Unrepresented stalled nonterminal")
    time: dict[str, Q] = {}
    work: dict[str, Q] = {}
    for name in sorted(ranks, key=lambda q: ranks[q]):
        if name in terminal:
            time[name] = work[name] = Q(0)
        else:
            time[name] = max(Q(e.elapsed) + time[e.target] for e in outgoing[name])
            work[name] = max(Q(e.work) + work[e.target] for e in outgoing[name])
    return PhaseCertificate(entry, time[entry], work[entry], time, work,
                            tuple(sorted({e.realization for e in edges})),
                            tuple(sorted(ranks.items())), frozenset(terminal), tuple(edges))


def phase_family_budget(
    ranks: Mapping[str, int], terminal: frozenset[str], edges: Sequence[PhaseEdge],
    entries: Sequence[str],
) -> PhaseCertificate:
    """Bound every declared interrupted entry using a demonic zero-cost root.

    The root is an analytic branching device, not a runtime state choice.
    Source coverage of entries is a separate realization obligation.
    """
    require(bool(entries), "Empty phase entry family")
    require(all(entry in ranks for entry in entries), "Entry family names absent phase")
    require(all(type(r) is int and r >= 0 for r in ranks.values()), "Invalid phase rank")
    name = "__all_entries__"
    while name in ranks:
        name += "_"
    joined = dict(ranks)
    joined[name] = max(ranks.values()) + 1
    branches = tuple(PhaseEdge(name, entry, Q(0), Q(0), "source partial-state entry map")
                     for entry in dict.fromkeys(entries))
    return phase_budget(joined, terminal, (*edges, *branches), name)


def initial_debt_deadline(
    phases: PhaseCertificate, commissioning: Q, deadline: Q,
) -> Q:
    """Check debt present at time zero, without inventing a nonnegative release."""
    commissioning = exact(commissioning, "Initial-debt commissioning")
    deadline = exact(deadline, "Initial-debt deadline")
    require(commissioning >= 0 and deadline >= 0, "Negative initial-debt endpoint")
    expected = phase_budget(dict(phases.ranks), phases.terminal, phases.edges, phases.entry)
    require(len(dict(phases.ranks)) == len(phases.ranks), "Duplicate phase ranks")
    exact(phases.time_bound, "Phase time bound")
    exact(phases.work_bound, "Phase work bound")
    for value in (*phases.remaining_time.values(), *phases.remaining_work.values()):
        exact(value, "Remaining phase bound")
    require(expected == phases, "Phase certificate differs from its ranked graph")
    finish = commissioning + expected.time_bound
    require(finish < deadline, "Initial debt can age out before its constructed closure")
    return deadline - finish


@dataclass(frozen=True)
class WindowEnvelope:
    persistent: int
    occupied: int
    burst: Q
    rate: Q
    initial_debt: int = 0

    def bound(self, horizon: Q, consumer_window: Q) -> int:
        natural(self.persistent, "Persistent token count")
        natural(self.occupied, "Occupied token count")
        natural(self.initial_debt, "Initial debt count")
        burst = exact(self.burst, "Acquisition burst")
        rate = exact(self.rate, "Acquisition rate")
        horizon = exact(horizon, "Horizon")
        consumer_window = exact(consumer_window, "Consumer window")
        require(min(burst, rate, horizon, consumer_window) >= 0, "Negative raw interval parameter")
        acquisitions = burst + rate*(horizon + consumer_window)
        return self.persistent + self.occupied + acquisitions.numerator//acquisitions.denominator + self.initial_debt


@dataclass(frozen=True)
class HorizonCertificate:
    horizon: Q
    support_budget: int
    required_time: Q
    slack: Q


def check_horizon(
    envelope: WindowEnvelope,
    horizon: Q,
    commissioning: Q,
    phases: PhaseCertificate,
    retirement_tail: Q,
    tolerated_tokens: int,
) -> HorizonCertificate:
    commissioning = exact(commissioning, "Commissioning bound")
    retirement_tail = exact(retirement_tail, "Retirement tail")
    horizon = exact(horizon, "Horizon")
    natural(tolerated_tokens, "Tolerated token count")
    require(commissioning >= 0 and retirement_tail >= 0, "Negative entry/retirement bound")
    require(type(phases) is PhaseCertificate, "Invalid phase certificate type")
    require(len(dict(phases.ranks)) == len(phases.ranks), "Duplicate phase ranks")
    expected = phase_budget(dict(phases.ranks), phases.terminal, phases.edges, phases.entry)
    for name, value in phases.remaining_time.items():
        exact(value, "Remaining phase time")
    for name, value in phases.remaining_work.items():
        exact(value, "Remaining phase work")
    exact(phases.time_bound, "Phase time bound")
    exact(phases.work_bound, "Phase work bound")
    require(expected == phases, "Phase certificate differs from its ranked graph")
    required = commissioning + expected.time_bound + retirement_tail
    require(required < horizon, "No strict completion-before-age-out slack")
    count = envelope.bound(Q(horizon), Q(horizon))
    require(count <= tolerated_tokens, "Whole-attempt raw support exceeds realized phase budget")
    return HorizonCertificate(Q(horizon), count, required, Q(horizon) - required)


def reservoir_margin(capacity: Q, burst: Q, rate: Q, supply_rate: Q, deficit: Q) -> Q:
    """Margin for demand<=burst+rate*L and supply>=supply_rate*(L-deficit)^+."""
    capacity, burst, rate, supply_rate, deficit = (
        exact(value, name) for value, name in zip(
            (capacity, burst, rate, supply_rate, deficit),
            ("Stock capacity", "Demand burst", "Demand rate", "Supply rate", "Supply deficit")))
    require(min(capacity, burst, rate, supply_rate, deficit) >= 0, "Negative stock parameter")
    require(supply_rate >= rate, "Long-run supply cannot support the declared demand envelope")
    margin = capacity - burst - rate*deficit
    require(margin > 0, "No positive usable-reserve margin")
    return Q(margin)

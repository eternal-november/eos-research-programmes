"""Four source-bound voters and two independently keyed, durable output stores."""
from collections import Counter
from dataclasses import dataclass, field, replace
from itertools import combinations, product

from cover import Blocked, certify


VOTERS = tuple(range(4))
P, Q = range(2)
ROUTES = tuple(frozenset(route) for route in combinations(VOTERS, 3))
MASKS = (frozenset(), *(frozenset({voter}) for voter in VOTERS))
EPOCH = 17


def require(ok, message):
    if not ok:
        raise ValueError(message)


@dataclass
class Sink:
    side: int
    epoch: int
    seen: dict = field(default_factory=dict)
    closed: bool = False
    pending: tuple | None = None
    store: dict = field(default_factory=dict)
    insertions: int = 0
    work: int = 0
    strobed: bool = False

    def receive(self, port, key, yes):
        if self.closed or key != self.epoch or port not in VOTERS or port in self.seen:
            return False
        self.work += 1
        self.seen[port] = bool(yes)
        return True

    def close(self):
        if self.closed:
            return
        self.work += 1
        self.closed = True
        if sum(self.seen.values()) >= 3:
            # One durable, noncancelable descriptor in this sink's fixed-key slot.
            self.pending = (self.epoch, self.side)

    def persist(self):
        if not self.closed or self.strobed:
            return
        self.strobed = True
        self.work += 1  # The local strobe costs one even when no item is pending.
        if self.pending is None:
            return
        key, value = self.pending
        if key not in self.store:
            # The observable service is this insert; repeated calls leave it intact.
            self.store[key] = value
            self.insertions += 1
        self.pending = None


def modes(f, coherent):
    for bad in combinations(VOTERS, f):
        good = tuple(v for v in VOTERS if v not in bad)
        for signs in product((P, Q), repeat=len(good)):
            if coherent and len(set(signs)) != 1:
                continue
            for pairs in product(tuple(product((False, True), repeat=2)), repeat=f):
                bits = [(False, False)] * len(VOTERS)
                for v, sign in zip(good, signs):
                    bits[v] = sign == P, sign == Q
                for v, drives in zip(bad, pairs):
                    bits[v] = drives
                yield frozenset(bad), signs, tuple(bits)


def scheduled_captures(clock_profile, reverse_ties=False):
    arrivals = []
    for v, (sample, delay_p, delay_q) in enumerate(clock_profile):
        arrivals.extend(((sample + delay_p, v, P), (sample + delay_q, v, Q)))
    return sorted(arrivals, key=lambda e: (e[0], -e[1] if reverse_ties else e[1],
                                          -e[2] if reverse_ties else e[2]))


def assemble(bits, arrivals):
    sinks = (Sink(P, EPOCH), Sink(Q, EPOCH))
    charges = [1] * 4  # One capture/drive at each voter, then one launch per lead.
    for t, v, side in arrivals:
        charges[v] += 1
        require(2 <= t <= 4, "A correct capture left the promised window")
        require(sinks[side].receive(v, EPOCH, bits[v][side]), "A dedicated capture was lost")
    require(charges == [3] * 4, "The fixed voter cells cannot share a launch budget")
    for sink in sinks:
        sink.close()
    return sinks


def paid_strobes(closed, delays):
    # Fork the reached committed state, keeping private stores separate.
    sinks = tuple(replace(s, store=s.store.copy()) for s in closed)
    receipt = {}
    for tick in (6, 7):
        for sink in sinks:
            if tick == 5 + delays[sink.side]:
                sink.persist()
                if sink.insertions:
                    receipt[sink.side] = tick
    for sink in sinks:
        sink.persist()  # Retained descriptor has been consumed even if the caller retries.
        require(sink.work == 6, "Four captures, closing inspection and storage strobe must be paid locally")
        require(sink.pending is None and sink.insertions == int(sink.side in receipt),
                "An old strobe duplicated or deferred the actual insertion")
        require(sink.store == ({EPOCH: sink.side} if sink.side in receipt else {}),
                "Credit and local durable store differ")
    return receipt


def votes(bits):
    return tuple(int(sum(pair[side] for pair in bits) >= 3) for side in (P, Q))


def source_checks():
    # Each head has arbitrary error in [-1/4,1/4], after arbitrary drift in the same
    # interval. Affine monotonicity makes the interval endpoints sufficient.
    for initial_sign, drift, error in product((-1, 1), (-1, 1), (-1, 1)):
        measured_quarters = 4 * initial_sign + drift + error
        require(initial_sign * measured_quarters >= 2, "Head sign ambiguous in margin")

    certificates = certify(ROUTES, MASKS)
    for mask, route in certificates.items():
        require(route in ROUTES and not route & mask, "False surviving route")
    blockers = set()
    for pair in combinations(VOTERS, 2):
        denial = frozenset(pair)
        try:
            certify(ROUTES, (denial,))
        except Blocked as gap:
            require(gap.mask == denial and {r for r, _ in gap.hits} == set(ROUTES)
                    and all(i in r & denial for r, i in gap.hits), "Missing route witness")
            blockers.add(denial)
    require(len(blockers) == 6, "Missed a minimal denial")

    # Positive input traces exhaust the whole-window fixed faulty site and its
    # two independently driven leads. Each source clock profile is shared by the
    # sinks; their transport delays and local persistence strobes are independent.
    patterns = [case for f in (0, 1) for case in modes(f, True)]
    clocks = tuple(product((1, 2), repeat=3))
    counts = Counter()
    for phase in product(clocks, repeat=4):
        arrivals = scheduled_captures(phase)
        for bad, signs, bits in patterns:
            side = signs[0]
            covered = certificates[bad]
            sinks = assemble(bits, arrivals)
            require(all(sinks[side].seen[v] for v in covered), "Coverage failed at the real sink")
            winners = tuple(s.side for s in sinks if s.pending is not None)
            require(winners == (side,), "Wrong or nonexclusive durable commitment")
            require(all(not s.store for s in sinks), "Commit treated as immediate delivery")
            # Persistent requests after closure cannot reverse the winner.
            require(not sinks[1 - side].receive(0, EPOCH, True), "Closed aperture accepted a grant")
            for delays in product((1, 2), repeat=2):
                receipts = paid_strobes(sinks, delays)
                require(set(receipts) == {side}, "Wrong actual write after the funded strobe")
                counts[receipts[side], side] += 1
    require(sum(counts.values()) == 557056, "Missed a positive timing/command combination")

    def table(f):
        return Counter(votes(bits) for _, _, bits in modes(f, False))

    base = table(0) + table(1)
    enlarged = table(2)
    require(base[(1, 1)] == 0 and base[(0, 0)] == 54 and sum(base.values()) == 144,
            "Consistency was confused with progress")
    require(enlarged[(1, 1)] == 12 and sum(enlarged.values()) == 384,
            "Two-site consistency boundary lost")

    # Exercise the two boundary assignments through the actual local operations.
    fixed = scheduled_captures(((1, 1, 1),) * 4)
    split = ((True, False), (True, False), (False, True), (False, False))
    duplicate = ((True, True), (True, True), (True, False), (False, True))
    require(paid_strobes(assemble(split, fixed), (1, 1)) == {},
            "A split honest context unexpectedly certified a route")
    require(paid_strobes(assemble(duplicate, fixed), (1, 2)) == {P: 6, Q: 7},
            "Separate sinks failed to exhibit both opposing effects")
    enrolled = Sink(Q, EPOCH)
    require(enrolled.receive(0, EPOCH, False) and not enrolled.receive(0, EPOCH, True)
            and not enrolled.receive(4, EPOCH, True) and not enrolled.receive(1, EPOCH - 1, True),
            "Duplicate, foreign or stale slot should not change evidence")
    require(enrolled.seen == {0: False} and enrolled.work == 1, "Endpoint binding diverged")

    # Different orders at tied arrivals update disjoint source-owned slots.
    phase = ((1, 1, 2), (2, 2, 2), (1, 2, 2), (2, 1, 1))
    bits = ((False, True), (True, True), (False, True), (False, True))
    traces = [assemble(bits, scheduled_captures(phase, rev)) for rev in (False, True)]
    require(traces[0] == traces[1], "Independent simultaneous captures failed to commute")
    positive = traces[0][Q]
    require(positive.pending is not None and not positive.store, "Lost pre-write history")
    # Enlarge just the service clock: stutter through the deadline with pending intact.
    for _ in range(8):
        require(positive.pending is not None and not positive.store, "Stutter created output")
    positive.persist()
    require(positive.store == {EPOCH: Q}, "Eventual delayed insertion failed")
    # Recommission a distinct new key; even a syntactically affirmative old word is unusable.
    newer = Sink(Q, EPOCH + 1)
    require(all(not newer.receive(v, EPOCH, True) for v in VOTERS), "An old tag crossed epochs")
    newer.close()
    newer.persist()
    require(not newer.store, "Stale votes wrote a new output")
    # Fresh aperture state can reopen under a reused name. If the old actual
    # store survives, its keyed insertion still suppresses the second effect.
    remembered = Sink(Q, EPOCH, store=positive.store)
    for voter in (0, 2, 3):
        remembered.receive(voter, EPOCH, True)
    remembered.close()
    remembered.persist()
    require(remembered.insertions == 0 and positive.store == {EPOCH: Q},
            "Name reuse alone bypassed the retained durable entry")
    reused = Sink(Q, EPOCH)  # Reopen the name with the original key memory discarded.
    for v in (0, 2, 3):
        reused.receive(v, EPOCH, True)
    reused.close()
    reused.persist()
    require(positive.insertions + reused.insertions == 2, "Key reuse failed to admit old votes")
    return counts, base, enlarged


if __name__ == "__main__":
    counts, base, enlarged = source_checks()
    print("Positive endpoint/delay combinations:", dict(sorted(counts.items())))
    print("Arbitrary honest signs, up to one faulty ID:", dict(sorted(base.items())))
    print("Arbitrary honest signs, exactly two faulty IDs:", dict(sorted(enlarged.items())))

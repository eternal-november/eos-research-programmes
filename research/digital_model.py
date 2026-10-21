"""Operational signed broadcast, terminal evidence, and its epistemic event product.

No external packages. All nondeterministic choices are finite, explicitly enumerated
ideal-signature / synchronous-round choices. run_checks() returns a JSON-safe audit.
Prefix, initials(), successors(), local_view(), local_action(), and traces() are the
public adapter surface. Observer identities 3 and 4 have the sole action 'observe'.
Invalid, duplicate, late-raw, and other-epoch packets are rejected before this API;
their normalization is tested separately, not modeled as resource-free real networks.
"""
from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass
from itertools import combinations, product
import json

PARTICIPANTS = (0, 1, 2)
OBSERVERS = (3, 4)
ACTORS = PARTICIPANTS + OBSERVERS
FAULTS = (None, 0, 1, 2)
BITS = (0, 1)


def submasks(mask):
    return tuple(m for m in range(mask + 1) if m & mask == m)


def bit(value):
    return 1 << value


def choose(mask):
    return 1 if mask == 2 else 0


def token(signer, value):
    return 1 << (2 * signer + value)


def tokens(mask):
    return tuple((i, v) for i in PARTICIPANTS for v in BITS if mask & token(i, v))


def certificate(mask, value):
    return sum(bool(mask & token(i, value)) for i in PARTICIPANTS) >= 2


@dataclass(frozen=True)
class Event:
    kind: str
    data: tuple


@dataclass(frozen=True)
class Prefix:
    faulty: int | None
    input: int
    epoch: int = 0
    events: tuple[Event, ...] = ()

    @property
    def phase(self):
        return len(self.events)

    @property
    def raw(self):
        return self.events[0].data[1:] if self.phase >= 1 else (0, 0)

    @property
    def leader_signed(self):
        return self.events[0].data[0] if self.phase >= 1 else 0

    @property
    def echoes(self):
        return self.events[1].data if self.phase >= 2 else (0, 0)

    @property
    def decisions(self):
        if self.phase < 2:
            return (None, None, None)
        r1, r2 = self.raw
        e1, e2 = self.echoes
        proposed = (self.input, choose(r1 | e1), choose(r2 | e2))
        return tuple(None if i == self.faulty else proposed[i] for i in PARTICIPANTS)

    @property
    def terminal_signed(self):
        if self.phase < 3:
            return 0
        bad_mask = self.events[2].data[0]
        out = 0
        for i in PARTICIPANTS:
            vals = bad_mask if i == self.faulty else bit(self.decisions[i])
            for v in BITS:
                if vals & bit(v):
                    out |= token(i, v)
        return out

    @property
    def receipts(self):
        if self.phase < 3:
            return (0, 0)
        return self.events[-1].data[-2:]


def initials(epoch=0):
    for faulty in FAULTS:
        # A Byzantine leader's alleged private input has no validity consumer.
        for value in ((0,) if faulty == 0 else BITS):
            yield Prefix(faulty, value, epoch)


def round_clock(p):
    """(logical round, cutoff reached); phase 3 is inside round 3, phase 4 ends it."""
    return ((0, True), (1, True), (2, True), (3, False), (3, True))[p.phase]


def local_view(p, actor):
    """Permitted persistent input/receipt/own-action history; never the fault index."""
    view = [("epoch", p.epoch), ("input", p.input) if actor == 0 else ("input", None)]
    for phase, event in enumerate(p.events, 1):
        view.append(("clock", phase))
        if phase == 1:
            signed, r1, r2 = event.data
            if actor == 0:
                view.append(("signed-proposal", signed))
            elif actor in (1, 2):
                view.append(("raw", (r1, r2)[actor - 1]))
        elif phase == 2:
            if actor in (1, 2):
                own_echo = event.data[1 if actor == 1 else 0]
                view.extend((("sent-echo", own_echo), ("received-echo", event.data[actor - 1])))
            if actor in PARTICIPANTS and actor != p.faulty:
                view.append(("decision", p.decisions[actor]))
        elif phase == 3:
            if actor in PARTICIPANTS:
                own = tuple(v for i, v in tokens(p.terminal_signed) if i == actor)
                view.append(("signed-terminal", own))
            else:
                view.append(("terminal-receipts", event.data[actor - 2]))
        elif actor in OBSERVERS:
            view.append(("terminal-receipts", event.data[actor - 3]))
    return tuple(view)


def local_action(actor, view):
    """One fixed correct policy, computed solely from the supplied local view."""
    phase = max((entry[1] for entry in view if entry[0] == "clock"), default=0)
    fields = dict(view)
    if actor in OBSERVERS:
        return ("observe",)
    if phase == 0:
        return ("propose", bit(fields["input"])) if actor == 0 else ("wait",)
    if phase == 1:
        return ("echo", fields["raw"]) if actor != 0 else ("wait",)
    if phase == 2:
        return ("terminal", bit(fields["decision"])) if "decision" in fields else ("wait",)
    return ("retain",)


def successors(p):
    """All successors of one prefix, including static-fault choices and schedule choices.

    Phase 4 is a finished slot, intentionally terminal. Repetition uses a fresh epoch;
    the explicitly specified finite-run verdict is success after the phase-4 cutoff.
    """
    if p.phase == 0:
        proposals = range(4) if p.faulty == 0 else (local_action(0, local_view(p, 0))[1],)
        for signed in proposals:
            receipts = product(submasks(signed), repeat=2) if p.faulty == 0 else ((signed, signed),)
            for r1, r2 in receipts:
                yield Prefix(p.faulty, p.input, p.epoch, (Event("raw-cutoff", (signed, r1, r2)),))
    elif p.phase == 1:
        choices = []
        for source in (2, 1):
            choices.append(submasks(p.leader_signed) if source == p.faulty
                           else (local_action(source, local_view(p, source))[1],))
        for e1, e2 in product(*choices):
            yield Prefix(p.faulty, p.input, p.epoch, p.events + (Event("echo-cutoff", (e1, e2)),))
    elif p.phase == 2:
        for bad_mask in ((0,) if p.faulty is None else range(4)):
            provisional = Prefix(p.faulty, p.input, p.epoch, p.events + (Event("terminal-send", (bad_mask, 0, 0)),))
            for a, b in product(submasks(provisional.terminal_signed), repeat=2):
                yield Prefix(p.faulty, p.input, p.epoch, p.events + (Event("terminal-send", (bad_mask, a, b)),))
    elif p.phase == 3:
        honest = sum(token(i, p.decisions[i]) for i in PARTICIPANTS if i != p.faulty)
        old_a, old_b = p.receipts
        available = p.terminal_signed
        choices = []
        for old in (old_a, old_b):
            mandatory = honest | old
            optional = available & ~mandatory
            choices.append(tuple(mandatory | extra for extra in submasks(optional)))
        for a, b in product(*choices):
            yield Prefix(p.faulty, p.input, p.epoch, p.events + (Event("terminal-cutoff", (a, b)),))


def traces(phase=4, epoch=0):
    level = list(initials(epoch))
    for _ in range(phase):
        level = [nxt for p in level for nxt in successors(p)]
    return iter(level)


def event_label(before, after):
    """Enriched DEL event includes its actual per-actor observation vector.

    Its guard requires the underlying protocol event and this observation vector to
    be enabled at the source world. Including the vector is necessary: a decision
    computed after an echo depends on the old raw inbox as well as the echo payload.
    """
    assert after.events[:-1] == before.events and after.phase == before.phase + 1
    return after.events[-1], tuple(local_view(after, i)[len(local_view(before, i)):] for i in ACTORS)


def final_value(p):
    good = {d for d in p.decisions if d is not None}
    assert len(good) == 1
    return next(iter(good))


def accept_packet(epoch, phase, kind, signers, value, packet_epoch):
    """Scope/phase guard only; signature provenance is generated by successors()."""
    if epoch != packet_epoch or value not in BITS or len(set(signers)) != len(signers):
        return False
    if kind == "proposal":
        return phase == 1 and signers == (0,)
    if kind == "echo":
        return phase == 2 and len(signers) == 2 and signers[0] == 0 and signers[1] in (1, 2)
    return kind == "terminal" and phase in (3, 4) and len(signers) == 1 and signers[0] in PARTICIPANTS


def product_projection(p):
    """Independently accumulate event-model factual postconditions and local records.

    Preconditions are the operationally enabled source/event pairs. No actual event
    is publicly announced: every enabled alternative event remains in the product.
    This returns state/observations, not a strategic quotient of possible futures.
    """
    views = [[("epoch", p.epoch), ("input", p.input if i == 0 else None)] for i in ACTORS]
    raw = [0, 0]
    received_echo = [0, 0]
    decided = [None, None, None]
    signed_terminal = 0
    receipts = (0, 0)
    for t, event in enumerate(p.events, 1):
        for view in views:
            view.append(("clock", t))
        if event.kind == "raw-cutoff":
            signed, raw[0], raw[1] = event.data
            views[0].append(("signed-proposal", signed))
            for i in (1, 2):
                views[i].append(("raw", raw[i - 1]))
        elif event.kind == "echo-cutoff":
            received_echo[:] = event.data
            for i in (1, 2):
                views[i].extend((("sent-echo", received_echo[2 - i]), ("received-echo", received_echo[i - 1])))
            for i in PARTICIPANTS:
                if i == p.faulty:
                    continue
                values = {v for v in BITS if (raw[i - 1] | received_echo[i - 1]) & bit(v)} if i else {p.input}
                decided[i] = next(iter(values)) if len(values) == 1 else 0
                views[i].append(("decision", decided[i]))
        elif event.kind == "terminal-send":
            bad_mask, a, b = event.data
            for i in PARTICIPANTS:
                values = tuple(v for v in BITS if bad_mask & bit(v)) if i == p.faulty else (decided[i],)
                views[i].append(("signed-terminal", values))
                for value in values:
                    signed_terminal |= token(i, value)
            receipts = (a, b)
            for i, received in zip(OBSERVERS, receipts):
                views[i].append(("terminal-receipts", received))
        else:
            receipts = event.data
            for i, received in zip(OBSERVERS, receipts):
                views[i].append(("terminal-receipts", received))
    return tuple(decided), signed_terminal, receipts, tuple(map(tuple, views))


def knowledge_tables(points, actors=ACTORS):
    values = {i: defaultdict(set) for i in actors}
    faults = {i: defaultdict(set) for i in actors}
    for p in points:
        value = final_value(p)
        for i in actors:
            if i in PARTICIPANTS and i == p.faulty:
                continue  # K_i is evaluated in the system conditioned on i correct.
            view = local_view(p, i)
            values[i][view].add(value)
            faults[i][view].add(p.faulty)
    return values, faults


def legal_round_tuple(fault, value, raw1, raw2, echo1, echo2):
    """Independent finite transcription of Digital.lean's Legal relation."""
    return ((fault == 0 or raw1 == raw2 == bit(value))
            and (fault == 1 or echo2 == raw1)
            and (fault == 2 or echo1 == raw2)
            and (fault != 1 or echo2 & ~bit(value) == 0)
            and (fault != 2 or echo1 & ~bit(value) == 0))


def run_checks():
    levels = [list(initials())]
    product_checked = 0
    for phase in range(4):
        next_level = []
        new_to_product = {i: {} for i in ACTORS}
        product_to_new = {i: {} for i in ACTORS}
        for p in levels[-1]:
            extension = list(successors(p))
            assert extension, ("premature deadlock", p)
            for nxt in extension:
                _, observation = event_label(p, nxt)
                for i in ACTORS:
                    old_view, new_view = local_view(p, i), local_view(nxt, i)
                    relation_key = (old_view, observation[i])
                    assert new_view not in new_to_product[i] or new_to_product[i][new_view] == relation_key
                    assert relation_key not in product_to_new[i] or product_to_new[i][relation_key] == new_view
                    new_to_product[i][new_view] = relation_key
                    product_to_new[i][relation_key] = new_view
            next_level.extend(extension)
        levels.append(next_level)
    counts = [len(level) for level in levels]
    projected = {(p.faulty, p.input, *p.raw, *p.echoes) for p in levels[2]}
    legal = {(fault, value, r1, r2, e1, e2) for fault in FAULTS
             for value in ((0,) if fault == 0 else BITS)
             for r1, r2, e1, e2 in product(range(4), repeat=4)
             if legal_round_tuple(fault, value, r1, r2, e1, e2)}
    assert projected == legal
    assert all(not tuple(successors(p)) for p in levels[4])
    action_classes = {}
    for level in levels:
        assert len(level) == len(set(level))
        for p in level:
            decisions, signed, received, views = product_projection(p)
            assert decisions == p.decisions and signed == p.terminal_signed and received == p.receipts
            for i in ACTORS:
                assert views[i] == local_view(p, i)
                if i != p.faulty:
                    key = (i, views[i])
                    action = local_action(i, views[i])
                    assert key not in action_classes or action_classes[key] == action
                    action_classes[key] = action
            product_checked += 1
            if p.phase >= 2:
                value = final_value(p)
                if p.faulty != 0:
                    assert value == p.input
            if p.phase >= 3:
                for bundle in p.receipts:
                    assert bundle & ~p.terminal_signed == 0
                    for v in BITS:
                        if certificate(bundle, v):
                            assert final_value(p) == v
                for i in PARTICIPANTS:
                    if i != p.faulty:
                        assert token(i, p.decisions[i]) & p.terminal_signed
                        before_send = Prefix(p.faulty, p.input, p.epoch, p.events[:2])
                        assert local_action(i, local_view(before_send, i)) == ("terminal", bit(p.decisions[i]))
            if p.phase == 4:
                assert all(certificate(bundle, final_value(p)) for bundle in p.receipts)

    early_values, early_faults = knowledge_tables(levels[3])
    for p in levels[3]:
        for idx, i in enumerate(OBSERVERS):
            for v in BITS:
                if certificate(p.receipts[idx], v):
                    assert early_values[i][local_view(p, i)] == {v}
    terminal_values, _ = knowledge_tables(levels[4])
    assert all(len(v) == 1 for i in OBSERVERS for v in terminal_values[i].values())

    # Higher order: certificate holder knows at least two correct participants know
    # the decided value, but cannot in general name a pair known to be correct.
    for p in levels[3]:
        for i in PARTICIPANTS:
            if i != p.faulty:
                assert early_values[i][local_view(p, i)] == {final_value(p)}
    unidentified = next(p for p in levels[3] if certificate(p.receipts[0], 0)
                        and early_faults[3][local_view(p, 3)] >= {0, 1, 2})
    assert all(any(bad in pair for bad in early_faults[3][local_view(unidentified, 3)])
               for pair in combinations(PARTICIPANTS, 2))
    selective = next(p for p in levels[3] if certificate(p.receipts[0], 0)
                     and p.receipts[1] == 0 and early_values[4][local_view(p, 4)] == {0, 1})
    # This world itself refutes K_A K_B Final(0), while A knows Final(0).
    assert early_values[3][local_view(selective, 3)] == {0}
    single = next(p for p in levels[3] if p.receipts[0] == token(0, 1)
                  and final_value(p) == 0 and early_values[3][local_view(p, 3)] == {0, 1})
    existence_without_possession = next(p for p in levels[3] if p.receipts == (0, 0))
    assert certificate(existence_without_possession.terminal_signed, final_value(existence_without_possession))
    assert early_values[3][local_view(existence_without_possession, 3)] == {0, 1}
    # A truthful announcement of the single signed payload 1 deletes this actual
    # operational world. Pure valuation inheritance likewise misses new possession.
    assert final_value(single) != 1
    before_cert = Prefix(selective.faulty, selective.input, selective.epoch, selective.events[:2])
    assert not certificate(before_cert.receipts[0], 0) and certificate(selective.receipts[0], 0)

    # Negative evidence is about historical honest receipts, not hidden signing.
    negative_classes = defaultdict(set)
    for p in levels[2]:
        for i in (1, 2):
            if i != p.faulty:
                historical = any(p.raw[j - 1] & bit(1) for j in (1, 2) if j != p.faulty)
                negative_classes[(i, local_view(p, i))].add(historical)
                if not (p.raw[i - 1] | p.echoes[i - 1]) & bit(1):
                    assert not historical
    assert all(values == {False} for (i, view), values in negative_classes.items()
               if not (dict(view)["raw"] | dict(view)["received-echo"]) & bit(1))
    premature = next(p for p in levels[1] if p.faulty == 0 and p.raw == (0, bit(1)))
    assert not premature.raw[0] & bit(1) and premature.raw[1] & bit(1)
    hidden_sign = next(p for p in levels[2] if p.faulty == 0 and p.raw == (0, 0)
                       and p.leader_signed & bit(1))
    assert hidden_sign.echoes == (0, 0)
    early_conflict = next(p for p in levels[2] if p.faulty == 0 and p.raw == (bit(0), bit(1)))
    assert early_conflict.echoes == (bit(1), bit(0)) and final_value(early_conflict) == 0

    # Epoch/phase/identity validation is a meaningful premise, exercised independently.
    for epoch in (0, 1):
        for value in BITS:
            assert accept_packet(epoch, 1, "proposal", (0,), value, epoch)
            assert not accept_packet(epoch, 2, "proposal", (0,), value, epoch)
            assert not accept_packet(epoch, 3, "terminal", (1, 1), value, epoch)
            assert not accept_packet(epoch, 3, "terminal", (1,), value, 1 - epoch)
    # Accepting late raw values can split two honest followers after an empty first round.
    assert choose(bit(1)) != choose(0)
    # Dropping the complete-echo premise also invalidates negative evidence/agreement.
    dropped_raw, dropped_echo = (0, bit(1)), (0, 0)
    assert tuple(choose(r | e) for r, e in zip(dropped_raw, dropped_echo)) == (0, 1)

    # Every pair of legal completed slots with the SAME faulty identity composes.
    pairs = 0
    for p, q in product(levels[2], repeat=2):
        if p.faulty != q.faulty:
            continue
        logs = [tuple((p.decisions[i], q.decisions[i])) for i in PARTICIPANTS if i != p.faulty]
        assert len(set(logs)) == 1
        assert all(log[:1] == (final_value(p),) for log in logs)
        pairs += 1
    old, newer = (next(p for p in levels[2] if p.faulty is None and final_value(p) == v) for v in BITS)
    assert (old.decisions[1], newer.decisions[1]) == (0, 1)
    return {
        "identities": 3, "max_static_faults": 1, "read_only_verifiers": 2,
        "prefixes_by_phase": counts, "event_product_points_checked": product_checked,
        "formal_round_projection_cases": len(projected),
        "correct_local_action_classes": len(action_classes), "compatible_two_slot_pairs": pairs,
        "decision_round": 2, "public_certificate_cutoff": 3,
        "operational_phases": "initial, raw cutoff, echo/decision cutoff, selective terminal delivery, terminal cutoff",
        "certificate_soundness_and_availability": True,
        "receipt_universal_warrant": True, "negative_evidence_checked": True,
        "cutoff_common_knowledge_basis": "each observer accessibility class preserves final value; hence every finite observer chain does",
        "truthful_announcement_and_pure_valuation_counterexamples": True,
        "single_terminal_claim_witness": {"fault": single.faulty, "signed_claim": 1, "actual_final": 0},
        "certificate_existence_not_possession": True,
        "historical_not_latest_witness": {"slot_0_certificate": 0, "two_slot_log": [0, 1], "latest": 1},
        "higher_order_unknown_correct_pair": {"possible_faults": sorted(x for x in early_faults[3][local_view(unidentified, 3)] if x is not None), "certificate": list(tokens(unidentified.receipts[0]))},
        "selective_delivery_witness": {"fault": selective.faulty, "certificate_A": list(tokens(selective.receipts[0])), "received_B": [], "B_possible_decisions": [0, 1]},
        "negative_premature_witness": {"first_round_received": list(premature.raw), "observer": 1},
        "negative_hidden_signing_witness": {"leader_signed_mask": hidden_sign.leader_signed, "honest_first_receipts": [0, 0]},
        "missing_echo_witness": {"raw": list(dropped_raw), "echoes": list(dropped_echo), "incorrect_decisions": [0, 1]},
        "early_nonfinal_echo_witness": {"first_receipts": list(early_conflict.raw), "echoes": list(early_conflict.echoes), "decision": 0},
        "boundaries": ["ideal phase/epoch-bound signatures", "timely correct messages and common rounds", "fixed faults", "finite binary values", "no HotStuff locks", "no physical truth or effect inference"],
    }


if __name__ == "__main__":
    print(json.dumps(run_checks(), indent=2, sort_keys=True))

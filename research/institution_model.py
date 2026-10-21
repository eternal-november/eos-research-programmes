"""Operational institution/recovery instance. Standard library, no file writes.

Authentication is an ideal event-authentication oracle, not cryptography. See
INSTITUTION.md for trust boundaries, global fault family, and core-adapter obligations.
"""
from __future__ import annotations

from dataclasses import dataclass, replace, asdict
from itertools import product, permutations
from typing import Iterable
import json


SAFE = range(2, 9)
CONTROLS = (0, 1, 2)
MODES = {"live": (2, 1), "isolated": (2, 0), "repair": (1, 0), "ready": (2, 0)}
OFFICER = 12


@dataclass(frozen=True)
class Config:
    era: int
    sensors: tuple[int, int, int]
    authorizers: tuple[int, int, int]

    @property
    def digest(self) -> tuple:
        return (self.era, self.sensors, self.authorizers)


CONFIGS = (Config(0, (0, 1, 2), (3, 4, 5)), Config(1, (6, 7, 8), (9, 10, 11)))
ACTORS = frozenset(range(12))


def admissible_faults(faults: frozenset[int], configs: Iterable[Config] = CONFIGS) -> bool:
    """One global static coalition, projected to each selected role configuration."""
    configs = tuple(configs)
    return (faults <= ACTORS
            and all(len(set(role)) == 3 and set(role) <= ACTORS and len(faults.intersection(role)) <= 1
                    for c in configs for role in (c.sensors, c.authorizers)))


def configuration_allowed(candidate: Config) -> bool:
    """Public admission proof over ALL joint hypotheses, never the actual hidden B."""
    return all(admissible_faults(faults, (candidate,)) for faults in finite_fault_family())


@dataclass(frozen=True)
class Signature:
    signer: int
    era: int
    kind: str
    payload: tuple


class Authentication:
    """Oracle witnesses actual signing events; arbitrary fabricated bytes fail.

    A caller representing an honest actor uses only the explicit policy below.
    The adversary's signing interface is limited to the fixed coalition or explicitly
    leaked old-era keys. This oracle does not certify physical truth or human intent.
    """
    def __init__(self, faults: frozenset[int], old_leaks: frozenset[tuple[int, int]] = frozenset()):
        self.faults = faults
        self.old_leaks = old_leaks
        self.events: set[Signature] = set()

    def emit(self, signer: int, era: int, kind: str, payload: tuple) -> Signature:
        event = Signature(signer, era, kind, payload)
        self.events.add(event)
        return event

    def adversary_emit(self, signer: int, era: int, kind: str, payload: tuple) -> Signature:
        if signer not in self.faults and (signer, era) not in self.old_leaks:
            raise ValueError("adversary lacks this signing capability")
        return self.emit(signer, era, kind, payload)

    def verify(self, artifact: Signature) -> bool:
        return artifact in self.events


@dataclass(frozen=True)
class Institution:
    status: str = "active"
    norm_cap: int = 2
    generation: int = 0
    office: tuple[int, ...] = (OFFICER,)

    @property
    def digest(self) -> tuple:
        return (self.status, self.norm_cap, self.generation, self.office)


@dataclass(frozen=True)
class State:
    x: int
    faults: frozenset[int]
    config: Config = CONFIGS[0]
    institution: Institution = Institution()
    mode: str = "live"
    epoch: int = 0
    delivered: int = 0
    breached: bool = False
    conduct_breach: bool = False
    clean: bool = False


@dataclass(frozen=True)
class GateView:
    config: Config
    institution: Institution
    mode: str
    epoch: int


def gate_observation(state: State) -> GateView:
    """No inventory or faulty identity is revealed to the gate."""
    return GateView(state.config, state.institution, state.mode, state.epoch)


def envelope(median: int) -> tuple[int, ...]:
    return tuple(x for x in SAFE if abs(x - median) <= 1)


def certified(median: int, control: int) -> bool:
    states = envelope(median)
    return bool(states) and control in CONTROLS and all(
        z + control - 1 + b in SAFE for z in states for b in (-1, 0, 1))


def authorizer_policy(view: GateView, received: tuple[Signature, ...], auth: Authentication) -> tuple[int, ...]:
    """Only local messages/current public configuration, never x or B."""
    entries = []
    for sensor in view.config.sensors:
        values = [m.payload[-1] for m in received if auth.verify(m) and m.kind == "report"
                  and len(m.payload) == 5 and isinstance(m.payload[-1], int)
                  and m.signer == sensor and m.era == view.config.era
                  and m.payload[:3] == (view.config.digest, view.epoch, view.epoch)]
        # Collection occurs at the synchronous cutoff; honest messages are present.
        entries.append(min(values) if values else 0)
    median = sorted(entries)[1]
    return tuple(u for u in CONTROLS if u <= view.institution.norm_cap and certified(median, u))


def report_round(state: State, auth: Authentication, readings: dict[int, int],
                 hostile_reports: dict[tuple[int, int], int | None]) -> dict[int, tuple[Signature, ...]]:
    """Environment samples once per correct sensor, then routes actual signed events."""
    received = {}
    for recipient in state.config.authorizers:
        messages = []
        for sensor in state.config.sensors:
            if sensor in state.faults:
                value = hostile_reports.get((sensor, recipient))
                if value is None:
                    continue
                issue = auth.adversary_emit
            else:
                value = readings[sensor]
                if abs(value - state.x) > 1:
                    raise ValueError("incorrect measurement environment")
                issue = auth.emit
            payload = (state.config.digest, state.epoch, state.epoch, recipient, value)
            messages.append(issue(sensor, state.config.era, "report", payload))
        received[recipient] = tuple(messages)
    return received


def endorsement_round(state: State, auth: Authentication, received: dict[int, tuple[Signature, ...]],
                      hostile_choices: dict[int, tuple[int, ...]]) -> tuple[Signature, ...]:
    view = gate_observation(state)
    messages = []
    for actor in state.config.authorizers:
        if actor in state.faults:
            controls = hostile_choices.get(actor, ())
            issue = auth.adversary_emit
        else:
            controls = authorizer_policy(view, received[actor], auth)
            issue = auth.emit
        for u in controls:
            payload = (view.config.digest, view.epoch, view.institution.digest, u)
            messages.append(issue(actor, view.config.era, "endorse", payload))
    return tuple(messages)


def verify_current(view: GateView, auth: Authentication, u: int, artifact: tuple[Signature, ...]) -> bool:
    """Public acceptance: signature/support/scope checks, not an oracle for safety."""
    payload = (view.config.digest, view.epoch, view.institution.digest, u)
    return (u in CONTROLS and len(artifact) >= 2
            and len({s.signer for s in artifact}) == len(artifact)
            and all(auth.verify(s) and s.kind == "endorse" and s.era == view.config.era
                    and s.signer in view.config.authorizers and s.payload == payload for s in artifact))


def assemble(view: GateView, auth: Authentication, messages: tuple[Signature, ...]) -> tuple[int, tuple[Signature, ...]] | None:
    for u in CONTROLS:
        payload = (view.config.digest, view.epoch, view.institution.digest, u)
        # Authenticate and validate every share before its claimed identity can
        # occupy a support slot. Otherwise an invalid/replayed packet could replace
        # a genuine honest share or poison an otherwise valid candidate certificate.
        shares = tuple(s for s in messages if auth.verify(s) and s.kind == "endorse"
                       and s.era == view.config.era and s.signer in view.config.authorizers
                       and s.payload == payload)
        # Only valid shares reach deduplication; repeated packets add no support.
        shares = tuple({s.signer: s for s in shares}.values())
        if verify_current(view, auth, u, shares):
            return u, shares
    return None


@dataclass(frozen=True)
class EpochRecord:
    before: int
    after: int
    epoch: int
    mode: str
    era: int
    action: int
    bypass: int
    service: int
    certificate: tuple[Signature, ...]


def control_epoch(state: State, auth: Authentication, readings: dict[int, int],
                  hostile_reports: dict[tuple[int, int], int | None],
                  hostile_choices: dict[int, tuple[int, ...]], bypass: int) -> tuple[State, EpochRecord]:
    if not admissible_faults(state.faults):
        raise ValueError("coalition violates the joint family")
    cap, radius = MODES[state.mode]
    if abs(bypass) > radius:
        raise ValueError("hostile flow exceeds current physical capability")
    view = gate_observation(state)
    certificate = ()
    if state.mode == "live":
        received = report_round(state, auth, readings, hostile_reports)
        messages = endorsement_round(state, auth, received, hostile_choices)
        result = assemble(view, auth, messages)
        if result is None:
            raise ValueError("no current authorized action; mission cannot be certified")
        u, certificate = result
    else:
        u = 1  # Observed physical isolation makes constant replenishment sufficient.
    if u > cap or u > state.institution.norm_cap:
        raise ValueError("technical or normative capacity insufficient")
    following = state.x + u - 1 + bypass
    record = EpochRecord(state.x, following, state.epoch, state.mode, state.config.era, u, bypass, 1, certificate)
    # Delivery and the decrement share one transition contract; a receipt alone is insufficient.
    after = replace(state, x=following, epoch=state.epoch + 1, delivered=state.delivered + 1,
                    breached=state.breached or record.service < 1)
    return after, record


def recognize(n: Institution, order: str) -> Institution:
    """Constitutive update after a powered registration, independently of permission."""
    if order == "grantTwo":
        return replace(n, norm_cap=2)
    statuses = {"suspend": "suspended", "beginRepair": "repairing", "finishRepair": "ready", "reinstate": "active"}
    if order == "isolate":
        return n
    return replace(n, status=statuses[order], generation=n.generation + (order == "reinstate"))


def order_permitted(state: State, order: str, clean: bool = False, consent: bool = False) -> bool:
    n, mode = state.institution, state.mode
    return {"suspend": n.status == "active", "isolate": n.status == "suspended" and mode == "live",
            "beginRepair": n.status == "suspended" and mode == "isolated",
            "finishRepair": n.status == "repairing" and mode == "repair" and clean,
            "reinstate": n.status == "ready" and mode == "ready" and state.clean,
            "grantTwo": consent}[order]


def order_credential(state: State, auth: Authentication, order: str, actor: int = OFFICER) -> Signature:
    return auth.emit(actor, state.config.era, "order", (state.institution.digest, state.epoch, order))


def has_power(state: State, auth: Authentication, credential: Signature, order: str) -> bool:
    return (auth.verify(credential) and credential.signer in state.institution.office
            and credential.kind == "order" and credential.era == state.config.era
            and credential.payload == (state.institution.digest, state.epoch, order))


def register_order(state: State, auth: Authentication, credential: Signature, order: str,
                   *, clean: bool = False, consent: bool = False) -> State:
    """Institutional validity is independent of whether conduct was permitted.

    This wider semantic transition includes an office-holder's unlawful exercise.
    The enforced implementation below calls it only after checking permission.
    Registration changes no physical mode or installed configuration.
    """
    if not has_power(state, auth, credential, order):
        return state
    return replace(state, institution=recognize(state.institution, order),
                   conduct_breach=state.conduct_breach or not order_permitted(state, order, clean, consent))


def administrative_step(state: State, auth: Authentication, credential: Signature, order: str,
                        *, clean: bool = False, consent: bool = False, access: bool = True,
                        replacement: Config | None = None) -> State:
    """Enforced path: authentic/powered/permitted/accessible are distinct checks.

    The isolation and repair effects are trusted physical contracts, not inferred
    from the officer's signature. Failure of effective access leaves the state unchanged.
    """
    if not has_power(state, auth, credential, order) or not order_permitted(state, order, clean, consent) or not access:
        return state
    registered = register_order(state, auth, credential, order, clean=clean, consent=consent)
    n = registered.institution
    if order == "reinstate":
        if replacement is None or replacement.era <= state.config.era or not configuration_allowed(replacement):
            return state
        return replace(state, institution=n, mode="live", config=replacement, clean=False)
    mode = {"isolate": "isolated", "beginRepair": "repair", "finishRepair": "ready"}.get(order, state.mode)
    return replace(state, institution=n, mode=mode, clean=clean if order == "finishRepair" else state.clean)


@dataclass(frozen=True)
class Duty:
    bearer: str = "gate_operator"
    beneficiary: str = "service_recipient"
    trigger: str = "start"
    deadline: str = "end"
    required_units: int = 1
    exception_epochs: tuple[int, ...] = ()


UNIT_DUTY = Duty()


def duty_breach(history: Iterable[dict], duty: Duty = UNIT_DUTY) -> bool:
    """Declarative history query: a triggered duty misses its first matching deadline.

    Exceptions are part of the recognized duty, never an untrusted event flag.
    The selected recovery duty has no exceptions. Pending starts are not yet breaches.
    """
    history = tuple(history)
    for start, event in enumerate(history):
        if event["kind"] != duty.trigger:
            continue
        epoch = event.get("epoch", 0)
        ends = [e for e in history[start+1:] if e["kind"] == duty.deadline and e.get("epoch", 0) == epoch]
        if ends and epoch not in duty.exception_epochs and ends[0]["service"] < duty.required_units:
            return True
    return False


def breach_monitor(events: Iterable[dict], duty: Duty = UNIT_DUTY) -> list[bool]:
    answer, breached, pending = [False], False, set()
    for event in events:
        epoch = event.get("epoch", 0)
        if event["kind"] == duty.trigger:
            pending.add(epoch)
        elif event["kind"] == duty.deadline and epoch in pending:
            pending.remove(epoch)
            breached = breached or (epoch not in duty.exception_epochs and event["service"] < duty.required_units)
        answer.append(breached)
    return answer


def verify_equivocation(auth: Authentication, first: Signature, second: Signature) -> bool:
    """Historical event evidence; neither current eligibility nor physical truth."""
    return (auth.verify(first) and auth.verify(second) and first.kind == second.kind == "report"
            and len(first.payload) == len(second.payload) == 5
            and isinstance(first.payload[-1], int) and isinstance(second.payload[-1], int)
            and first.signer == second.signer and first.era == second.era
            and first.payload[:3] == second.payload[:3] and first.payload[-1] != second.payload[-1])


@dataclass(frozen=True)
class CapabilityState:
    capacity: int


@dataclass(frozen=True)
class CapabilityEvent:
    command: int
    output: int
    capacity_before: int
    capacity_after: int
    hostile: int


def capability_step(state: CapabilityState, command: int, next_capacity: int, hostile: int = 0) -> tuple[CapabilityState, CapabilityEvent]:
    """Finite diagnostic plant: output=min(command,capacity)+hostile.

    The environment may disable capacity after the effect. The outside observer
    sees only output; it sees neither the private command nor subsequent damage.
    """
    if state.capacity not in (0, 1) or command not in (0, 1) or next_capacity not in (0, state.capacity) or hostile not in (-1, 0):
        raise ValueError("outside diagnostic capability model")
    event = CapabilityEvent(command, min(command, state.capacity) + hostile, state.capacity, next_capacity, hostile)
    return CapabilityState(next_capacity), event


def capability_observation(event: CapabilityEvent) -> int:
    return event.output


def maximal_verdict(state: State, pending_epoch: bool) -> dict[str, bool]:
    """A maximal deadlock during an owed epoch fails service; prefixes are not maximal."""
    return {"safe": state.x in SAFE, "service": not pending_epoch and not state.breached}


def finite_fault_family() -> tuple[frozenset[int], ...]:
    options = [[None, *role] for c in CONFIGS for role in (c.sensors, c.authorizers)]
    return tuple(frozenset(i for i in row if i is not None) for row in product(*options))


def run_checks() -> dict:
    # Independent interval specification checks the general formula on a bounded grid.
    capacity_checks = 0
    for width, demand, cap, radius in product(range(7), range(4), range(5), range(4)):
        actual = all(any(all(0 <= x + u - demand + b <= width for b in range(-radius, radius+1))
                         for u in range(cap+1)) for x in range(width+1))
        expected = cap >= demand + radius and demand >= radius and width >= 2*radius
        assert actual == expected
        capacity_checks += 1

    # Exhaust local median/support classes: independently calculate every resulting effect.
    local_checks = 0
    for x, medians, bad, subset in product(SAFE, product(range(-1, 2), repeat=3), range(3), range(8)):
        medians = tuple(x + v for v in medians)
        supported = {u: [i for i in range(3) if (bool(subset & (1 << u)) if i == bad else certified(medians[i], u))] for u in CONTROLS}
        winners = [u for u, support in supported.items() if len(support) >= 2]
        assert winners
        for u in winners:
            assert all(x + u - 1 + b in SAFE for b in (-1, 0, 1))
        local_checks += 1

    # Each full trace keeps ONE B across both configurations and all modes.
    trace_count, epochs = 0, 0
    specimen = None
    for faults, initial in product(finite_fault_family(), SAFE):
        assert admissible_faults(faults)
        auth = Authentication(faults)
        state = State(initial, faults)
        records = []
        for order in (None, "suspend", "isolate", "beginRepair", None, "finishRepair", "reinstate", None):
            if order:
                credential = order_credential(state, auth, order)
                state = administrative_step(state, auth, credential, order, clean=True, replacement=CONFIGS[1])
            readings = {s: state.x + (-1 if s % 2 else 1) for s in state.config.sensors if s not in faults}
            hostile = {(s, a): state.x + (-3 if a % 2 else 3) for s in state.config.sensors if s in faults for a in state.config.authorizers}
            choices = {a: (0, 1, 2) for a in state.config.authorizers if a in faults}
            bypass = (-1 if state.epoch % 2 else 1) if state.mode == "live" else 0
            state, record = control_epoch(state, auth, readings, hostile, choices, bypass)
            assert state.x in SAFE and record.service == 1 and state.faults == faults
            records.append(record)
            epochs += 1
        assert state.config == CONFIGS[1] and state.institution.status == "active" and state.delivered == len(records)
        trace_count += 1
        if specimen is None and faults == frozenset({2, 5, 8, 11}) and initial == 2:
            specimen = [{k: v for k, v in asdict(r).items() if k != "certificate"} for r in records]
    assert all(configuration_allowed(c) for c in CONFIGS)
    # Two faulty hypotheses from separate original sensor roles can coincide here.
    assert not configuration_allowed(Config(2, (0, 6, 7), (3, 4, 5)))
    assert not configuration_allowed(Config(2, (0, 0, 1), (3, 4, 5)))

    # Normative impossibility and actual recognized update restoring service.
    auth = Authentication(frozenset())
    restricted = State(2, frozenset(), institution=Institution(norm_cap=1))
    assert not any(2 + u - 1 - 1 in SAFE for u in (0, 1))
    order = order_credential(restricted, auth, "grantTwo")
    assert has_power(restricted, auth, order, "grantTwo") and not order_permitted(restricted, "grantTwo")
    forbidden_registration = register_order(restricted, auth, order, "grantTwo")
    assert forbidden_registration.institution.norm_cap == 2 and forbidden_registration.conduct_breach
    assert forbidden_registration.mode == restricted.mode and forbidden_registration.x == restricted.x
    assert administrative_step(restricted, auth, order, "grantTwo") == restricted  # enforcer supplies prevention
    granted = administrative_step(restricted, auth, order, "grantTwo", consent=True)
    delivered, _ = control_epoch(granted, auth, {s: 2 for s in granted.config.sensors}, {}, {}, -1)
    assert delivered.x == 2 and delivered.delivered == 1
    ordinary = order_credential(restricted, auth, "grantTwo", actor=20)
    assert auth.verify(ordinary) and not has_power(restricted, auth, ordinary, "grantTwo")
    assert administrative_step(restricted, auth, order, "grantTwo", consent=True, access=False) == restricted

    # Suspension and credential revocation do not isolate the bypass. Wrong order is fatal.
    suspended = administrative_step(granted, auth, order_credential(granted, auth, "suspend"), "suspend")
    assert suspended.institution.status == "suspended" and MODES[suspended.mode][1] == 1
    rejected = administrative_step(suspended, auth, order_credential(suspended, auth, "beginRepair"), "beginRepair")
    assert rejected == suspended
    unsafe_wrong_order = [2 + u - 1 - 1 for u in (0, 1)]
    assert all(x not in SAFE for x in unsafe_wrong_order)
    # Same actual controller with two environmental port choices. No office act licenses bypass.
    reference = State(5, frozenset())
    closed, no_bypass = control_epoch(reference, auth, {s: 5 for s in CONFIGS[0].sensors}, {}, {}, 0)
    affected, raw_bypass = control_epoch(reference, auth, {s: 5 for s in CONFIGS[0].sensors}, {}, {}, 1)
    assert affected.x == closed.x + 1 and no_bypass.action == raw_bypass.action
    assert affected.institution == closed.institution and 20 not in granted.institution.office
    isolated = administrative_step(suspended, auth, order_credential(suspended, auth, "isolate"), "isolate")
    repairing = administrative_step(isolated, auth, order_credential(isolated, auth, "beginRepair"), "beginRepair")
    unclean = administrative_step(repairing, auth, order_credential(repairing, auth, "finishRepair"), "finishRepair", clean=False)
    assert unclean == repairing

    # Operationally generated attribution, historical validity and current rejection.
    faulty = frozenset({2, 5, 8, 11})
    auth = Authentication(faulty)
    state = State(5, faulty)
    received = report_round(state, auth, {0: 4, 1: 6}, {(2, 3): 4, (2, 4): 6, (2, 5): 5})
    a = next(r for r in received[3] if r.signer == 2)
    b = next(r for r in received[4] if r.signer == 2)
    assert verify_equivocation(auth, a, b)
    honest_reports = [r for row in received.values() for r in row if r.signer not in faulty]
    assert not any(verify_equivocation(auth, a, b) for a, b in product(honest_reports, repeat=2))
    old_messages = endorsement_round(state, auth, received, {5: CONTROLS})
    old_u, old_cert = assemble(gate_observation(state), auth, old_messages)
    newstate = replace(state, config=CONFIGS[1], institution=replace(state.institution, generation=1))
    assert not verify_current(gate_observation(newstate), auth, old_u, old_cert)
    assert verify_equivocation(auth, a, b)  # historical verifier deliberately ignores current membership
    mixed = (auth.adversary_emit(5, 0, "endorse", (CONFIGS[0].digest, 0, state.institution.digest, 2)),
             auth.adversary_emit(11, 1, "endorse", (CONFIGS[1].digest, 0, newstate.institution.digest, 2)))
    assert len({s.signer for s in mixed}) == 2 and all(auth.verify(s) for s in mixed)
    assert not verify_current(gate_observation(newstate), auth, 2, mixed)
    assert 8 + 2 - 1 + 1 == 10  # a scope-blind threshold would license this
    replay_view = replace(gate_observation(state), epoch=1)
    assert not verify_current(replay_view, auth, old_u, old_cert)
    assert not verify_current(gate_observation(state), auth, old_u, old_cert[:1] * 2)
    forged = Signature(3, 0, "endorse", (CONFIGS[0].digest, 0, state.institution.digest, 0))
    assert forged not in auth.events and not auth.verify(forged)

    # Availability regression: an unauthenticated wrong-era packet claiming signer3
    # used to overwrite that actor's genuine u=2 share during identity deduplication.
    flood_state = State(2, frozenset({5}))
    flood_auth = Authentication(flood_state.faults)
    flood_view = gate_observation(flood_state)
    flood_reports = report_round(flood_state, flood_auth, {0: 2, 1: 2, 2: 2}, {})
    honest_shares = endorsement_round(flood_state, flood_auth, flood_reports, {})
    assert {s.signer for s in honest_shares} == {3, 4}
    payload2 = (CONFIGS[0].digest, 0, flood_state.institution.digest, 2)
    poison3 = Signature(3, 1, "endorse", payload2)
    assert not flood_auth.verify(poison3)
    repaired = assemble(flood_view, flood_auth, honest_shares + (poison3,))
    assert repaired is not None and repaired[0] == 2
    assert verify_current(flood_view, flood_auth, *repaired)
    assert {s.signer for s in repaired[1]} == {3, 4}
    poison4 = Signature(4, 0, "unrelated", payload2)
    valid_bad = flood_auth.adversary_emit(5, 0, "endorse", payload2)
    wrong_era = flood_auth.adversary_emit(5, 1, "endorse", payload2)
    wrong_kind = flood_auth.adversary_emit(5, 0, "report", payload2)
    wrong_config = flood_auth.adversary_emit(5, 0, "endorse", (CONFIGS[1].digest, 0, flood_state.institution.digest, 2))
    wrong_epoch = flood_auth.adversary_emit(5, 0, "endorse", (CONFIGS[0].digest, 1, flood_state.institution.digest, 2))
    wrong_institution = flood_auth.adversary_emit(5, 0, "endorse", (CONFIGS[0].digest, 0, Institution(norm_cap=1).digest, 2))
    unknown_signer = flood_auth.emit(99, 0, "endorse", payload2)  # authentic outsider, ineligible support
    invalid_packets = (poison3, poison4, wrong_era, wrong_kind, wrong_config, wrong_epoch, wrong_institution, unknown_signer)
    for invalid in invalid_packets:
        assert not verify_current(flood_view, flood_auth, 2, honest_shares + (invalid,))
        for packets in (honest_shares + (invalid,), (invalid,) + honest_shares,
                        honest_shares + (invalid, valid_bad, valid_bad, invalid)):
            result = assemble(flood_view, flood_auth, packets)
            assert result is not None and result[0] == 2 and verify_current(flood_view, flood_auth, *result)
            assert {3, 4} <= {s.signer for s in result[1]}
    flood_orders = 0
    for packets in set(permutations(honest_shares + (poison3, poison4, valid_bad, valid_bad, wrong_era))):
        result = assemble(flood_view, flood_auth, packets)
        assert result is not None and result[0] == 2 and verify_current(flood_view, flood_auth, *result)
        assert {s.signer for s in result[1]} == {3, 4, 5}
        flood_orders += 1
    assert flood_orders == 2520

    # Old key retention is not clean current-key repair; no temporal claim from raw timestamps.
    leaked = Authentication(frozenset(), frozenset({(3, 0)}))
    old_forged = leaked.adversary_emit(3, 0, "endorse", (CONFIGS[0].digest, 0, state.institution.digest, 2))
    assert leaked.verify(old_forged) and not verify_current(gate_observation(newstate), leaked, 2, (old_forged,))
    try:
        leaked.adversary_emit(3, 1, "endorse", ())
        raise AssertionError("old key unexpectedly granted new-era access")
    except ValueError:
        pass
    falsely_clean = Authentication(frozenset({11}), frozenset({(9, 1)}))
    unsafe_payload = (CONFIGS[1].digest, 0, newstate.institution.digest, 2)
    compromised_current = (falsely_clean.adversary_emit(9, 1, "endorse", unsafe_payload),
                           falsely_clean.adversary_emit(11, 1, "endorse", unsafe_payload))
    assert verify_current(gate_observation(newstate), falsely_clean, 2, compromised_current)
    assert 8 + 2 - 1 + 1 not in SAFE  # key leakage invalidates the operational honest-signer premise

    monitor_checks = 0
    for history in product((0, 1), repeat=6):
        events = [event for epoch, count in enumerate(history)
                  for event in ({"kind": "start", "epoch": epoch}, {"kind": "end", "epoch": epoch, "service": count})]
        monitor = breach_monitor(events)
        assert all(monitor[n] == duty_breach(events[:n]) for n in range(len(events)+1))
        assert all(not monitor[n] or monitor[n+1] for n in range(len(events)))
        monitor_checks += 1
    # Maximal finite pending executions have a verdict; ordinary pending prefixes do not.
    assert not duty_breach([{"kind": "start"}])
    assert duty_breach([{"kind": "start"}, {"kind": "end", "service": 0}])
    assert not duty_breach([{"kind": "end", "service": 0}])
    assert duty_breach([{"kind": "start"}, {"kind": "end", "service": 0, "exception": True}])
    assert not duty_breach([{"kind": "start"}, {"kind": "end", "service": 0}], replace(UNIT_DUTY, exception_epochs=(0,)))
    assert not maximal_verdict(State(5, frozenset()), pending_epoch=True)["service"]

    # Observation projections deliberately lose hidden capability and motive, not safety data.
    stays, success_stays = capability_step(CapabilityState(1), 1, 1)
    fails, success_fails = capability_step(CapabilityState(1), 1, 0)
    assert capability_observation(success_stays) == capability_observation(success_fails)
    assert stays.capacity != fails.capacity
    _, refusal = capability_step(CapabilityState(1), 0, 1)
    _, incapacity = capability_step(CapabilityState(0), 1, 0)
    assert capability_observation(refusal) == capability_observation(incapacity)
    assert refusal.capacity_before != incapacity.capacity_before
    # Possible contribution differs from forceability when another port can cancel.
    outputs = [capability_step(CapabilityState(1), 1, 1, b)[1].output for b in (-1, 0)]
    assert any(y >= 1 for y in outputs) and not all(y >= 1 for y in outputs)

    return {"capacity_grid_cases": capacity_checks, "local_support_profiles": local_checks,
            "global_fault_sets": len(finite_fault_family()), "recovery_traces": trace_count,
            "realized_service_epochs": epochs, "breach_histories": monitor_checks,
            "invalid_share_orderings": flood_orders,
            "counterexamples": {"wrong_order_successors": unsafe_wrong_order,
                                "mixed_scope_unsafe_successor": 10,
                                "unauthorized_bypass_effect": (closed.x, affected.x),
                                "past_success": (asdict(success_stays), asdict(success_fails)),
                                "omission": (asdict(refusal), asdict(incapacity))},
            "recovery_trace": specimen}


if __name__ == "__main__":
    print(json.dumps(run_checks(), indent=2, sort_keys=True))

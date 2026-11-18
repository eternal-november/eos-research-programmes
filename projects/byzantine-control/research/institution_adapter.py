"""Clocked, action-indexed institutional adapter. No writes or external packages.

The four stages are administration, report, endorse, effect. A fixed global
coalition controls its requests at every stage; malformed requests become no-ops.
The failure state is explicit and clocked. See INSTITUTION-ASSEMBLY.md.
"""
from __future__ import annotations

from dataclasses import dataclass, replace
from itertools import product
import json
import institution_model as inst


OFFICE, GATE = 12, 13
ACTORS = tuple(range(14))
STAGES = ("admin", "report", "endorse", "effect")


@dataclass(frozen=True)
class Intent:
    order: str = "none"
    clean: bool = False
    consent: bool = False
    access: bool = True
    replacement: inst.Config | None = None


@dataclass(frozen=True)
class Command:
    tag: str
    value: object = None


@dataclass(frozen=True)
class Issue:
    era: int
    kind: str
    payload: tuple


@dataclass(frozen=True)
class Send:
    recipient: int
    packet: object


IDLE = Command("idle")


@dataclass(frozen=True)
class Observation:
    stage: str
    tick: int
    public: inst.GateView
    clean: bool
    reading: int | None
    inbox: tuple
    intent: Intent | None
    failure: str | None


@dataclass(frozen=True)
class World:
    plant: inst.State
    stage: str
    tick: int
    signatures: frozenset
    inboxes: tuple
    readings: tuple
    intent: Intent
    histories: tuple
    age: int = 0
    duty_events: tuple = ()
    failure: str | None = None


@dataclass(frozen=True)
class Environment:
    # At the admin->report boundary, each sensor gets x+offset[its identity].
    # Correct offsets must be -1,0,1; the admitted environment includes all such tuples.
    offsets: tuple = (0,) * 12
    bypass: int = 0
    next_intent: Intent = Intent()


@dataclass(frozen=True)
class Transition:
    stage: str
    tick: int
    requests: tuple
    order: str | None = None
    registered: bool = False
    control: int | None = None
    bypass: int = 0
    delivered: int = 0
    failure: str | None = None


class LocalVerifier:
    """Only public verification results for received packets; no global log or B."""
    def __init__(self, inbox):
        self.valid = frozenset(packet for packet, accepted in inbox if accepted)

    def verify(self, packet):
        return packet in self.valid


def snapshot(world, actor):
    public = inst.gate_observation(world.plant)
    inbox = tuple((s, s in world.signatures) for s in world.inboxes[actor])
    reading = world.readings[actor] if actor in world.plant.config.sensors else None
    return Observation(world.stage, world.tick, public, world.plant.clean, reading,
                       inbox, world.intent if actor == OFFICE else None, world.failure)


def initial(plant, intent=Intent(), signatures=frozenset()):
    if not isinstance(plant, inst.State) or not isinstance(plant.institution, inst.Institution) or not isinstance(plant.config, inst.Config):
        raise ValueError("initial state requires typed component records")
    if (type(plant.x) is not int or type(plant.epoch) is not int or plant.epoch < 0
            or not isinstance(plant.mode, str) or plant.mode not in inst.MODES or type(plant.institution.norm_cap) is not int
            or plant.institution.norm_cap < 0 or not intent_shape(Intent(replacement=plant.config))
            or not isinstance(plant.institution.status, str) or plant.institution.status not in {"active", "suspended", "repairing", "ready"}
            or type(plant.institution.generation) is not int or plant.institution.generation < 0
            or not isinstance(plant.institution.office, tuple)
            or any(type(i) is not int for i in plant.institution.office)
            or not isinstance(plant.faults, frozenset) or any(type(i) is not int for i in plant.faults)):
        raise ValueError("ill-typed initial physical/institutional interface")
    if not inst.admissible_faults(plant.faults) or not inst.configuration_allowed(plant.config):
        raise ValueError("not an admitted initial fault/configuration pair")
    if signatures:
        raise ValueError("initial authentication history must be reconstructed by transitions")
    world = World(plant, "admin", 0, frozenset(signatures), ((),) * 14, (None,) * 12,
                  intent, (), duty_events=(("start", plant.epoch, 0),))
    return replace(world, histories=tuple((("observe", snapshot(world, i)),) for i in ACTORS))


def observe(world, actor):
    return world.histories[actor]


def policy(actor, history):
    """Single actor-local policy; histories never contain actual x or B."""
    obs = history[-1][1]
    if obs.failure is not None:
        return IDLE
    view = obs.public
    if obs.stage == "admin" and actor == OFFICE:
        return Command("admin", obs.intent)
    if obs.stage == "report" and view.mode == "live" and actor in view.config.sensors:
        return Command("report", obs.reading)
    if obs.stage == "endorse" and view.mode == "live" and actor in view.config.authorizers:
        messages = tuple(packet for packet, _ in obs.inbox)
        controls = inst.authorizer_policy(view, messages, LocalVerifier(obs.inbox))
        return Command("endorse", controls)
    if obs.stage == "effect" and actor == GATE:
        if view.mode != "live":
            return Command("apply", (1, ())) if view.institution.norm_cap >= 1 else Command("fail", "permission excludes replenishment")
        messages = tuple(packet for packet, _ in obs.inbox)
        result = inst.assemble(view, LocalVerifier(obs.inbox), messages)
        return Command("apply", result) if result is not None else Command("fail", "no current authorized control")
    return IDLE


def follows(world, requests):
    return (isinstance(requests, tuple) and len(requests) == len(ACTORS)
            and all(i in world.plant.faults or requests[i] == policy(i, observe(world, i)) for i in ACTORS))


def signature_shape(packet):
    if not isinstance(packet, inst.Signature):
        return False
    if type(packet.signer) is not int or packet.signer < 0 or type(packet.era) is not int or packet.era < 0:
        return False
    if not isinstance(packet.kind, str) or not isinstance(packet.payload, tuple):
        return False
    try:
        hash(packet)
    except TypeError:
        return False
    return True


def raw_packets(world, actor, request, events):
    """Decode finite requests; Issue always signs as the actual issuing actor.

    Forwarding an existing Signature never adds it to the authentication log.
    A claimed different identity is therefore not a signing capability.
    """
    if not isinstance(request, Command):
        return ()
    p, result = world.plant, []
    if world.stage == "report" and request.tag == "report" and type(request.value) is int:
        for recipient in p.config.authorizers:
            packet = inst.Signature(actor, p.config.era, "report", (p.config.digest, p.epoch, p.epoch, recipient, request.value))
            events.add(packet)
            result.append(Send(recipient, packet))
    elif world.stage == "endorse" and request.tag == "endorse" and isinstance(request.value, tuple):
        for value in request.value:
            if type(value) is int:
                packet = inst.Signature(actor, p.config.era, "endorse", (p.config.digest, p.epoch, p.institution.digest, value))
                events.add(packet)
                result.append(Send(GATE, packet))
    elif request.tag == "raw" and isinstance(request.value, tuple):
        for send in request.value:
            if not isinstance(send, Send) or type(send.recipient) is not int or send.recipient not in ACTORS:
                continue
            packet = send.packet
            if isinstance(packet, Issue):
                packet = inst.Signature(actor, packet.era, packet.kind, packet.payload)
                if signature_shape(packet):
                    events.add(packet)
            if signature_shape(packet):
                result.append(Send(send.recipient, packet))
    return tuple(result)


def intent_shape(intent):
    """A malformed administrative input is a rejected attempt, not an exception."""
    if not isinstance(intent, Intent) or not isinstance(intent.order, str):
        return False
    if any(type(flag) is not bool for flag in (intent.clean, intent.consent, intent.access)):
        return False
    candidate = intent.replacement
    if candidate is not None:
        if not isinstance(candidate, inst.Config) or type(candidate.era) is not int or candidate.era < 0:
            return False
        if any(not isinstance(role, tuple) or len(role) != 3
               or any(type(i) is not int for i in role) for role in (candidate.sensors, candidate.authorizers)):
            return False
    return True


def environment_admissible(world, env):
    """Environment contract, independent of safety or certificate success.

    Sampling occurs after the administrative interface has installed its mode and
    role map. Computing that interface update does not inspect x or control success.
    """
    if not isinstance(env, Environment):
        return False
    if world.failure is not None:
        return True
    p = world.plant
    if world.stage == "admin":
        intent = world.intent
        if intent_shape(intent) and intent.order in {"suspend", "isolate", "beginRepair", "finishRepair", "reinstate", "grantTwo"}:
            auth = inst.Authentication(p.faults)
            auth.events = set(world.signatures)
            credential = inst.order_credential(p, auth, intent.order)
            p = inst.administrative_step(p, auth, credential, intent.order, clean=intent.clean,
                                        consent=intent.consent, access=intent.access, replacement=intent.replacement)
        return (p.mode != "live" or (isinstance(env.offsets, tuple) and len(env.offsets) == 12
                and all(type(env.offsets[i]) is int and env.offsets[i] in (-1, 0, 1)
                        for i in p.config.sensors if i not in p.faults)))
    if world.stage == "effect":
        return type(env.bypass) is int and abs(env.bypass) <= inst.MODES[p.mode][1]
    return True


def _advance(before, after, requests, record):
    # Faulty private memories are outside the query family. The complete request
    # remains in the edge record; it is not rendered or treated as a correct memory.
    # Accepted signing events and all correct own commands/receipts are retained.
    histories = tuple(before.histories[i] + (("issued", requests[i] if i not in before.plant.faults else ("byzantine-input",)),
                                           ("observe", snapshot(after, i))) for i in ACTORS)
    return replace(after, histories=histories), record


def step(world, requests, env=Environment()):
    """Total on every following profile and admitted environment.

    Non-following correct requests are outside Follows, not adversarial failures.
    A missing mission certificate becomes an explicit failed state, never an empty run.
    """
    if not follows(world, requests):
        raise ValueError("correct component does not follow its local policy")
    p = world.plant
    after = replace(world, tick=world.tick + 1, age=world.age + 1)
    record = Transition(world.stage, world.tick, requests)
    if world.failure is not None:
        return _advance(world, after, requests, replace(record, failure=world.failure))
    if world.stage == "admin":
        intent = requests[OFFICE].value
        events = set(world.signatures)
        pnext = p
        accepted, order = False, None
        if intent_shape(intent) and intent.order in {"suspend", "isolate", "beginRepair", "finishRepair", "reinstate", "grantTwo"}:
            auth = inst.Authentication(p.faults)
            auth.events = events
            credential = inst.order_credential(p, auth, intent.order)
            pnext = inst.administrative_step(p, auth, credential, intent.order,
                clean=intent.clean, consent=intent.consent, access=intent.access, replacement=intent.replacement)
            # For an identity update that is already idempotent, accepted records the
            # same guard used by the constitutive/enforcement interface.
            accepted = (inst.has_power(p, auth, credential, intent.order)
                        and inst.order_permitted(p, intent.order, intent.clean, intent.consent) and intent.access
                        and (intent.order != "reinstate" or (intent.replacement is not None
                             and intent.replacement.era > p.config.era and inst.configuration_allowed(intent.replacement))))
            order = intent.order
        readings = []
        failure = None
        for actor in range(12):
            offset = env.offsets[actor] if isinstance(env.offsets, tuple) and len(env.offsets) == 12 else None
            if pnext.mode == "live" and actor in pnext.config.sensors and actor not in pnext.faults and (type(offset) is not int or offset not in (-1, 0, 1)):
                failure = "measurement premise failed"
            readings.append(pnext.x + offset if type(offset) is int else None)
        after = replace(after, plant=pnext, stage="report", signatures=frozenset(events),
                        inboxes=((),) * 14, readings=tuple(readings), failure=failure)
        return _advance(world, after, requests, replace(record, order=order, registered=accepted, failure=failure))
    if world.stage in ("report", "endorse"):
        events = set(world.signatures)
        inboxes = [list(items) for items in world.inboxes]
        # Correct transmissions are included independently of Byzantine traffic.
        for actor in ACTORS:
            for send in raw_packets(world, actor, requests[actor], events):
                accepted_route = ((world.stage == "report" and send.recipient in p.config.authorizers)
                                  or (world.stage == "endorse" and send.recipient == GATE))
                if accepted_route:
                    inboxes[send.recipient].append(send.packet)
        after = replace(after, stage="endorse" if world.stage == "report" else "effect",
                        signatures=frozenset(events), inboxes=tuple(map(tuple, inboxes)))
        return _advance(world, after, requests, record)
    # The effect is defined even when authorization is unavailable. The zero-input
    # fallback still incurs the stipulated physical service withdrawal; failure is
    # declared and no safety/service success is inferred from this fallback.
    command = requests[GATE]
    failure = None
    if command.tag == "apply":
        u, certificate = command.value
    else:
        u, certificate = 0, ()
        failure = str(command.value)
    b = env.bypass if type(env.bypass) is int else 0
    capacity, radius = inst.MODES[p.mode]
    if type(env.bypass) is not int or abs(b) > radius:
        failure = "physical bypass premise failed"
    if not 0 <= u <= capacity or u > p.institution.norm_cap:
        failure = "realization or permission unavailable"
        u = 0
    following = p.x + u - 1 + b
    pnext = replace(p, x=following, epoch=p.epoch + 1, delivered=p.delivered + 1)
    duty = world.duty_events + (("end", p.epoch, 1), ("start", p.epoch + 1, 0))
    after = replace(after, plant=pnext, stage="admin", inboxes=((),) * 14, readings=(None,) * 12,
                    intent=env.next_intent, age=0, duty_events=duty, failure=failure)
    return _advance(world, after, requests, replace(record, control=u, bypass=b, delivered=1, failure=failure))


def requested_profile(world, faulty_requests=None):
    faulty_requests = faulty_requests or {}
    return tuple(faulty_requests.get(i, IDLE) if i in world.plant.faults else policy(i, observe(world, i)) for i in ACTORS)


def invariant(world):
    """Phase invariant's public/physical clauses; evidence clauses are checked below."""
    p = world.plant
    return (world.failure is None and p.x in inst.SAFE and inst.admissible_faults(p.faults)
            and inst.configuration_allowed(p.config) and p.institution.norm_cap >= 2
            and p.mode in inst.MODES and world.age <= 3 and world.tick % 4 == STAGES.index(world.stage))


def evidence_invariant(world):
    p = world.plant
    if world.stage in ("endorse", "effect") and p.mode == "live":
        for actor in p.config.authorizers:
            if actor in p.faults:
                continue
            obs = snapshot(world, actor)
            values = []
            for sensor in p.config.sensors:
                valid = [packet.payload[-1] for packet, ok in obs.inbox if ok and packet.kind == "report"
                         and packet.signer == sensor and packet.era == p.config.era and len(packet.payload) == 5
                         and isinstance(packet.payload[-1], int) and packet.payload[:3] == (p.config.digest, p.epoch, p.epoch)]
                values.append(min(valid) if valid else 0)
            assert abs(sorted(values)[1] - p.x) <= 1
    if world.stage == "effect" and p.mode == "live":
        command = policy(GATE, observe(world, GATE))
        assert command.tag == "apply"
        u, certificate = command.value
        assert len({s.signer for s in certificate}) >= 2
        assert any(s.signer not in p.faults for s in certificate)
        assert all(p.x + u - 1 + b in inst.SAFE for b in (-1, 0, 1))


def check_decode(before, after, event):
    """Independent clock/fault/effect/service projection; no call to control_epoch."""
    assert after.tick == before.tick + 1 and after.plant.faults == before.plant.faults
    if before.failure is not None:
        assert after.plant == before.plant and after.failure == before.failure and event.delivered == 0
    elif before.stage == "effect":
        assert after.plant.x - before.plant.x == event.control - event.delivered + event.bypass
        assert event.delivered == 1 and after.plant.delivered == before.plant.delivered + 1
        assert after.plant.epoch == before.plant.epoch + 1 and after.stage == "admin"
    else:
        assert after.plant.x == before.plant.x and after.plant.delivered == before.plant.delivered
        assert after.plant.epoch == before.plant.epoch
        assert after.stage == STAGES[STAGES.index(before.stage) + 1]
    for i in ACTORS:
        assert after.histories[i][:-2] == before.histories[i]
        assert after.histories[i][-1] == ("observe", snapshot(after, i))


def request_cases(world, actor):
    """Finite stress classes, not a claim to enumerate all integer packet payloads."""
    p = world.plant
    report = lambda recipient, value: Issue(p.config.era, "report", (p.config.digest, p.epoch, p.epoch, recipient, value))
    endorsement = Issue(p.config.era, "endorse", (p.config.digest, p.epoch, p.institution.digest, 2))
    # Claim a correct active identity; this creates no authentication event.
    honest = next(i for i in p.config.authorizers if i not in p.faults)
    forged = inst.Signature(honest, p.config.era + 1, "endorse", endorsement.payload)
    unhashable = inst.Signature(honest, p.config.era, "endorse", (p.config.digest, p.epoch, p.institution.digest, [2]))
    old = tuple(Send(GATE, s) for s in sorted(world.signatures, key=repr) if s.kind == "endorse" and s.era <= p.config.era)[:2]
    equivocation = tuple(Send(a, report(a, -100 if a % 2 else 100)) for a in p.config.authorizers)
    return (IDLE, None, Command("unknown", ()), Command("report", "malformed"),
            Command("raw", (Send(GATE, forged), Send(GATE, forged))),
            Command("raw", old), Command("raw", equivocation),
            Command("endorse", (0, 1, 2)),
            Command("raw", (Send(GATE, endorsement), Send(GATE, endorsement))),
            Command("raw", (Send(-1, endorsement), Send(GATE, Issue(-1, "endorse", ())),
                            Send(GATE, unhashable), Send(GATE, {"raw": "bytes"}), Send(GATE, None), "bad")))


def run_checks():
    transitions = profiles = recovery_epochs = 0
    local_classes = {}
    # Contexts exercise no fault, individual role faults, joint role faults, and
    # two future-configuration faults carried unchanged through replacement.
    fault_cases = (frozenset(), frozenset({2}), frozenset({5}), frozenset({2, 5}),
                   frozenset({8, 11}), frozenset({2, 5, 8, 11}))
    schedule = (Intent(), Intent("suspend"), Intent("isolate"), Intent("beginRepair"),
                Intent(), Intent("finishRepair", clean=True), Intent("reinstate", replacement=inst.CONFIGS[1]), Intent())
    for faults, x in product(fault_cases, inst.SAFE):
        world = initial(inst.State(x, faults), schedule[0])
        for epoch, intent in enumerate(schedule):
            assert world.intent == intent
            for _ in range(4):
                assert invariant(world)
                evidence_invariant(world)
                for i in ACTORS:
                    if i not in faults:
                        key = (i, observe(world, i))
                        value = policy(i, observe(world, i))
                        assert local_classes.setdefault(key, value) == value
                # Admitted plant choices are varied across epoch and actor; all honest
                # messages arrive, independently of the chosen hostile traffic class.
                hostile = {i: request_cases(world, i)[(epoch + i) % 10] for i in faults}
                env = Environment(tuple(-1 if i % 2 else 1 for i in range(12)),
                                  (-1 if epoch % 2 else 1) if world.plant.mode == "live" else 0,
                                  schedule[epoch + 1] if epoch + 1 < len(schedule) else Intent())
                profile = requested_profile(world, hostile)
                assert environment_admissible(world, env)
                following, event = step(world, profile, env)
                check_decode(world, following, event)
                assert invariant(following)
                evidence_invariant(following)
                world = following
                transitions += 1
            recovery_epochs += 1
        assert world.plant.config == inst.CONFIGS[1] and world.plant.delivered == len(schedule)
        assert world.tick == 4 * len(schedule)
        history = [{"kind": kind, "epoch": epoch, "service": delivered} for kind, epoch, delivered in world.duty_events]
        assert not inst.duty_breach(history)

    # All 100 joint traffic profiles of both currently faulty roles, in each stage,
    # plus independent inactive-fault traffic. Honest requests remain fixed.
    for x in inst.SAFE:
        world = initial(inst.State(x, frozenset({2, 5, 8, 11})))
        for stage in STAGES:
            assert world.stage == stage
            cases2, cases5 = request_cases(world, 2), request_cases(world, 5)
            for r2, r5 in product(cases2, cases5):
                raw = {2: r2, 5: r5, 8: cases2[4], 11: cases5[8]}
                for bypass in ((-1, 0, 1) if stage == "effect" else (0,)):
                    env = Environment(bypass=bypass)
                    assert environment_admissible(world, env)
                    following, event = step(world, requested_profile(world, raw), env)
                    check_decode(world, following, event)
                    assert invariant(following)
                    evidence_invariant(following)
                    profiles += 1
            world, event = step(world, requested_profile(world), Environment())

    # Exact packet overwrite witness must remain harmless after a real endorsement phase.
    world = initial(inst.State(2, frozenset({5})))
    for _ in range(2):
        world, _ = step(world, requested_profile(world))
    p = world.plant
    poison = inst.Signature(3, 1, "endorse", (p.config.digest, p.epoch, p.institution.digest, 2))
    profile = requested_profile(world, {5: Command("raw", (Send(GATE, poison),))})
    world, _ = step(world, profile)
    assert policy(GATE, observe(world, GATE)).tag == "apply"
    world, record = step(world, requested_profile(world), Environment(bypass=-1))
    assert world.plant.x == 2 and record.delivered == 1
    big = initial(inst.State(5, frozenset({2})))
    big, _ = step(big, requested_profile(big))
    big, _ = step(big, requested_profile(big, {2: Command("report", 10 ** 5000)}))
    assert invariant(big)
    evidence_invariant(big)

    # Carry a genuinely different honest local view across report and endorsement:
    # medians 4 and 6 yield {1,2} and {0,1}; with a withholding bad authorizer only
    # the common control1 is certified. No policy receives the true inventory5.
    split = initial(inst.State(5, frozenset({2, 5})))
    split_offsets = (-1, 1) + (0,) * 10
    split, _ = step(split, requested_profile(split), Environment(offsets=split_offsets))
    cp = split.plant
    attack = Command("raw", tuple(Send(a, Issue(0, "report", (cp.config.digest, 0, 0, a, 4 if a == 3 else 6)))
                                  for a in cp.config.authorizers))
    split, _ = step(split, requested_profile(split, {2: attack}))
    assert policy(3, observe(split, 3)) == Command("endorse", (1, 2))
    assert policy(4, observe(split, 4)) == Command("endorse", (0, 1))
    split, _ = step(split, requested_profile(split))
    assert policy(GATE, observe(split, GATE)).value[0] == 1
    for b in (-1, 0, 1):
        end, record = step(split, requested_profile(split), Environment(bypass=b))
        check_decode(split, end, record)
        assert invariant(end) and end.plant.x == 5 + b

    # Normative infeasibility is an admitted changed context with an explicit failed
    # transition. Nonblocking is not established by raising an exception or deleting it.
    failed = initial(inst.State(2, frozenset(), institution=inst.Institution(norm_cap=1)))
    for _ in range(4):
        before = failed
        failed, event = step(failed, requested_profile(failed), Environment(bypass=-1))
        check_decode(before, failed, event)
    assert failed.failure == "no current authorized control" and failed.plant.x == 0
    later, event = step(failed, requested_profile(failed))
    check_decode(failed, later, event)
    assert later.failure and later.tick == failed.tick + 1 and event.delivered == 0

    # Admission is public over the whole F; an actual empty B never licenses a bad
    # proposed configuration. Permission also requires physical readiness.
    p = inst.State(5, frozenset(), institution=inst.Institution(status="ready"), mode="ready", clean=True)
    bad_config = inst.Config(2, (0, 6, 7), (3, 4, 5))
    world = initial(p, Intent("reinstate", replacement=bad_config))
    after, record = step(world, requested_profile(world))
    assert not record.registered and after.plant.config == p.config and after.plant.mode == "ready"
    for malformed in (None, Intent("reinstate", replacement="bad"), Intent("grantTwo", consent="yes")):
        bad_input = initial(p, malformed)
        after, record = step(bad_input, requested_profile(bad_input))
        assert after.plant == p and not record.registered and after.tick == 1
    # Isolation makes sensing unnecessary; no fresh sample is assumed during repair.
    isolated = initial(inst.State(2, frozenset({2, 5, 8, 11}), institution=inst.Institution(status="repairing"), mode="repair"))
    for _ in range(4):
        isolated, _ = step(isolated, requested_profile(isolated), Environment(offsets=(None,) * 12))
    assert invariant(isolated) and isolated.plant.x == 2 and isolated.plant.delivered == 1
    return {"phase_transitions": transitions, "completed_recovery_epochs": recovery_epochs,
            "following_traffic_profiles": profiles, "correct_local_history_classes": len(local_classes),
            "four_phase_clock_and_service_decode": True, "fixed_faults_across_replacement": True,
            "invalid_and_replayed_requests_normalized": True, "explicit_unavailable_mission_failure": True,
            "split_local_views_common_control": 1,
            "unavailable_normative_state_successor": failed.plant.x,
            "scope": "structural arbitrary-finite-request proof plus bounded traffic/offset/recovery tests; zero-delay physical context"}


if __name__ == "__main__":
    print(json.dumps(run_checks(), indent=2, sort_keys=True))

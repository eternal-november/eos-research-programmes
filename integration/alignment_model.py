"""Operational signing, evidence alternatives, and baseline row adapters.

Run --check to reproduce alignment_results.json or --write to refresh it.
All source kernels retain arbitrary admitted faulty effects.
"""
from __future__ import annotations
from dataclasses import dataclass
import argparse
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent / "research"))
from structure_model import Relation, compile_kernel, extract_tables, join_tree_solve, natural_join
from finite_model import Node, Table, Initial, Observation, Outcome, verify
import quorum_alignment as qa
import digital_model as digital
from evidence_model import SensorWorld, witness_effect

if sys.flags.optimize:
    raise RuntimeError("Run without Python optimization")

def submasks(mask):
    value = mask
    while True:
        yield value
        if value == 0:
            break
        value = (value-1) & mask

def own_mask(facts, actor):
    return (facts >> (2*actor)) & 3

def exclusive(facts, effective_bad, actors=4):
    return all(i == effective_bad or own_mask(facts, i) != 3 for i in range(actors))

def guard(own, value):
    return int(qa.local_action(tuple(v for v in (0, 1) if own & (1 << v)), value)[0] == "sign")

@dataclass(frozen=True)
class RoleFault:
    executor: int | None
    key: int | None
    @property
    def effective(self):
        values = {i for i in (self.executor, self.key) if i is not None}
        assert len(values) <= 1
        return next(iter(values)) if values else None

@dataclass(frozen=True)
class SignState:
    facts: int
    code_logs: tuple[int, ...]

class SigningKernel:
    actors = 4
    def faults(self):
        yield RoleFault(None, None)
        for i in range(self.actors):
            yield RoleFault(i, None)
            yield RoleFault(None, i)
            yield RoleFault(i, i)
    def compliant(self, fault, actor):
        return fault.executor != actor
    def initials(self, fault):
        return (Initial(SignState(0, (0,)*self.actors), ("boot",)*self.actors),)
    def initial_violations(self, fault, state):
        return () if state == SignState(0, (0,)*self.actors) else ("not_empty_initial_signing_state",)
    def observations(self, fault, state):
        yield Observation((None,)*self.actors)
        for actor, value in itertools.product(range(self.actors), (0, 1)):
            local = [None]*self.actors
            local[actor] = str(state.code_logs[actor])+":"+str(value)
            yield Observation(tuple(local), (actor, value))
    def outcomes(self, fault, state, observation, issued):
        request = observation.physical_sample
        if request is None:
            choices = (0,)
        else:
            actor, value = request
            choices = (0, 1) if fault.executor == actor else (issued[actor],)
        for command in choices:
            if command not in (0, 1):
                yield Outcome(state, frozenset(), ("missing_invocation",), {})
                continue
            facts, logs = state.facts, list(state.code_logs)
            bad, steps = [], []
            if request is not None:
                actor, value = request
                if fault.executor != actor and command != guard(logs[actor], value):
                    bad.append("compliant_guard_deviation")
                if command:
                    facts |= 1 << (2*actor+value)
                    steps.append((actor, value))
                    if fault.executor != actor:
                        logs[actor] |= 1 << value
            for forged in ((0,) if fault.effective is None else range(4)):
                result, events = facts, list(steps)
                if fault.effective is not None:
                    for value in (0, 1):
                        if forged & (1 << value):
                            result |= 1 << (2*fault.effective+value)
                            events.append((fault.effective, value))
                successor = SignState(result, tuple(logs))
                verdict = list(bad)
                if not exclusive(result, fault.effective):
                    verdict.append("effective_honest_double_sign")
                if qa.certificate(result, 0) and qa.certificate(result, 1):
                    verdict.append("conflicting_issued_certificates")
                projected = state.facts
                for event in events:
                    projected = qa.step(projected, fault.effective, event)
                # This assertion tests correspondence on actual guard-following
                # transitions. Illegal commands remain modeled and marked above.
                if not verdict and exclusive(state.facts, fault.effective):
                    assert projected == result
                for received in submasks(result):
                    accepted = tuple(v for v in (0, 1) if qa.certificate(received, v))
                    assert received & ~result == 0
                    if not verdict:
                        assert len(accepted) <= 1
                    yield Outcome(successor, frozenset(("certificate",)) if accepted else frozenset(),
                                  tuple(verdict), {"request": request, "command": command,
                                  "adversarial_signature_mask": forged, "signing_events": events,
                                  "abstract_facts": projected, "received": received,
                                  "accepted": accepted})
    def service(self, fault): return ()
    def recurrent_service(self, fault): return ()

def signing_envelope(kernel):
    nodes = set()
    for fault in kernel.faults():
        for facts in range(256):
            if not exclusive(facts, fault.effective):
                continue
            choices = []
            for i in range(4):
                own = own_mask(facts, i)
                if fault.executor == i:
                    choices.append((0,))
                elif fault.key == i:
                    choices.append(tuple(x for x in (0, 1, 2) if x & ~own == 0))
                else:
                    choices.append((own,))
            for logs in itertools.product(*choices):
                nodes.add(Node(fault, SignState(facts, logs), (0,)*4, ()))
    return frozenset(nodes)

def signing_alignment():
    kernel = SigningKernel()
    supports = tuple(frozenset(q) for q in itertools.combinations(range(4), 3))
    geometry_checks = 0
    for f in kernel.faults():
        bad = frozenset() if f.effective is None else frozenset((f.effective,))
        assert any(not q & bad for q in supports)
        for q, r in itertools.product(supports, repeat=2):
            assert (q & r) - bad
            geometry_checks += 1
    labels = tuple(str(log)+":"+str(v) for log in (0, 1, 2) for v in (0, 1))
    template = Table(labels, ("boot",), (0,), ((0,)*len(labels),), ((0,)*len(labels),))
    domains, relations, counts = compile_kernel(kernel, signing_envelope(kernel),
                                                (template,)*4, ((0, 1),)*4)
    assert all(len(r.scope) <= 1 for r in relations)
    parents = (-1,) + (0,)*(len(relations)-1)
    assignment, _, passes = join_tree_solve(relations, parents)
    assert assignment is not None
    policies = extract_tables(assignment, (template,)*4, domains)
    for p in policies:
        assert p.outputs[0] == tuple(guard(log, value) for log in (0, 1, 2) for value in (0, 1))
    replay = verify(kernel, policies, full=True)
    assert replay["winning"]
    # Exhaust every actual adversarial signing/forgery continuation during a
    # four-request common-value publication sweep. Receipt choices are then
    # restricted by the separately declared honest-delivery cutoff premise.
    publication_states = guaranteed_receipts = 0
    for fault in kernel.faults():
        for value in (0, 1):
            states = {SignState(0, (0,)*4)}
            for actor in range(4):
                next_states = set()
                for state in states:
                    obs = Observation(tuple(str(state.code_logs[i])+":"+str(value) if i == actor else None
                                            for i in range(4)), (actor, value))
                    issued = tuple(policies[i].react(0, obs.local[i])[0]
                                   if kernel.compliant(fault, i) else None for i in range(4))
                    for outcome in kernel.outcomes(fault, state, obs, issued):
                        assert not outcome.violations
                        next_states.add(outcome.state)
                states = next_states
            mandatory = sum(1 << (2*i+value) for i in range(4) if i != fault.effective)
            for state in states:
                publication_states += 1
                assert mandatory & ~state.facts == 0 and qa.certificate(mandatory, value)
                for receipt in submasks(state.facts):
                    if receipt & mandatory == mandatory:
                        assert qa.certificate(receipt, value)
                        guaranteed_receipts += 1
    # No honest-delivery or common-request premise is smuggled into safety.
    state = SignState(0, (0,)*4)
    fault = RoleFault(3, None)
    for actor, value in ((0, 0), (1, 1), (2, 1), (0, 1), (1, 0), (2, 0)):
        obs = Observation(tuple(str(state.code_logs[i])+":"+str(value) if i == actor else None
                                for i in range(4)), (actor, value))
        issued = tuple(policies[i].react(0, obs.local[i])[0] if kernel.compliant(fault, i) else None
                       for i in range(4))
        state = next(kernel.outcomes(fault, state, obs, issued)).state
        assert not qa.certificate(state.facts, 0) and not qa.certificate(state.facts, 1)
    idle = Observation((None,)*4)
    assert any(o.state == state and not o.delivered for o in kernel.outcomes(fault, state, idle, (None,)*4))
    return {"role_faults": len(tuple(kernel.faults())), "compiled": counts,
            "quorum_supports": [sorted(q) for q in supports],
            "honest_intersection_checks": geometry_checks, "fault_disjoint_availability": True,
            "variables": len(domains), "largest_scope": max(map(lambda r: len(r.scope), relations)),
            "semijoin_passes": passes, "selected_guard": policies[0].outputs,
            "source_replay": replay, "conditional_publication_terminal_states": publication_states,
            "honest_delivery_cutoff_receipts": guaranteed_receipts,
            "conditional_service_bound_request_rounds": 4,
            "unconditional_service_claimed": False, "stall_facts": state.facts,
            "existing_quorum_checks": qa.run_checks()}

@dataclass(frozen=True)
class SourceFault:
    actuator: int
    sensor: int | None

class EvidenceSelection:
    actors = 1
    def __init__(self, view="raw", allowed=(0, 1), probe=False, deadline=1):
        self.view, self.allowed, self.probe, self.deadline = view, tuple(allowed), probe, deadline
    def faults(self):
        return tuple(SourceFault(a, s) for a in (0, 1) for s in (None, 0, 1, 2))
    def compliant(self, fault, actor): return True
    def initials(self, fault): return (Initial(0, ("boot",)),)
    def initial_violations(self, fault, state): return () if state == 0 else ("not_initial_probe_stage",)
    def raw_vectors(self, fault):
        for reports in itertools.product((0, 1), repeat=3):
            if all(s == fault.sensor or reports[s] == fault.actuator for s in range(3)):
                yield reports
    def observations(self, fault, state):
        seen = set()
        for reports in self.raw_vectors(fault):
            if self.probe:
                symbol = "first:"+str(reports[0]) if state == 0 else "full:"+''.join(map(str, reports))
            elif self.view == "raw":
                symbol = ''.join(map(str, reports))
            elif self.view == "majority":
                symbol = str(int(sum(reports) >= 2))
            elif self.view == "first":
                symbol = str(reports[0])
            else:
                symbol = "blind"
            if symbol not in seen:
                seen.add(symbol)
                yield Observation((symbol,), reports)
    def outcomes(self, fault, state, observation, issued):
        action = issued[0]
        if action == 2 and self.probe:
            # Inspection consumes the compliant routing action, but it never
            # suppresses autonomous output from the faulty actuator.
            for hostile in (0, 1):
                outputs = tuple(hostile if i == fault.actuator else 0 for i in (0, 1))
                yield Outcome(1, frozenset(("delivery",)) if hostile else frozenset(), (),
                              {"probe": True, "outputs": outputs, "actual_delivery": hostile})
            return
        if action not in (0, 1):
            yield Outcome(state, frozenset(), ("invalid_command",), {})
            return
        # The intact selected actuator outputs one; the bad actuator may emit
        # zero or one independently of the issued route. No clipping by rights.
        for hostile in (0, 1):
            outputs = tuple(hostile if i == fault.actuator else int(i == action) for i in (0, 1))
            delivery = sum(outputs)
            violations = () if action in self.allowed else ("forbidden_route",)
            yield Outcome(state, frozenset(("delivery",)) if delivery >= 1 else frozenset(),
                          violations, {"outputs": outputs, "actual_delivery": delivery,
                                       "selected": action, "bad_actuator": fault.actuator})
    def service(self, fault): return (("delivery", self.deadline),)
    def recurrent_service(self, fault): return ("delivery",)

def source_hypothesis_pairs(kernel, observations, observed_sources):
    # Component universe: actuator 0/1 and sensor 0/1/2. The nominal
    # actuator constraints bind physical bad-mode x to the same fault f.
    pairs = set()
    for x, f in itertools.product((0, 1), kernel.faults()):
        actuator_constraints = all(x != i for i in (0, 1) if i != f.actuator)
        source_constraints = all(observations[s] == x for s in observed_sources if s != f.sensor)
        if actuator_constraints and source_constraints:
            pairs.add((x, f))
    assert all(x == f.actuator for x, f in pairs)
    return frozenset(pairs)

def evidence_hypotheses(kernel, observations, observed_sources):
    pairs = source_hypothesis_pairs(kernel, observations, observed_sources)
    result = frozenset(f for x, f in pairs)
    direct = frozenset(f for f in kernel.faults()
                       if all(s == f.sensor or observations[s] == f.actuator for s in observed_sources))
    assert result == direct
    return result

def source_scenario_legal(kernel: EvidenceSelection, node: Node, observation: Observation,
                          command: int, envelope: frozenset[Node]):
    """The selected single-planner, memoryless interface at its full scenario."""
    assert kernel.actors == 1 and node.memory == (0,)
    seen = False
    for outcome in kernel.outcomes(node.fault, node.state, observation, (command,)):
        seen = True
        ages = tuple(0 if name in outcome.delivered else age+1
                     for age, (name, _) in zip(node.ages, kernel.service(node.fault)))
        successor = Node(node.fault, outcome.state, node.memory, ages)
        if outcome.violations or successor not in envelope:
            return False
    return seen

def selection_compile(kernel):
    labels = tuple(sorted({o.local[0] for f in kernel.faults() for o in kernel.observations(f, 0)}))
    template = Table(labels, ("boot",), (0,), ((0,)*len(labels),), ((0,)*len(labels),))
    envelope = frozenset(Node(f, 0, (0,), (0,)) for f in kernel.faults())
    domains, relations, counts = compile_kernel(kernel, envelope, (template,), ((0, 1),))
    rows = natural_join(relations)
    return template, domains, relations, rows, counts

def evidence_alignment():
    raw = EvidenceSelection("raw")
    template, domains, relations, rows, counts = selection_compile(raw)
    assert len(rows) == 1
    policy = extract_tables(rows[0], (template,), domains)
    assert verify(raw, policy)["winning"]
    hypothesis_cases = 0
    for reports in itertools.product((0, 1), repeat=3):
        fresh = evidence_hypotheses(raw, reports, (0, 1, 2))
        old = evidence_hypotheses(raw, reports, (0,))
        assert fresh <= old
        assert fresh
        for f in raw.faults():
            if reports in tuple(raw.raw_vectors(f)):
                assert f in fresh
        # The relation intersection is exactly the actual robust service/rights
        # row, with sensor and actuator identities retained in one f.
        envelope = frozenset(Node(f, 0, (0,), (0,)) for f in raw.faults())
        symbol = ''.join(map(str, reports))
        observation = Observation((symbol,), reports)
        robust = {a for a in (0, 1) if all(source_scenario_legal(
                    raw, Node(f, 0, (0,), (0,)), observation, a, envelope) for f in fresh)}
        assert robust == {a for a in (0, 1) if all(a != f.actuator and a in raw.allowed for f in fresh)}
        compiled = {row[0][0] for r in relations if r.scope == ((0, 0, symbol),) for row in r.rows}
        assert robust == compiled == {1-int(sum(reports) >= 2)}
        hypothesis_cases += 1
    majority = EvidenceSelection("majority")
    mt, md, mr, mrows, _ = selection_compile(majority)
    assert len(mrows) == 1
    mp = extract_tables(mrows[0], (mt,), md)
    assert verify(majority, mp)["winning"]
    for symbol in template.observations:
        coarse = str(int(sum(map(int, symbol)) >= 2))
        assert policy[0].react(0, symbol) == mp[0].react(0, coarse)
    assert len(evidence_hypotheses(raw, (0, 0, 0), (0, 1, 2))) == 4
    assert not selection_compile(EvidenceSelection("first"))[3]
    assert not selection_compile(EvidenceSelection("blind"))[3]
    assert not selection_compile(EvidenceSelection("raw", allowed=(0,)))[3]
    # Active acquisition is a different transition: it consumes a service tick.
    probes = {}
    for deadline in (1, 2):
        active = EvidenceSelection(probe=True, deadline=deadline)
        labels = ("first:0", "first:1") + tuple("full:"+''.join(map(str, r))
                                                  for r in itertools.product((0, 1), repeat=3))
        outputs = (2, 2) + tuple(1-int(sum(r) >= 2) for r in itertools.product((0, 1), repeat=3))
        p = Table(labels, ("boot",), (0,), (outputs,), ((0,)*len(labels),))
        probes[str(deadline)] = verify(active, (p,), full=True)
    assert not probes["1"]["winning"] and probes["2"]["winning"]
    # Identical mode/fault/report evidence has different safe next-step rows
    # when its retained service age changes; the mode is not the whole state.
    aged = EvidenceSelection(probe=True, deadline=2)
    f = aged.faults()[0]
    observation = next(iter(aged.observations(f, 1)))
    q = frozenset(Node(fault, stage, (0,), (age,)) for fault in aged.faults()
                  for stage, age in ((0, 0), (1, 0), (1, 1)))
    assert source_scenario_legal(aged, Node(f, 1, (0,), (0,)), observation, f.actuator, q)
    assert not source_scenario_legal(aged, Node(f, 1, (0,), (1,)), observation, f.actuator, q)
    # Reuse the existing calibrated scene mechanism as an actual row witness.
    low = SensorWorld(0, 1, False, True, 1, 1)
    high = SensorWorld(1, 0, False, True, 1, 1)
    bad = SensorWorld(0, 0, False, False, 1, 1)
    def scene_rows(worlds, observe):
        grouped = {}
        for world in worlds:
            symbol = observe(world)
            valid = {u for u in (0, 1) if 0 <= witness_effect(world, u) <= 1}
            grouped[symbol] = grouped.get(symbol, {0, 1}) & valid
        return {str(k): sorted(v) for k, v in grouped.items()}
    without = scene_rows((low, high), lambda w: w.reported)
    witnessed = scene_rows((low, high), lambda w: (w.reported, w.scene_observation()))
    uncalibrated = scene_rows((low, high, bad), lambda w: (w.reported, w.scene_observation()))
    assert any(not v for v in without.values()) and all(witnessed.values()) and any(
        not v for v in uncalibrated.values())
    return {"joint_fault_scenarios": len(raw.faults()), "raw_compile": counts,
            "hypothesis_row_equalities": hypothesis_cases,  "typed_source_hypothesis_pairs_checked": True,
            "legal_predicate_uses_full_source_successors": True,
            "retained_service_age_changes_row": True, "raw_policy": policy[0].outputs,
            "majority_policy": mp[0].outputs, "uncertain_fault_labels_for_000": 4,
            "raw_majority_policy_reflection_scope": "this unique-action finite family only",
            "first_source_only_unrealizable_at_Q": True, "permission_cap_obstruction": True,
            "active_probe": probes, "scene_report_rows": without, "scene_witness_rows": witnessed,
            "scene_missing_calibration_rows": uncalibrated}

DIGITAL_ACTIONS = tuple(sorted(
    {("observe",), ("wait",), ("retain",)} |
    {("propose", b) for b in (1, 2)} |
    {("echo", b) for b in range(4)} |
    {("terminal", b) for b in (1, 2)}, key=repr))
DIGITAL_CODE = {action: i for i, action in enumerate(DIGITAL_ACTIONS)}

@dataclass(frozen=True)
class DigitalFailure:
    origin: digital.Prefix
    issued: tuple[int | None, ...]
    reason: str = "protocol_contract_deviation"

def failure_event(state):
    return {"terminal_failure": state.reason, "fresh_delivery": False,
            "origin_issued": state.issued, "origin_phase": state.origin.phase,
            "origin_epoch": state.origin.epoch}

def digital_verdict(prefix):
    if isinstance(prefix, DigitalFailure):
        return (prefix.reason,)
    bad = []
    if prefix.phase >= 2:
        values = {v for v in prefix.decisions if v is not None}
        if len(values) != 1:
            bad.append("decision_agreement")
        if prefix.faulty != 0 and values != {prefix.input}:
            bad.append("correct_leader_validity")
    if prefix.phase >= 3:
        accepted = set()
        for receipt in prefix.receipts:
            if receipt & ~prefix.terminal_signed:
                bad.append("receipt_without_issuance")
            for value in (0, 1):
                if digital.certificate(receipt, value):
                    accepted.add(value)
                    if any(d is not None and d != value for d in prefix.decisions):
                        bad.append("terminal_certificate_soundness")
        if len(accepted) > 1:
            bad.append("conflicting_receipts")
    if prefix.phase == 4 and not all(
            digital.certificate(receipt, digital.final_value(prefix)) for receipt in prefix.receipts):
        bad.append("missing_cutoff_certificate")
    return tuple(bad)

class DigitalProtocolKernel:
    """Exact source behavior for the imported protocol contract.

    Other compliant instructions enter explicit contract failure, not a
    purported successful physical execution. This is an implementation
    embedding, not synthesis complete for alternative broadcast protocols.
    """
    actors = 5
    def faults(self): return digital.FAULTS
    def compliant(self, fault, actor): return actor != fault
    def initials(self, fault):
        return tuple(Initial(p, ("boot",)*5) for p in digital.initials() if p.faulty == fault)
    def initial_violations(self, fault, state):
        if isinstance(state, DigitalFailure):
            return ("invalid_protocol_initialization", state.reason)
        return () if state.faulty == fault and state.phase == 0 else ("invalid_protocol_initialization",)
    def observations(self, fault, state):
        if isinstance(state, DigitalFailure):
            yield Observation((None,)*self.actors)
            return
        yield Observation(tuple(repr(digital.local_view(state, i)) for i in digital.ACTORS))
    def outcomes(self, fault, state, observation, issued):
        if isinstance(state, DigitalFailure):
            yield Outcome(state, frozenset(), digital_verdict(state), failure_event(state))
            return
        expected = tuple(DIGITAL_CODE[digital.local_action(i, digital.local_view(state, i))]
                         for i in digital.ACTORS)
        if any(issued[i] != expected[i] for i in digital.ACTORS if self.compliant(fault, i)):
            failed = DigitalFailure(state, tuple(issued))
            yield Outcome(failed, frozenset(), digital_verdict(failed),
                          dict(failure_event(failed), issued=tuple(issued)))
            return
        if state.phase == 4:
            yield Outcome(state, frozenset(), digital_verdict(state),
                          {"completed_terminal_stutter": True, "fresh_delivery": False})
            return
        for nxt in digital.successors(state):
            delivered = (("decision",) if nxt.phase == 2 else
                         ("certificate",) if nxt.phase == 4 else ())
            yield Outcome(nxt, frozenset(delivered), digital_verdict(nxt),
                          {"event": nxt.events[-1].kind, "fresh_delivery": bool(delivered)})
    def service(self, fault): return ()
    def recurrent_service(self, fault): return ()

def digital_alignment():
    levels = [list(digital.initials())]
    for _ in range(4):
        levels.append([nxt for before in levels[-1] for nxt in digital.successors(before)])
    kernel = DigitalProtocolKernel()
    universe = frozenset(p for level in levels for p in level)
    assignment = {}
    row_count = transition_count = serialization_events = 0
    kernel_edges = terminal_stutters = deviation_tests = 0
    all_correct_decision_rows = receiver_checks = completed_delivery = 0
    for level in levels:
        for prefix in level:
            scope, row = [], []
            for actor in digital.ACTORS:
                if actor != prefix.faulty:
                    view = digital.local_view(prefix, actor)
                    variable = (actor, 0, repr(view))
                    action = (DIGITAL_CODE[digital.local_action(actor, view)], 0)
                    if variable in assignment:
                        assert assignment[variable] == action
                    assignment[variable] = action
                    scope.append(variable)
                    row.append(action)
            relation = Relation(tuple(scope), frozenset((tuple(row),)))
            assert tuple(assignment[v] for v in relation.scope) in relation.rows
            row_count += 1
            observation = next(iter(kernel.observations(prefix.faulty, prefix)))
            issued = tuple(assignment[(i, 0, observation.local[i])][0]
                           if kernel.compliant(prefix.faulty, i) else None for i in digital.ACTORS)
            expected_posts = {prefix} if prefix.phase == 4 else set(digital.successors(prefix))
            actual_posts = set()
            for outcome in kernel.outcomes(prefix.faulty, prefix, observation, issued):
                assert not outcome.violations and outcome.state in universe
                assert outcome.state.faulty == prefix.faulty
                actual_posts.add(outcome.state)
                kernel_edges += 1
                if prefix.phase == 4:
                    assert not outcome.delivered
                    terminal_stutters += 1
                else:
                    assert outcome.state.phase == prefix.phase + 1
                    assert (4-outcome.state.phase) < (4-prefix.phase)
            assert actual_posts == expected_posts
            # The explicit deviation branch establishes the converse row
            # characterization; no invalid command is silently normalized.
            for i in digital.ACTORS:
                if kernel.compliant(prefix.faulty, i):
                    changed = list(issued)
                    changed[i] = (changed[i]+1) % len(DIGITAL_ACTIONS)
                    bad = tuple(kernel.outcomes(prefix.faulty, prefix, observation, tuple(changed)))
                    assert bad and all("protocol_contract_deviation" in o.violations for o in bad)
                    for failure in bad:
                        assert isinstance(failure.state, DigitalFailure)
                        assert failure.state.origin == prefix and failure.state.issued == tuple(changed)
                        absent = tuple(kernel.observations(prefix.faulty, failure.state))
                        assert len(absent) == 1 and absent[0].local == (None,)*kernel.actors
                        resumed = tuple(kernel.outcomes(prefix.faulty, failure.state, absent[0],
                                                        (None,)*kernel.actors))
                        assert len(resumed) == 1 and resumed[0].state == failure.state
                        assert not resumed[0].delivered and resumed[0].violations == failure.violations
                    deviation_tests += 1
            if prefix.phase >= 2:
                decisions = {d for d in prefix.decisions if d is not None}
                assert len(decisions) == 1
                all_correct_decision_rows += 1
            if prefix.phase >= 3:
                issued = prefix.terminal_signed
                assert exclusive(issued, prefix.faulty, 3)
                accepted = set()
                for receipt in prefix.receipts:
                    assert receipt & ~issued == 0
                    for value in (0, 1):
                        if digital.certificate(receipt, value):
                            assert value == digital.final_value(prefix)
                            accepted.add(value)
                    receiver_checks += 1
                assert len(accepted) <= 1
                if prefix.phase == 4:
                    assert all(digital.certificate(receipt, digital.final_value(prefix))
                               for receipt in prefix.receipts)
                    completed_delivery += 1
            if prefix.phase:
                before = digital.Prefix(prefix.faulty, prefix.input, prefix.epoch, prefix.events[:-1])
                old = before.terminal_signed
                new = prefix.terminal_signed
                assert old & ~new == 0
                replay = old
                for signer, value in digital.tokens(new & ~old):
                    replay = qa.step(replay, prefix.faulty, (signer, value))
                    serialization_events += 1
                assert replay == new
                transition_count += 1
    # Pair supports need D2 agreement; guarded own signatures alone do not suffice.
    r0 = digital.token(0, 0) | digital.token(1, 0)
    r1 = digital.token(0, 1) | digital.token(2, 1)
    broken = digital.Prefix(0, 0, 0, (digital.Event("raw-cutoff", (3, 1, 2)),
                digital.Event("echo-cutoff", (0, 0)), digital.Event("terminal-send", (3, r0, r1))))
    assert digital.certificate(r0, 0) and digital.certificate(r1, 1)
    assert exclusive(broken.terminal_signed, 0, 3)
    assert {d for d in broken.decisions if d is not None} == {0, 1}
    assert broken.events[1] not in {p.events[1] for p in digital.successors(
        digital.Prefix(0, 0, 0, broken.events[:1]))}
    return {"stage_sizes": list(map(len, levels)), "local_variables": len(assignment),
            "closed_program_rows": row_count, "mapped_transitions": transition_count,
            "actual_kernel_edges": kernel_edges, "terminal_stutters_without_service": terminal_stutters,
            "program_deviation_failures_checked": deviation_tests, "command_codebook": DIGITAL_ACTIONS,
            "exact_nonterminal_post_correspondence": True, "completion_rank": "4 minus phase",
            "serialized_terminal_issuance_events": serialization_events,
            "agreement_rows": all_correct_decision_rows, "receipt_checks": receiver_checks,
            "completed_slots_with_actual_certificates": completed_delivery,
            "decision_cutoff_round": 2, "evidence_cutoff_round": 3,
            "terminal_stutters_counted_as_service": False,
            "pair_quorums_require_D2": True, "full_strategy_synthesis_claimed": False}

def core_failure_regression(core_bridge_path):
    """Exercise actual CoreBridge.prepare/profile/core_successors, without a mock."""
    path = Path(core_bridge_path)
    if not path.is_file():
        raise ValueError("CoreBridge source required; pass --core-bridge in an isolated worker")
    spec = importlib.util.spec_from_file_location("alignment_actual_core_bridge", path)
    bridge = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = bridge
    spec.loader.exec_module(bridge)
    source_hash = lambda p: hashlib.sha256(Path(p).read_bytes().replace(bytes((13,10)), bytes((10,)))).hexdigest()
    assert source_hash(bridge.source.__file__) == source_hash(HERE.parent/"enforcement"/"finite_model.py")
    kernel = DigitalProtocolKernel()
    # Cover every fault/input at every protocol phase; these are actual source
    # prefixes, with a single explicit causal continuation chosen per stage.
    prefixes = set()
    for initial in digital.initials():
        current = initial
        prefixes.add(current)
        while current.phase < 4:
            current = next(iter(digital.successors(current)))
            prefixes.add(current)
    labels = [{repr(digital.local_view(p, i)): DIGITAL_CODE[digital.local_action(i, digital.local_view(p, i))]
               for p in prefixes} for i in digital.ACTORS]
    tables = []
    for local in labels:
        observations = tuple(sorted(local))
        row = tuple(local[o] for o in observations)
        tables.append(bridge.source.Table(observations, ("boot",), (0,),
                    (row, row), ((1,)*len(row), (0,)*len(row))))
    tables = tuple(tables)
    initials = bridge.initial_boundaries(kernel, tables)
    assert len(initials) == len(tuple(digital.initials()))
    assert all(not b.violations and b.node.memory == (0,)*5 for b in initials)
    positive_edges = 0
    for boundary in initials:
        profile = bridge.profile(kernel, tables, boundary)
        successors = tuple(bridge.core_successors(kernel, boundary, profile))
        assert {b.node.state for b, _ in successors} == set(digital.successors(boundary.node.state))
        assert all(not b.violations for b, _ in successors)
        positive_edges += len(successors)
    failures = continuations = 0
    for prefix in sorted(prefixes, key=repr):
        node = bridge.source.Node(prefix.faulty, prefix, (0,)*5, ())
        boundary = bridge.prepare(kernel, node)[0]
        good = bridge.profile(kernel, tables, boundary)
        for actor in digital.ACTORS:
            if not kernel.compliant(prefix.faulty, actor):
                continue
            changed = list(good)
            command, memory = changed[actor]
            changed[actor] = ((command+1) % len(DIGITAL_ACTIONS), memory)
            issued, committed = bridge.masks(kernel, boundary, tuple(changed))
            outcomes = tuple(bridge.core_successors(kernel, boundary, tuple(changed)))
            assert len(outcomes) == 1
            failed, event = outcomes[0]
            assert isinstance(failed.node.state, DigitalFailure)
            origin = failed.node.state
            assert origin.origin == prefix and origin.issued == issued
            assert failed.node.fault == prefix.faulty and failed.node.memory == committed
            assert failed.observation.local == (None,)*kernel.actors
            assert origin.reason in failed.violations
            assert failed.previous_effect.issued_compliant == issued
            assert failed.previous_effect.source_violations == (origin.reason,)
            assert not failed.previous_effect.delivered
            assert event["origin_issued"] == issued and event["origin_phase"] == prefix.phase
            assert kernel.initial_violations(prefix.faulty, origin)
            assert digital_verdict(origin) == (origin.reason,)
            hash(failed.node)  # Frozen source Node and failure provenance remain valid keys.
            failures += 1
            for _ in range(3):
                actual = bridge.profile(kernel, tables, failed)
                ghosts = tuple((u+1000, m+31) for u, m in actual)
                assert bridge.masks(kernel, failed, ghosts) == ((None,)*5, committed)
                next_edges = tuple(bridge.core_successors(kernel, failed, ghosts))
                assert len(next_edges) == 1
                nxt, effect = next_edges[0]
                assert nxt.node.state == origin and nxt.node.fault == prefix.faulty
                assert nxt.node.memory == committed and nxt.observation.local == (None,)*5
                assert origin.reason in nxt.violations
                assert not nxt.previous_effect.delivered and not effect["fresh_delivery"]
                assert nxt.previous_effect.issued_compliant == (None,)*5
                assert effect["origin_issued"] == issued
                failed = nxt
                continuations += 1
    return {"core_bridge_sha256_lf": source_hash(path),
            "source_kernel_sha256_lf": source_hash(bridge.source.__file__),
            "api": "initial_boundaries, prepare, profile(kernel,tables,boundary), masks, core_successors",
            "source_prefixes": len(prefixes), "phases": sorted({p.phase for p in prefixes}),
            "positive_initial_macro_edges": positive_edges, "failed_macro_edges": failures,
            "absorbing_macro_edges": continuations, "origin_commands_retained": True,
            "invocation_memory_committed_then_held": True, "all_future_invocations_absent": True,
            "failure_never_delivers_service": True, "immutable_state_keys_checked": True}

def reproduce(core_bridge_path=None):
    path = Path(core_bridge_path) if core_bridge_path is not None else HERE/"core_bridge.py"
    bridge_result = core_failure_regression(path)
    return {"signing": signing_alignment(), "evidence": evidence_alignment(),
            "digital": digital_alignment(), "core_failure_regression": bridge_result}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--write", action="store_true")
    parser.add_argument("--core-bridge", type=Path, default=HERE/"core_bridge.py",
                        help="Actual CoreBridge source; defaults to the adjacent integration module")
    args = parser.parse_args()
    result = reproduce(args.core_bridge)
    names = ("alignment_model.py", "Alignment.lean", "ALIGNMENT.md",
             "structure_model.py", "Structure.lean", "../enforcement/finite_model.py",
             "../research/quorum_alignment.py", "../research/QuorumAlignment.lean",
             "../research/Control.lean", "../research/Evidence.lean",
             "../research/evidence_model.py", "../research/Digital.lean", "../research/digital_model.py")
    result["source_sha256_lf"] = {n: hashlib.sha256((HERE/n).read_bytes().replace(b"\r\n", b"\n")).hexdigest()
                                for n in names}
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    path = HERE / "alignment_results.json"
    if args.write:
        path.write_text(rendered, encoding="utf-8")
    elif not path.exists() or path.read_text(encoding="utf-8") != rendered:
        raise SystemExit("Alignment evidence differs; review before --write")
    print(json.dumps({"verified": True, "signing_variables": result["signing"]["variables"],
                      "digital_rows": result["digital"]["closed_program_rows"],
                      "evidence_faults": result["evidence"]["joint_fault_scenarios"]}))

if __name__ == "__main__":
    main()

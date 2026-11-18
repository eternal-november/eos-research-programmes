"""Exact finite causal checking and bounded local-table synthesis for peer brakes.

Standard library only. Run python finite_model.py --check to reproduce the
committed JSON, or --write to replace it. No solver or random sampling is used.
"""
from __future__ import annotations
import argparse
import hashlib
import itertools
import json
import math
import sys
from collections import Counter, deque
from dataclasses import asdict, dataclass, replace
from pathlib import Path
from typing import Any, Hashable, Iterable, Protocol

if sys.flags.optimize:
    raise RuntimeError('Optimized Python disables required assertions; run without -O/-OO')

@dataclass(frozen=True)
class Table:
    observations: tuple[str, ...]
    initial_symbols: tuple[str, ...]
    initial: tuple[int, ...]
    outputs: tuple[tuple[int, ...], ...]
    updates: tuple[tuple[int, ...], ...]
    def start(self, symbol: str) -> int:
        return self.initial[self.initial_symbols.index(symbol)]
    def react(self, memory: int, observation: str | None) -> tuple[int | None, int]:
        if observation is None:
            return None, memory
        column = self.observations.index(observation)
        return self.outputs[memory][column], self.updates[memory][column]

def local_tables(memory: int, observations: tuple[str, ...], commands: tuple[int, ...],
                 initial_symbols: tuple[str, ...] = ("boot",)) -> Iterable[Table]:
    """All deterministic local tables at this bound; smaller tables can pad."""
    if memory < 1 or not observations or not commands or not initial_symbols:
        raise ValueError("Nonempty finite policy interfaces and positive memory required")
    width = len(observations)
    for initial in itertools.product(range(memory), repeat=len(initial_symbols)):
        for outputs in itertools.product(commands, repeat=memory * width):
            rows = tuple(tuple(outputs[i * width:(i + 1) * width]) for i in range(memory))
            for updates in itertools.product(range(memory), repeat=memory * width):
                next_rows = tuple(tuple(updates[i * width:(i + 1) * width]) for i in range(memory))
                yield Table(observations, initial_symbols, initial, rows, next_rows)

@dataclass(frozen=True)
class Initial:
    state: Hashable
    local_inputs: tuple[str, ...]
    service_ages: tuple[int, ...] | None = None

@dataclass(frozen=True)
class Observation:
    local: tuple[str | None, ...]
    # Private to the plant/checker. Table.react receives only its local symbol.
    # Scalar for a local device; component tuple for the product kernel.
    physical_sample: int | tuple[int, ...] | None = None

@dataclass(frozen=True)
class Outcome:
    state: Hashable
    delivered: frozenset[str]
    violations: tuple[str, ...]
    event: dict[str, Any]

class Kernel(Protocol):
    actors: int
    def faults(self) -> Iterable[Hashable]: ...
    def compliant(self, fault: Hashable, actor: int) -> bool: ...
    def initials(self, fault: Hashable) -> Iterable[Initial]: ...
    def initial_violations(self, fault: Hashable, state: Hashable) -> tuple[str, ...]: ...
    def observations(self, fault: Hashable, state: Hashable) -> Iterable[Observation]: ...
    def outcomes(self, fault: Hashable, state: Hashable, observation: Observation,
                 issued: tuple[int | None, ...]) -> Iterable[Outcome]: ...
    def service(self, fault: Hashable) -> tuple[tuple[str, int], ...]: ...
    def recurrent_service(self, fault: Hashable) -> tuple[str, ...]: ...

@dataclass(frozen=True)
class Node:
    fault: Hashable
    state: Hashable
    memory: tuple[int, ...]
    ages: tuple[int, ...]

def serial(value: Any) -> Any:
    if hasattr(value, "__dataclass_fields__"):
        return {k: serial(v) for k, v in asdict(value).items()}
    if isinstance(value, dict):
        return {str(k): serial(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [serial(v) for v in value]
    if isinstance(value, (set, frozenset)):
        return sorted(serial(v) for v in value)
    return value

def service_free_rank(nodes: list[Node], edges: list[tuple[Node, Node, frozenset[str]]],
                      service: str) -> dict[Node, int] | None:
    """Rank decreases on EVERY service-free edge, not merely bottom SCCs."""
    adjacency = {node: set() for node in nodes}
    for src, dst, delivered in edges:
        if service not in delivered:
            adjacency[src].add(dst)
    indegree = {node: 0 for node in nodes}
    for successors in adjacency.values():
        for dst in successors:
            indegree[dst] += 1
    ready = deque(node for node in nodes if indegree[node] == 0)
    order = []
    while ready:
        node = ready.popleft()
        order.append(node)
        for dst in sorted(adjacency[node], key=repr):
            indegree[dst] -= 1
            if indegree[dst] == 0:
                ready.append(dst)
    if len(order) != len(nodes):
        return None
    rank = {}
    for node in reversed(order):
        rank[node] = max((rank[dst] + 1 for dst in adjacency[node]), default=0)
    return rank

def verify(kernel: Kernel, policies: tuple[Table, ...], *, recurrent: bool = True,
           full: bool = False) -> dict[str, Any]:
    """Universal finite checking. Missing kernel continuations are losing.

    Every admitted causal outcome must be enumerated by the kernel. An admitted
    primitive move with no outcome must be an explicit violation Outcome; an
    entirely empty observation/effect iterator is caught here as deadlock.
    """
    if len(policies) != kernel.actors:
        raise ValueError("One fixed local table is required for every executor")
    parents: dict[Node, tuple[Node, dict[str, Any]] | None] = {}
    queue: deque[Node] = deque()
    by_fault: Counter[str] = Counter()
    edge_count = 0
    edges: list[tuple[Node, Node, frozenset[str]]] = []
    digest = hashlib.sha256()
    maxima: dict[str, int] = {}
    examples: dict[str, Any] = {}

    def failure(reason: tuple[str, ...], node: Node | None, event: dict | None = None) -> dict:
        trace = []
        current = node
        while current is not None and parents.get(current) is not None:
            previous, edge = parents[current]
            trace.append({"before": serial(previous.state), "event": edge,
                          "after": serial(current.state)})
            current = previous
        trace.reverse()
        if event is not None:
            trace.append({"before": serial(node.state) if node else None, "event": event})
        return {"winning": False, "violations": list(reason),
                "fault": serial(node.fault) if node else None,
                "initial_state": serial(current.state) if current else None,
                "trace": trace, "explored_states": len(parents), "checked_edges": edge_count}

    faults = tuple(kernel.faults())
    if not faults:
        return failure(("empty_fault_family",), None)
    if not recurrent and any(kernel.recurrent_service(f) for f in faults):
        raise ValueError("Cannot suppress declared recurring-service obligations")
    unbounded_recurrence = {f: tuple(name for name in kernel.recurrent_service(f)
                                  if name not in {n for n, _ in kernel.service(f)}) for f in faults}
    for fault in faults:
        initial_states = tuple(kernel.initials(fault))
        if not initial_states:
            return failure(("empty_initial_family",), None, {"fault": serial(fault)})
        for initial in initial_states:
            if len(initial.local_inputs) != kernel.actors:
                raise ValueError("Initial information must be supplied for each actor")
            bad = kernel.initial_violations(fault, initial.state)
            contracts = kernel.service(fault)
            ages = initial.service_ages if initial.service_ages is not None else tuple(0 for _ in contracts)
            if len(ages) != len(contracts):
                raise ValueError("Initial service ages must match service obligations")
            if any(deadline < 1 or not 0 <= age < deadline for age, (_, deadline) in zip(ages, contracts)):
                bad += ("invalid_initial_service_age",)
            node = Node(fault, initial.state,
                        tuple(p.start(j) for p, j in zip(policies, initial.local_inputs)),
                        ages)
            if node not in parents:
                parents[node] = None
                queue.append(node)
            if bad:
                return failure(bad, node)
    while queue:
        node = queue.popleft()
        by_fault[repr(node.fault)] += 1
        for attr in ("x", "heat"):
            if hasattr(node.state, attr):
                maxima[attr] = max(maxima.get(attr, 0), getattr(node.state, attr))
        seen_observation = False
        for observation in kernel.observations(node.fault, node.state):
            seen_observation = True
            if len(observation.local) != kernel.actors:
                raise ValueError("One local observation slot per actor is required")
            issued, memories = [], []
            for i, table in enumerate(policies):
                if kernel.compliant(node.fault, i):
                    command, memory = table.react(node.memory[i], observation.local[i])
                else:
                    command, memory = None, node.memory[i]
                issued.append(command)
                memories.append(memory)
            seen_outcome = False
            for outcome in kernel.outcomes(node.fault, node.state, observation, tuple(issued)):
                seen_outcome = True
                edge_count += 1
                bad = list(outcome.violations)
                ages = []
                for age, (name, deadline) in zip(node.ages, kernel.service(node.fault)):
                    if deadline < 1:
                        raise ValueError("Service deadline must be positive")
                    next_age = 0 if name in outcome.delivered else age + 1
                    ages.append(next_age)
                    if next_age >= deadline:
                        bad.append("actual_service_deadline:" + name)
                if bad:
                    return failure(tuple(sorted(set(bad))), node, outcome.event)
                successor = Node(node.fault, outcome.state, tuple(memories), tuple(ages))
                if full:
                    digest.update(repr((node, observation.local, tuple(issued), successor,
                                        sorted(outcome.delivered))).encode("utf-8"))
                    labels = tuple(x for x in observation.local if x is not None)
                    if len(set(labels)) > 1 and "differing_local_labels" not in examples:
                        examples["differing_local_labels"] = outcome.event
                    if outcome.event.get("faulty_engagement_without_command") and "faulty_engagement" not in examples:
                        examples["faulty_engagement"] = outcome.event
                    if outcome.event.get("delayed_engagement_below_authorization_state") and "delayed_authorized_engagement" not in examples:
                        examples["delayed_authorized_engagement"] = outcome.event
                if recurrent and unbounded_recurrence[node.fault]:
                    edges.append((node, successor, outcome.delivered))
                if successor not in parents:
                    parents[successor] = (node, outcome.event)
                    queue.append(successor)
            if not seen_outcome:
                return failure(("no_effect_continuation",), node, {"observation": serial(observation)})
        if not seen_observation:
            return failure(("no_observation_continuation",), node)
    ranks = {}
    if recurrent:
        for fault in faults:
            selected = [n for n in parents if n.fault == fault]
            selected_edges = [e for e in edges if e[0].fault == fault]
            for name in kernel.recurrent_service(fault):
                bounded = {n: (i, d) for i, (n, d) in enumerate(kernel.service(fault))}
                if name in bounded:
                    index, deadline = bounded[name]
                    ranks[repr(fault) + ":" + name] = max(
                        (deadline - 1 - n.ages[index] for n in selected), default=0)
                    continue
                rank = service_free_rank(selected, selected_edges, name)
                if rank is None:
                    return {"winning": False, "violations": ["service_free_cycle:" + name],
                            "fault": serial(fault), "explored_states": len(parents),
                            "checked_edges": edge_count}
                ranks[repr(fault) + ":" + name] = max(rank.values(), default=0)
    result = {"winning": True, "explored_states": len(parents), "checked_edges": edge_count,
              "fault_classes": len(faults), "reachable_maxima": maxima}
    if full:
        result.update({"edge_sha256": digest.hexdigest(), "states_by_fault": dict(sorted(by_fault.items())),
                       "semantic_witnesses": examples})
    if recurrent:
        result["service_free_rank_maxima"] = ranks
    return result

@dataclass(frozen=True)
class BrakeFault:
    motor_bad: bool
    planner: tuple[int, ...] = ()
    actuator: tuple[int, ...] = ()

@dataclass(frozen=True)
class BrakeState:
    x: int
    heat: int
    pending: tuple[tuple[int, ...], ...]
    samples: tuple[int, ...]

@dataclass(frozen=True)
class BrakeConfig:
    actors: int = 3
    fault_budget: int = 1
    motor_good: int = 4
    motor_bad_max: int = 6
    force_numerator: int = 10
    effect_delay: int = 1
    sensor_delay: int = 0
    observation: str = "local"
    label_threshold: int = 3
    error_bound: int = 1
    conduct_threshold: int = 2
    prohibit_on: bool = False
    brake_channel: bool = True
    fault_engagement_max: int = 1
    safety_limit: int = 10
    heat_limit: int = 6

class PeerBrakes:
    """Integer physical subfamily; independently commanded and faultable brakes."""
    def __init__(self, config: BrakeConfig = BrakeConfig()):
        if config.effect_delay < 1 or config.sensor_delay < 0 or config.force_numerator < 0:
            raise ValueError("Positive effect delay and nonnegative force required")
        if config.observation not in ("local", "blind", "exact"):
            raise ValueError("Unknown observation interface")
        self.config = config
        self.actors = config.actors
        self.x_cap = 2 * max(config.motor_good, config.motor_bad_max)
        max_engagement = config.actors + config.fault_budget * max(0, config.fault_engagement_max - 1)
        self.heat_cap = max(config.heat_limit, (max_engagement * self.x_cap + 4) // 5)
    def faults(self):
        c = self.config
        for motor_bad in (False, True):
            for roles in itertools.product(range(4), repeat=c.actors):
                if sum(role != 0 for role in roles) <= c.fault_budget:
                    yield BrakeFault(motor_bad, tuple(i for i, r in enumerate(roles) if r & 1),
                                     tuple(i for i, r in enumerate(roles) if r & 2))
    def compliant(self, fault, actor):
        return actor not in fault.planner
    def initials(self, fault):
        c = self.config
        for x in range(0 if fault.motor_bad else 1, 5):
            for heat in range(c.heat_limit + 1):
                yield Initial(BrakeState(x, heat, ((0,) * c.actors,) * c.effect_delay,
                                         (x,) * c.sensor_delay), ("boot",) * c.actors)
    def initial_violations(self, fault, state):
        bad = []
        if state.x > self.config.safety_limit:
            bad.append("world_speed")
        if state.heat > self.config.heat_limit:
            bad.append("world_heat")
        if not fault.motor_bad and state.x < 1:
            bad.append("normal_motor_service_floor")
        return tuple(bad)
    def observations(self, fault, state):
        c = self.config
        sample = state.samples[0] if c.sensor_delay else state.x
        if c.observation == "blind":
            labels = ("blind",)
        elif c.observation == "exact":
            labels = (str(sample),)
        else:
            labels = tuple(label for label, possible in (
                ("low", sample - c.error_bound < c.label_threshold),
                ("high", sample + c.error_bound >= c.label_threshold)) if possible)
        for local in itertools.product(labels, repeat=c.actors):
            yield Observation(local, sample)
    def outcomes(self, fault, state, observation, issued):
        c = self.config
        command_choices = [(0, 1) if i in fault.planner else (issued[i],) for i in range(c.actors)]
        for commands in itertools.product(*command_choices):
            if any(command is None for command in commands):
                yield Outcome(state, frozenset(), ("missing_compliant_invocation",), {})
                continue
            if any(command not in (0, 1) for command in commands):
                raise ValueError("Peer-brake issued commands must be binary")
            pending_actual = state.pending[0]
            engagement_choices = [
                tuple(range(c.fault_engagement_max + 1)) if i in fault.actuator
                else (pending_actual[i],) for i in range(c.actors)]
            for engagements in itertools.product(*engagement_choices):
                actual = engagements if c.brake_channel else (0,) * c.actors
                total = sum(actual)
                motor_values = range(c.motor_bad_max + 1) if fault.motor_bad else (c.motor_good,)
                for motor in motor_values:
                    x_next = max(0, (5 * state.x + 10 * motor - c.force_numerator * total) // 10)
                    heat_next = (5 * state.heat + total * state.x) // 10
                    if x_next > self.x_cap or heat_next > self.heat_cap:
                        raise AssertionError("Derived carrier failed; never clip a violation")
                    samples = state.samples[1:] + (state.x,) if c.sensor_delay else ()
                    successor = BrakeState(x_next, heat_next, state.pending[1:] + (commands,), samples)
                    bad = list(self.initial_violations(fault, successor))
                    for i, command in enumerate(commands):
                        if i not in fault.planner and command == 1:
                            if c.prohibit_on or state.x < c.conduct_threshold:
                                bad.append("honest_issued_response:" + str(i))
                    deliveries = (0, x_next) if fault.motor_bad and x_next else (x_next,)
                    for delivered in deliveries:
                        event = {"sample_x": observation.physical_sample,
                                 "invocation_x": state.x,
                                 "labels": list(observation.local), "issued": list(commands),
                                 "pending_applied": list(pending_actual), "actual_engagement": list(actual),
                                 "motor_input": motor, "x_next": x_next, "heat_next": heat_next,
                                 "actual_delivery": delivered,
                                 "faulty_engagement_without_command": any(
                                     i in fault.actuator and actual[i] and not pending_actual[i]
                                     for i in range(c.actors)),
                                 "delayed_engagement_below_authorization_state": state.x < c.conduct_threshold
                                 and any(actual[i] and i not in fault.actuator and i not in fault.planner
                                         for i in range(c.actors))}
                        yield Outcome(successor, frozenset(("target",)) if delivered >= 1 else frozenset(),
                                      tuple(bad), event)
    def service(self, fault):
        return () if fault.motor_bad else (("target", 1),)
    def recurrent_service(self, fault):
        return () if fault.motor_bad else ("target",)

def threshold_policy(actors=3, observation="local", threshold=3, x_cap=12):
    labels = ("low", "high") if observation == "local" else (
        ("blind",) if observation == "blind" else tuple(str(x) for x in range(x_cap + 1)))
    outputs = (0, 1) if observation == "local" else (
        (0,) if observation == "blind" else tuple(int(x >= threshold) for x in range(x_cap + 1)))
    table = Table(labels, ("boot",), (0,), (outputs,), ((0,) * len(labels),))
    return (table,) * actors

def synthesize_memoryless(kernel: PeerBrakes):
    labels = ("low", "high") if kernel.config.observation == "local" else ("blind",)
    candidates = tuple(local_tables(1, labels, (0, 1)))
    winners, failures = [], Counter()
    examined = 0
    for policies in itertools.product(candidates, repeat=kernel.actors):
        examined += 1
        result = verify(kernel, policies)
        if result["winning"]:
            winners.append([list(p.outputs[0]) for p in policies])
        else:
            failures[";".join(result["violations"])] += 1
    return {"local_memory_bound": 1, "observations": list(labels),
            "command_alphabet": [0, 1], "examined": examined, "winners": winners,
            "rejections": dict(sorted(failures.items()))}


@dataclass(frozen=True)
class ProductFault:
    components: tuple[BrakeFault, ...]

class ProductPeerBrakes:
    """Exact independent-device product, retaining one correlated joint fault.

    Separate heat stores are summed; this is not a shared-basin dynamics model.
    Ownership correlations may restrict faults(), but never enlarge a projection
    beyond the local bound used by its certificate.
    """
    def __init__(self, devices: int, bad_motors: int):
        if not 0 <= bad_motors < devices:
            raise ValueError("Aggregate positive service needs fewer bad motors than devices")
        self.devices, self.bad_motors = devices, bad_motors
        self.local = PeerBrakes()
        self.actors = devices * self.local.actors
    def faults(self):
        local_faults = tuple(self.local.faults())
        for components in itertools.product(local_faults, repeat=self.devices):
            if sum(f.motor_bad for f in components) <= self.bad_motors:
                yield ProductFault(components)
    def compliant(self, fault, actor):
        device, local_actor = divmod(actor, self.local.actors)
        return self.local.compliant(fault.components[device], local_actor)
    def initials(self, fault):
        for items in itertools.product(*(tuple(self.local.initials(f)) for f in fault.components)):
            yield Initial(tuple(item.state for item in items),
                          tuple(j for item in items for j in item.local_inputs))
    def initial_violations(self, fault, state):
        bad = [str(i) + ":" + v for i, (f, x) in enumerate(zip(fault.components, state))
               for v in self.local.initial_violations(f, x)]
        if sum(x.heat for x in state) > self.devices * self.local.config.heat_limit:
            bad.append("aggregate_heat")
        return tuple(bad)
    def observations(self, fault, state):
        # Product observations are carried privately; no table receives the tuple.
        for observations in itertools.product(*(tuple(self.local.observations(f, x))
                                                 for f, x in zip(fault.components, state))):
            yield Observation(tuple(o for obs in observations for o in obs.local),
                              tuple(obs.physical_sample for obs in observations))
    def outcomes(self, fault, state, observation, issued):
        width = self.local.actors
        component_outcomes = []
        for i, (f, x) in enumerate(zip(fault.components, state)):
            obs = Observation(observation.local[i * width:(i + 1) * width],
                              observation.physical_sample[i])
            component_outcomes.append(tuple(self.local.outcomes(
                f, x, obs, issued[i * width:(i + 1) * width])))
        for items in itertools.product(*component_outcomes):
            next_state = tuple(item.state for item in items)
            delivered = sum(item.event["actual_delivery"] for item in items)
            heat_sum = sum(x.heat for x in next_state)
            bad = tuple(str(i) + ":" + v for i, item in enumerate(items) for v in item.violations)
            if heat_sum > self.devices * self.local.config.heat_limit:
                bad += ("aggregate_heat",)
            event = {"components": [item.event for item in items],
                     "aggregate_delivery": delivered, "aggregate_heat": heat_sum}
            yield Outcome(next_state,
                          frozenset(("aggregate",)) if delivered >= self.devices - self.bad_motors else frozenset(),
                          bad, event)
    def service(self, fault):
        return (("aggregate", 1),)
    def recurrent_service(self, fault):
        return ("aggregate",)

def product_certificate(local_result):
    """Construct a product closure certificate; do not enumerate its full graph."""
    if not local_result["winning"]:
        raise ValueError("A losing component cannot discharge the product certificate")
    product = ProductPeerBrakes(2, 1)
    local_faults = tuple(product.local.faults())
    counts = local_result["states_by_fault"]
    joint_count = 0
    product_state_upper_bound = 0
    projected_profiles = 0
    for fault in product.faults():
        joint_count += 1
        assert all(f in local_faults for f in fault.components)
        product_state_upper_bound += math.prod(counts[repr(f)] for f in fault.components)
        # A deterministic boundary probe exercises every projected fault class.
        state = tuple(BrakeState(4, 6, ((0, 0, 0),), ()) for _ in fault.components)
        obs = next(iter(product.observations(fault, state)))
        issued = tuple(1 if product.compliant(fault, i) else None for i in range(product.actors))
        for result in product.outcomes(fault, state, obs, issued):
            projected_profiles += 1
            assert not result.violations
            assert "aggregate" in result.delivered
            assert result.event["aggregate_heat"] == sum(x.heat for x in result.state)
            assert result.event["aggregate_delivery"] == sum(
                e["actual_delivery"] for e in result.event["components"])
            for j, f in enumerate(fault.components):
                event = result.event["components"][j]
                assert result.state[j].x == event["x_next"]
                assert result.state[j].heat == event["heat_next"]
                if not f.motor_bad:
                    assert event["actual_delivery"] >= 1
    return {"construction": "union over one joint f of Cartesian products of verified local closed sets",
            "theorem_parameters": "M>=2, 0<=p<M; each planner/actuator union projection has at most one faulty brake",
            "actual_delivery_lower_bound_per_tick": "M-p",
            "aggregate_separate_heat_bound": "6*M",
            "checked_instance": {"M": 2, "p": 1, "joint_fault_classes": joint_count,
                                 "cartesian_certificate_state_upper_bound": product_state_upper_bound,
                                 "boundary_effect_profiles_checked": projected_profiles},
            "full_global_graph_enumerated": False,
            "scope": "independent physical devices and separate heat stores; arbitrary fault correlations respecting each projection are covered"}


def check_sensor_quotient():
    checks = 0
    for x in range(13):
        permitted = set()
        for corrupt_index in (None, 0, 1, 2):
            choices = [range(x - 1, x + 2)] * 3
            if corrupt_index is not None:
                choices[corrupt_index] = (-100, x - 1, x, x + 1, 100)
            for reports in itertools.product(*choices):
                median = sorted(reports)[1]
                assert x - 1 <= median <= x + 1
                permitted.add("high" if median >= 3 else "low")
                checks += 1
        expected = {label for label, ok in (("low", x <= 3), ("high", x >= 2)) if ok}
        assert permitted == expected
    return {"checked_report_vectors": checks, "exact_label_relation": "low iff possible x<=3; high iff possible x>=2",
            "scope": "finite extreme-report checks supplement the order-statistic proof; arbitrary integer reports are proved, not enumerated"}

def generic_regressions():
    class Broken(PeerBrakes):
        def observations(self, fault, state):
            return iter(())
    failed = verify(Broken(), threshold_policy())
    assert not failed["winning"] and failed["violations"] == ["no_observation_continuation"]
    table = Table(("tick",), ("boot",), (1,), ((0,), (0,)), ((1,), (0,)))
    assert table.react(1, None) == (None, 1)
    class Aged(PeerBrakes):
        def faults(self):
            return (BrakeFault(False),)
        def initials(self, fault):
            yield Initial(BrakeState(4, 0, ((0, 0, 0),), ()), ("boot",) * 3, (1,))
        def service(self, fault):
            return (("target", 2),)
        def outcomes(self, fault, state, observation, issued):
            yield Outcome(state, frozenset(), (), {"actual_delivery": 0})
    aged = verify(Aged(), threshold_policy())
    assert not aged["winning"] and aged["violations"] == ["actual_service_deadline:target"]
    a = Node("test", "a", (), ())
    b = Node("test", "b", (), ())
    assert service_free_rank([a, b], [(a, a, frozenset()), (a, b, frozenset(("s",))),
                                           (b, b, frozenset(("s",)))], "s") is None
    rank = service_free_rank([a, b], [(a, b, frozenset()), (b, a, frozenset(("s",)))], "s")
    assert rank is not None and rank[a] > rank[b]
    return {"missing_continuation_loses": True, "absent_invocation_does_not_tick_local_memory": True,
            "nonbottom_service_free_cycle_rejected": True, "service_free_rank_checked": True, "preexisting_service_age_preserved": True}


def stale_information_witness():
    """Replay matched histories; universality is supplied by FINITE.md's proof."""
    kernel = PeerBrakes(replace(BrakeConfig(), sensor_delay=2))
    fault = BrakeFault(True)
    quiet = attack = BrakeState(0, 0, ((0, 0, 0),), (0, 0))
    prefix = []

    def transition(state, labels, commands, motor):
        observation = Observation(labels, state.samples[0])
        assert observation in tuple(kernel.observations(fault, state))
        return next(result for result in kernel.outcomes(fault, state, observation, commands)
                    if result.event["motor_input"] == motor and result.event["actual_delivery"] == 0)

    for tick, motor in enumerate((4, 6, 6)):
        assert quiet.x == 0
        assert quiet.samples[0] == attack.samples[0] == 0
        labels, commands = ("low",) * 3, (0,) * 3
        q = transition(quiet, labels, commands, 0)
        a = transition(attack, labels, commands, motor)
        assert not q.violations and not a.violations
        prefix.append({"tick": tick, "quiet_before": serial(quiet), "attack_before": serial(attack),
                       "common_local_labels": list(labels), "forced_common_commands": list(commands),
                       "quiet_event": q.event, "attack_event": a.event})
        quiet, attack = q.state, a.state
    assert attack.x == 10 and attack.samples[0] == 4 and attack.pending[0] == (0, 0, 0)
    endings = []
    for commands in itertools.product((0, 1), repeat=3):
        result = transition(attack, ("high",) * 3, commands, 6)
        assert result.state.x == 11 and result.violations == ("world_speed",)
        endings.append(result.event)

    # Reach an old-high/current-zero case under the threshold policy. Its next
    # ON command is forbidden by the unchanged current-invocation conduct law.
    state = BrakeState(4, 0, ((0, 0, 0),), (4, 4))
    deceleration = []
    for motor in (2, 0):
        result = transition(state, ("high",) * 3, (1,) * 3, motor)
        assert not result.violations
        deceleration.append({"before": serial(state), "event": result.event})
        state = result.state
    assert state.x == 0 and state.samples[0] == 4
    failure = transition(state, ("high",) * 3, (1,) * 3, 0)
    assert failure.violations == tuple("honest_issued_response:" + str(i) for i in range(3))
    deceleration.append({"before": serial(state), "event": failure.event,
                         "violations": list(failure.violations)})
    return {"fault": serial(fault), "matched_prefix": prefix,
            "attack_endings_all_eight_current_commands": endings,
            "argument": "Current-zero quiet world forces OFF under universal conduct; matching delayed observations transfer those commands through tick two. At tick three every command arrives after the unsafe effect.",
            "stale_high_current_zero_conduct_regression": deceleration}


def reproduce():
    base = BrakeConfig()
    policy = threshold_policy()
    model = PeerBrakes(base)
    positive = verify(model, policy, full=True, recurrent=True)
    assert positive["winning"]
    synthesis = synthesize_memoryless(model)
    assert synthesis["examined"] == 64
    variants = {
        "brakes_removed": replace(base, brake_channel=False),
        "zero_counterforce_with_heat_retained": replace(base, force_numerator=0),
        "stale_observation_two_ticks": replace(base, sensor_delay=2),
        "effect_delay_three_ticks": replace(base, effect_delay=3),
        "forbidden_correct_engagement": replace(base, prohibit_on=True),
        "overpowered_faulty_enforcer": replace(base, fault_engagement_max=10),
    }
    comparisons = {}
    for name, config in variants.items():
        result = verify(PeerBrakes(config), policy)
        assert not result["winning"], name
        comparisons[name] = {"changed_parameters": {k: v for k, v in asdict(config).items()
                                                      if v != asdict(base)[k]}, "result": result}
    always_on = (Table(("low", "high"), ("boot",), (0,), ((1, 1),), ((0, 0),)),) * 3
    comparisons["always_on"] = {"result": verify(model, always_on)}
    assert any("honest_issued_response" in v for v in comparisons["always_on"]["result"]["violations"])
    weak_force = verify(PeerBrakes(replace(base, force_numerator=2)), policy)
    assert weak_force["winning"]
    endpoint_force = verify(PeerBrakes(replace(base, force_numerator=1)), policy)
    assert endpoint_force["winning"]
    comparisons["minimum_positive_integer_force_wins"] = {
        "changed_parameters": {"force_numerator": 1}, "result": endpoint_force}
    comparisons["weaker_positive_force_still_wins"] = {
        "changed_parameters": {"force_numerator": 2},
        "result": weak_force,
        "interpretation": "integer floor changes the real-valued insufficient-force boundary"}
    class CapabilityCut(PeerBrakes):
        def faults(self):
            return (BrakeFault(True, (), (0, 1, 2)),)
    cut = CapabilityCut(replace(base, fault_budget=3, observation="exact"))
    cut_result = verify(cut, threshold_policy(observation="exact"))
    assert not cut_result["winning"]
    comparisons["all_actuators_faulty_with_exact_information"] = {
        "changed_parameters": {"fault_budget": 3, "observation": "exact"},
        "fault_restriction": "bad motor; all three actuators faulty; planners correct",
        "result": cut_result}
    heat_model = PeerBrakes(replace(base, fault_engagement_max=10))
    heat_fault = BrakeFault(True, (), (2,))
    heat_state = BrakeState(4, 6, ((0, 0, 0),), ())
    heat_obs = Observation(("high",) * 3, 4)
    heat_witness = next(o for o in heat_model.outcomes(heat_fault, heat_state, heat_obs, (1, 1, 1))
                        if "world_heat" in o.violations)
    comparisons["global_heat_rights_witness"] = {
        "fault": serial(heat_fault), "admitted_initial_state": serial(heat_state),
        "resulting_state": serial(heat_witness.state), "event": heat_witness.event,
        "violations": list(heat_witness.violations),
        "scope": "overpowered-enforcer comparison; actual effect retained despite rights violation"}
    blind_synthesis = synthesize_memoryless(PeerBrakes(replace(base, observation="blind")))
    assert not blind_synthesis["winners"]
    forbidden_synthesis = synthesize_memoryless(PeerBrakes(replace(base, prohibit_on=True)))
    assert not forbidden_synthesis["winners"]
    class HealthyOnly(PeerBrakes):
        def faults(self):
            return (f for f in super().faults() if not f.motor_bad)
    routine = verify(HealthyOnly(replace(base, brake_channel=False)), policy)
    assert routine["winning"]
    return {"format": 1, "model": "finite integer delayed peer brakes", "parameters": asdict(base),
            "conduct_binding": "honest-issued ON requires current invocation speed >= conduct_threshold; observation age does not change this law",
            "physical_carrier": {"speed_cap": model.x_cap, "heat_cap": model.heat_cap,
                                 "caps_are_proved_carrier_bounds_not_safety_clipping": True},
            "sensor_quotient": check_sensor_quotient(), "generic_regressions": generic_regressions(),
            "positive_policy": [list(p.outputs[0]) for p in policy], "positive": positive,
            "product_certificate": product_certificate(positive),
            "bounded_synthesis": synthesis, "blind_bounded_synthesis": blind_synthesis,
            "forbidden_bounded_synthesis": forbidden_synthesis,
            "routine_healthy_service_without_brakes": routine, "comparisons": comparisons,
            "stale_information_causal_obstruction": stale_information_witness()}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--check", action="store_true")
    group.add_argument("--write", action="store_true")
    group.add_argument("--quick", action="store_true")
    args = parser.parse_args()
    if args.quick:
        print(json.dumps(verify(PeerBrakes(), threshold_policy(), full=True), indent=2, sort_keys=True))
        return
    result = reproduce()
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    output = Path(__file__).with_name("finite_results.json")
    if args.write:
        output.write_text(rendered, encoding="utf-8", newline="\n")
        print("Wrote " + str(output))
    else:
        if output.read_text(encoding="utf-8") != rendered:
            raise SystemExit("FAIL: finite_results.json differs from exhaustive reproduction")
        print("PASS: exact exhaustive results reproduced")
    print(json.dumps({"positive_states": result["positive"]["explored_states"],
                      "positive_edges": result["positive"]["checked_edges"],
                      "memoryless_winners": len(result["bounded_synthesis"]["winners"]),
                      "blind_memoryless_winners": len(result["blind_bounded_synthesis"]["winners"])},
                     sort_keys=True))

if __name__ == "__main__":
    main()

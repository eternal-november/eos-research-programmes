"""Joint-fault local-policy constraints and checked join-tree extraction.

Only the standard library is used. --check reproduces the committed evidence;
--write refreshes it. No source model is changed. Run without Python optimization.
"""
from __future__ import annotations
import argparse
from dataclasses import dataclass
import hashlib
import itertools
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "enforcement"))
from finite_model import (Kernel, Node, Table, Observation, Initial, Outcome,
                          BrakeState, BrakeFault, ProductFault, PeerBrakes, ProductPeerBrakes, verify)

if sys.flags.optimize:
    raise RuntimeError("Checks require Python without -O/-OO")

@dataclass(frozen=True)
class Relation:
    scope: tuple
    rows: frozenset

def agrees(left, lscope, right, rscope):
    return all(left[lscope.index(v)] == right[rscope.index(v)]
               for v in set(lscope) & set(rscope))

def semijoin(left, right):
    common = tuple(v for v in left.scope if v in right.scope)
    li = tuple(left.scope.index(v) for v in common)
    ri = tuple(right.scope.index(v) for v in common)
    index = {tuple(row[k] for k in ri) for row in right.rows}
    return Relation(left.scope, frozenset(row for row in left.rows
                    if tuple(row[k] for k in li) in index))

def natural_join(relations):
    """Independent exhaustive oracle for small regression instances."""
    results = [dict()]
    for rel in relations:
        next_results = []
        for old in results:
            for row in sorted(rel.rows, key=repr):
                new = dict(zip(rel.scope, row))
                if all(old[v] == new[v] for v in old.keys() & new.keys()):
                    next_results.append(old | new)
        results = next_results
    return results

def checked_tree(scopes, parents):
    if not scopes or len(scopes) != len(parents) or parents[0] != -1:
        raise ValueError("Nonempty rooted bag list required")
    for i, scope in enumerate(scopes):
        if len(set(scope)) != len(scope):
            raise ValueError("Repeated variable in bag")
        if i and not 0 <= parents[i] < i:
            raise ValueError("Parents must precede children")
    # Equivalent running-intersection test in this root-first order.
    previous = set(scopes[0])
    for i in range(1, len(scopes)):
        if not (set(scopes[i]) & previous) <= set(scopes[parents[i]]):
            raise ValueError("Bag tree violates running intersection")
        previous.update(scopes[i])

def join_tree_solve(relations, parents, *, prefer_last=False):
    checked_tree([r.scope for r in relations], parents)
    reduced = list(relations)
    passes = 0
    for child in range(len(reduced)-1, 0, -1):
        parent = parents[child]
        reduced[parent] = semijoin(reduced[parent], reduced[child])
        passes += 1
    for child in range(1, len(reduced)):
        parent = parents[child]
        reduced[child] = semijoin(reduced[child], reduced[parent])
        passes += 1
    if not reduced[0].rows:
        return None, reduced, passes
    roots = sorted(reduced[0].rows, key=repr)
    chosen = [roots[-1] if prefer_last else roots[0]]
    assignment = dict(zip(reduced[0].scope, chosen[0]))
    for child in range(1, len(reduced)):
        parent = parents[child]
        row = next(row for row in sorted(reduced[child].rows, key=repr)
                   if agrees(row, reduced[child].scope, chosen[parent], reduced[parent].scope))
        chosen.append(row)
        for variable, value in zip(reduced[child].scope, row):
            if variable in assignment:
                assert assignment[variable] == value
            assignment[variable] = value
    assert all(tuple(assignment[v] for v in r.scope) in r.rows for r in relations)
    return assignment, reduced, passes

def bag_relations(constraints, domains, bags, parents):
    """Exact tree-decomposition compilation; bag width is reported, not hidden."""
    checked_tree(bags, parents)
    assigned = [[] for _ in bags]
    for relation in constraints:
        target = next((i for i, bag in enumerate(bags) if set(relation.scope) <= set(bag)), None)
        if target is None:
            raise ValueError("A constraint is not covered by any bag")
        assigned[target].append(relation)
    if set(domains) != set().union(*(set(b) for b in bags)):
        raise ValueError("Bag coverage must equal the declared decision variables")
    result = []
    for bag, local in zip(bags, assigned):
        indices = [tuple(bag.index(v) for v in r.scope) for r in local]
        rows = frozenset(values for values in itertools.product(*(domains[v] for v in bag))
                         if all(tuple(values[k] for k in ix) in rel.rows
                                for rel, ix in zip(local, indices)))
        result.append(Relation(tuple(bag), rows))
    return result

def compile_kernel(kernel: Kernel, envelope: frozenset[Node], templates, commands,
                   *, ranks=None):
    """Exact Q-closure constraint compiler with fixed initial-memory maps.

    Each variable is (actor, current memory, local observation). Its value is
    (command, next memory). Ranks, if needed, are fixed proof data on all Q nodes.
    Relations sharing a scope are intersected while streaming scenarios.
    """
    faults = tuple(kernel.faults())
    if not faults or not envelope:
        raise ValueError("Nonempty fault family and supplied envelope required")
    if len(templates) != kernel.actors or len(commands) != kernel.actors:
        raise ValueError("One local interface per executor required")
    domains = {}
    for i, template in enumerate(templates):
        for memory in range(len(template.outputs)):
            for observation in template.observations:
                domains[(i, memory, observation)] = tuple(
                    (command, nxt) for command in commands[i]
                    for nxt in range(len(template.outputs)))
    if any(not domain for domain in domains.values()):
        raise ValueError("Empty local command/memory domain")
    for node in envelope:
        if node.fault not in faults or len(node.memory) != kernel.actors:
            raise ValueError("Envelope has an unknown fault or malformed memory")
        if any(not 0 <= m < len(templates[i].outputs) for i, m in enumerate(node.memory)):
            raise ValueError("Envelope memory is outside the declared interface")
        contracts = kernel.service(node.fault)
        if len(node.ages) != len(contracts) or any(
                deadline < 1 or not 0 <= age < deadline
                for age, (_, deadline) in zip(node.ages, contracts)):
            raise ValueError("Envelope violates its service-age type")
        unbounded = set(kernel.recurrent_service(node.fault)) - {n for n, _ in contracts}
        if any(ranks is None or (node, name) not in ranks or type(ranks[(node, name)]) is not int or ranks[(node, name)] < 0
               for name in unbounded):
            raise ValueError("Unbounded recurrence requires a supplied natural service-free rank")
    initial_count = 0
    for fault in faults:
        initials = tuple(kernel.initials(fault))
        if not initials:
            raise ValueError("Empty initial family")
        for initial in initials:
            if kernel.initial_violations(fault, initial.state):
                raise ValueError("An admitted initial state violates its initialization contract")
            if len(initial.local_inputs) != kernel.actors:
                raise ValueError("Malformed local initialization")
            ages = initial.service_ages if initial.service_ages is not None else tuple(
                0 for _ in kernel.service(fault))
            node = Node(fault, initial.state,
                        tuple(t.start(s) for t, s in zip(templates, initial.local_inputs)), ages)
            if node not in envelope:
                raise ValueError("Supplied Q does not cover initialization")
            initial_count += 1
    grouped = {}
    scenarios = checked_outcomes = rejected_rows = 0
    for node in sorted(envelope, key=repr):
        observations = tuple(kernel.observations(node.fault, node.state))
        if not observations:
            grouped[()] = frozenset()
        for observation in observations:
            scenarios += 1
            if len(observation.local) != kernel.actors:
                raise ValueError("Malformed local observation tuple")
            active = tuple(i for i in range(kernel.actors)
                           if kernel.compliant(node.fault, i) and observation.local[i] is not None)
            scope = tuple((i, node.memory[i], observation.local[i]) for i in active)
            if any(v not in domains for v in scope):
                raise ValueError("Observation outside declared local alphabet")
            candidates = grouped.get(scope)
            if candidates is None:
                candidates = frozenset(itertools.product(*(domains[v] for v in scope)))
            kept = set()
            for row in sorted(candidates, key=repr):
                issued, memory = [None] * kernel.actors, list(node.memory)
                for i, (command, nxt) in zip(active, row):
                    issued[i], memory[i] = command, nxt
                seen, good = False, True
                for outcome in kernel.outcomes(node.fault, node.state, observation, tuple(issued)):
                    seen = True
                    checked_outcomes += 1
                    ages = tuple(0 if name in outcome.delivered else age+1
                                 for age, (name, _) in zip(node.ages, kernel.service(node.fault)))
                    successor = Node(node.fault, outcome.state, tuple(memory), ages)
                    if outcome.violations or successor not in envelope:
                        good = False
                        break
                    for name in kernel.recurrent_service(node.fault):
                        if name not in {n for n, _ in kernel.service(node.fault)}:
                            if name not in outcome.delivered and not (
                                    ranks[(successor, name)] < ranks[(node, name)]):
                                good = False
                    if not good:
                        break
                if seen and good:
                    kept.add(row)
                else:
                    rejected_rows += 1
            grouped[scope] = frozenset(kept)
    relations = [Relation(scope, rows) for scope, rows in sorted(grouped.items(), key=lambda x: repr(x[0]))]
    return domains, relations, {"envelope_nodes": len(envelope), "initials": initial_count,
                               "predecision_scenarios": scenarios, "outcomes_checked": checked_outcomes,
                               "rows_removed": rejected_rows, "grouped_scopes": len(relations)}

def extract_tables(assignment, templates, domains):
    result = []
    for i, template in enumerate(templates):
        outputs, updates = [], []
        for memory in range(len(template.outputs)):
            selected = [assignment.get((i, memory, obs), domains[(i, memory, obs)][0])
                        for obs in template.observations]
            outputs.append(tuple(x[0] for x in selected))
            updates.append(tuple(x[1] for x in selected))
        result.append(Table(template.observations, template.initial_symbols, template.initial,
                            tuple(outputs), tuple(updates)))
    return tuple(result)

@dataclass(frozen=True)
class SwitchingState:
    physical: BrakeState
    mode: int
    @property
    def x(self):
        return self.physical.x
    @property
    def heat(self):
        return self.physical.heat

class SwitchingBrakes(PeerBrakes):
    """Independent brakes with heterogeneous, adversarially switching strengths.

    It reuses the actual command/fault/FIFO/thermal observations of PeerBrakes.
    Strength changes do not pass through a global authorization gate.
    """
    strengths = ((4, 10, 16), (7, 9, 14))
    def initials(self, fault):
        for initial in super().initials(fault):
            for mode in range(len(self.strengths)):
                yield Initial(SwitchingState(initial.state, mode), initial.local_inputs)
    def initial_violations(self, fault, state):
        physical = state.physical if isinstance(state, SwitchingState) else state
        return super().initial_violations(fault, physical)
    def observations(self, fault, state):
        yield from super().observations(fault, state.physical)
    def outcomes(self, fault, state, observation, issued):
        # Parent enumerates actual independent planner/actuator/drive choices.
        seen = set()
        for base in super().outcomes(fault, state.physical, observation, issued):
            e = base.event
            key = (tuple(e["issued"]), tuple(e["actual_engagement"]), e["motor_input"])
            if key in seen:
                continue
            seen.add(key)
            force = sum(w * a for w, a in zip(self.strengths[state.mode], e["actual_engagement"]))
            x = max(0, (5*state.physical.x + 10*e["motor_input"] - force)//10)
            physical = BrakeState(x, base.state.heat, base.state.pending, base.state.samples)
            bad = tuple(v for v in base.violations if v.startswith("honest_issued_response"))
            bad += super().initial_violations(fault, physical)
            deliveries = (0, x) if fault.motor_bad and x else (x,)
            for mode in range(len(self.strengths)):
                for delivered in deliveries:
                    event = dict(e, mode=state.mode, next_mode=mode, force_numerator=force,
                                 x_next=x, actual_delivery=delivered)
                    yield Outcome(SwitchingState(physical, mode),
                                  frozenset(("target",)) if delivered >= 1 else frozenset(),
                                  bad, event)

def switching_envelope(kernel):
    nodes = set()
    for fault in kernel.faults():
        intact = set(range(kernel.actors)) - set(fault.planner) - set(fault.actuator)
        for x, heat, pending, mode in itertools.product(
                range(0 if fault.motor_bad else 1, 11), range(7),
                itertools.product((0, 1), repeat=kernel.actors), range(len(kernel.strengths))):
            if x >= 8 and not any(pending[i] for i in intact):
                continue
            state = SwitchingState(BrakeState(x, heat, (pending,), ()), mode)
            nodes.add(Node(fault, state, (0,)*kernel.actors, () if fault.motor_bad else (0,)))
    return frozenset(nodes)


class SwitchingFleet(ProductPeerBrakes):
    def __init__(self, devices=2, bad_motors=1):
        super().__init__(devices, bad_motors)
        self.local = SwitchingBrakes()
    def faults(self):
        for fault in super().faults():
            # One shared brake-owner compromise across the entire fleet.
            if sum(len(set(f.planner) | set(f.actuator)) for f in fault.components) <= 1:
                yield fault

def fleet_certificate(local_bag, local_domains, local_templates):
    """Construct a gluing/product certificate, not an exhaustive global traversal."""
    fleet = SwitchingFleet()
    bags = []
    domains = {}
    for device in range(fleet.devices):
        mapping = {v: (device*3 + v[0], v[1], v[2]) for v in local_bag.scope}
        bags.append(Relation(tuple(mapping[v] for v in local_bag.scope), local_bag.rows))
        domains.update({mapping[v]: local_domains[v] for v in local_bag.scope})
    assignment, _, passes = join_tree_solve(bags, (-1, 0))
    assert assignment is not None
    policies = extract_tables(assignment, local_templates * fleet.devices, domains)
    checked, changed, hostile, actual_total_min = 0, 0, 0, None
    for fault in fleet.faults():
        state = tuple(SwitchingState(BrakeState(4, 6, ((0, 0, 0),), ()), j % 2)
                      for j in range(fleet.devices))
        observation = next(iter(fleet.observations(fault, state)))
        issued = tuple(p.react(0, observation.local[i])[0] if fleet.compliant(fault, i) else None
                       for i, p in enumerate(policies))
        for outcome in fleet.outcomes(fault, state, observation, issued):
            checked += 1
            assert not outcome.violations
            assert "aggregate" in outcome.delivered
            delivered = outcome.event["aggregate_delivery"]
            actual_total_min = delivered if actual_total_min is None else min(actual_total_min, delivered)
            changed += any(e["mode"] != e["next_mode"] for e in outcome.event["components"])
            hostile += any(e["faulty_engagement_without_command"] for e in outcome.event["components"])
    return {"devices": fleet.devices, "global_fault_scenarios": len(tuple(fleet.faults())),
            "shared_brake_owner_fault_budget": 1, "faulty_motor_budget": fleet.bad_motors,
            "largest_bag": len(local_bag.scope), "semijoin_passes": passes,
            "joint_boundary_outcomes_checked": checked, "capability_change_outcomes": changed,
            "uncommanded_faulty_effect_outcomes": hostile, "boundary_actual_delivery_min": actual_total_min,
            "all_run_certificate": "component Q closure plus actual summed service under one joint fault",
            "full_global_graph_enumerated": False}


class SharedPortBrakes(SwitchingBrakes):
    """A component contract for a shared planner's genuinely joint signal."""
    def observations(self, fault, state):
        x = state.physical.x
        shared = ("pair_low",) if x < 2 else ("pair_low", "pair_high")
        private = tuple(label for label, possible in
                        (("low", x-1 < 3), ("high", x+1 >= 3)) if possible)
        for local in itertools.product(shared, private, private):
            yield Observation(local, x)

class SharedPlannerFleet:
    actors = 5
    actor_maps = ((0, 1, 2), (0, 3, 4))
    def __init__(self, norms=("", "")):
        self.local = SharedPortBrakes()
        self.raw = PeerBrakes()
        self.norms = norms
    def faults(self):
        for bad_motors in ((), (0,), (1,)):
            for owner, role in ((-1, 0),) + tuple(itertools.product(range(5), (1, 2, 3))):
                components = []
                for device, mapping in enumerate(self.actor_maps):
                    affected = mapping.index(owner) if owner in mapping else None
                    components.append(BrakeFault(device in bad_motors,
                        (affected,) if affected is not None and role & 1 else (),
                        (affected,) if affected is not None and role & 2 else ()))
                yield ProductFault(tuple(components))
    def compliant(self, fault, actor):
        return all(self.local.compliant(fault.components[j], mapping.index(actor))
                   for j, mapping in enumerate(self.actor_maps) if actor in mapping)
    def initials(self, fault):
        for items in itertools.product(*(tuple(self.local.initials(f)) for f in fault.components)):
            yield Initial(tuple(item.state for item in items), ("boot",)*self.actors)
    def initial_violations(self, fault, state):
        return tuple(str(j)+":"+v for j, (f, x) in enumerate(zip(fault.components, state))
                     for v in self.local.initial_violations(f, x))
    def observations(self, fault, state):
        seen = set()
        for pair in itertools.product(*(tuple(self.raw.observations(f, x.physical))
                                        for f, x in zip(fault.components, state))):
            shared = "pair_high" if all(o.local[0] == "high" for o in pair) else "pair_low"
            local = (shared, pair[0].local[1], pair[0].local[2], pair[1].local[1], pair[1].local[2])
            if local not in seen:
                seen.add(local)
                yield Observation(local, tuple(x.physical.x for x in state))
    def outcomes(self, fault, state, observation, issued):
        projected = []
        for j, mapping in enumerate(self.actor_maps):
            local_obs = Observation(tuple(observation.local[i] for i in mapping), observation.physical_sample[j])
            local_issued = tuple(issued[i] for i in mapping)
            projected.append(tuple(self.local.outcomes(fault.components[j], state[j], local_obs, local_issued)))
        for items in itertools.product(*projected):
            bad = tuple(str(j)+":"+v for j, item in enumerate(items) for v in item.violations)
            if self.compliant(fault, 0) and observation.local[0] == "pair_high":
                for j, rule in enumerate(self.norms):
                    if (rule == "require" and issued[0] != 1) or (rule == "forbid" and issued[0] != 0):
                        bad += (str(j)+":shared_conduct",)
            delivery = sum(item.event["actual_delivery"] for item in items)
            yield Outcome(tuple(item.state for item in items),
                          frozenset(("aggregate",)) if delivery >= 1 else frozenset(), bad,
                          {"components": [item.event for item in items], "aggregate_delivery": delivery})
    def service(self, fault): return (("aggregate", 1),)
    def recurrent_service(self, fault): return ("aggregate",)

def shared_planner_certificate():
    local = SharedPortBrakes()
    templates = (Table(("pair_low", "pair_high"), ("boot",), (0,), ((0, 0),), ((0, 0),)),
                 Table(("low", "high"), ("boot",), (0,), ((0, 0),), ((0, 0),)),
                 Table(("low", "high"), ("boot",), (0,), ((0, 0),), ((0, 0),)))
    domains, constraints, counts = compile_kernel(local, switching_envelope(local), templates, ((0, 1),)*3)
    variables = tuple(sorted(domains, key=repr))
    local_bag = bag_relations(constraints, domains, (variables,), (-1,))[0]
    assert len(local_bag.rows) == 2
    permissions = permission_supports(local_bag, {0: "pair_high", 1: "high", 2: "high"})
    assert permissions["minimal_supports"] == [[1, 2]]
    assert permissions["minimal_blockers"] == [[1], [2]]
    fleet = SharedPlannerFleet()
    bags, global_domains = [], {}
    for mapping in fleet.actor_maps:
        rename = {v: (mapping[v[0]], v[1], v[2]) for v in variables}
        bags.append(Relation(tuple(rename[v] for v in variables), local_bag.rows))
        global_domains.update({rename[v]: domains[v] for v in variables})
    assignment, _, passes = join_tree_solve(bags, (-1, 0), prefer_last=True)
    assert assignment is not None
    global_templates = (templates[0], templates[1], templates[2], templates[1], templates[2])
    policies = extract_tables(assignment, global_templates, global_domains)
    assert policies[0].outputs == ((0, 1),)
    # The actual pair signal projects into BOTH component contracts. The
    # component need not infer the other target's state or invent a new view.
    projection_cases = 0
    f = next(iter(fleet.faults()))
    for a, b in itertools.product(range(11), repeat=2):
        state = tuple(SwitchingState(BrakeState(x, 0, ((0, 0, 0),), ()), j)
                      for j, x in enumerate((a, b)))
        for obs in fleet.observations(f, state):
            for j, mapping in enumerate(fleet.actor_maps):
                projected = tuple(obs.local[i] for i in mapping)
                allowed = {o.local for o in local.observations(f.components[j], state[j])}
                assert projected in allowed
                projection_cases += 1
    checked = changed = hostile = 0
    for fault in fleet.faults():
        state = tuple(SwitchingState(BrakeState(4, 6, ((0, 0, 0),), ()), j) for j in range(2))
        for observation in fleet.observations(fault, state):
            issued = tuple(p.react(0, observation.local[i])[0] if fleet.compliant(fault, i) else None
                           for i, p in enumerate(policies))
            for outcome in fleet.outcomes(fault, state, observation, issued):
                assert not outcome.violations
                assert "aggregate" in outcome.delivered
                checked += 1
                changed += any(e["mode"] != e["next_mode"] for e in outcome.event["components"])
                hostile += any(e["faulty_engagement_without_command"] for e in outcome.event["components"])
                if fleet.compliant(fault, 0):
                    assert outcome.event["components"][0]["issued"][0] == issued[0]
                    assert outcome.event["components"][1]["issued"][0] == issued[0]
    # Conflicting factive duties are imposed at the same actual shared HIGH
    # view; every physical outcome remains present and is marked inadmissible.
    shared = (0, 0, "pair_high")
    required = Relation(bags[0].scope, frozenset(row for row in bags[0].rows
                                               if row[bags[0].scope.index(shared)][0] == 1))
    forbidden = Relation(bags[1].scope, frozenset(row for row in bags[1].rows
                                               if row[bags[1].scope.index(shared)][0] == 0))
    assert join_tree_solve((required, forbidden), (-1, 0))[0] is None
    conflict = SharedPlannerFleet(("require", "forbid"))
    state = tuple(SwitchingState(BrakeState(4, 0, ((0, 0, 0),), ()), j) for j in range(2))
    observation = next(iter(conflict.observations(f, state)))
    conflict_outcomes = 0
    for command in (0, 1):
        for outcome in conflict.outcomes(f, state, observation, (command, 1, 1, 1, 1)):
            assert any(v.endswith("shared_conduct") for v in outcome.violations)
            conflict_outcomes += 1
    return {"global_actors": fleet.actors, "global_variables": len(global_domains),
            "largest_bag": len(variables), "shared_variables": sorted(set(bags[0].scope) & set(bags[1].scope)),
            "local_rows": len(local_bag.rows), "global_solutions": len(natural_join(bags)),
            "optional_permissions": permissions,
            "permission_fault_effects": permission_fault_effect_probe(local),
            "semijoin_passes": passes, "shared_policy": policies[0].outputs,
            "global_fault_scenarios": len(tuple(fleet.faults())), "local_compile": counts,
            "observation_projection_cases": projection_cases,
            "joint_boundary_outcomes_checked": checked, "capability_change_outcomes": changed,
            "uncommanded_faulty_effect_outcomes": hostile,
            "conflicting_authority_outcomes": conflict_outcomes,
            "conflicting_authority_join_empty": True,
            "all_run_certificate": "overlapping local-policy gluing and product physical closure",
            "full_global_graph_enumerated": False}


class CyclicControl:
    """Three indistinguishable local decisions with incompatible joint duties."""
    actors = 3
    active_pairs = ((0, 1), (1, 2), (0, 2))
    def faults(self): return ((),)
    def compliant(self, fault, actor): return True
    def initials(self, fault):
        return tuple(Initial(x, ("boot",)*3) for x in range(3))
    def initial_violations(self, fault, state): return ()
    def observations(self, fault, state):
        yield Observation(tuple("go" if i in self.active_pairs[state] else None for i in range(3)))
    def outcomes(self, fault, state, observation, issued):
        i, j = self.active_pairs[state]
        allowed = issued[i] == issued[j] if state < 2 else issued[i] != issued[j]
        yield Outcome(state, frozenset(("service",)),
                      () if allowed else ("joint_conduct",), {"actual_delivery": 1})
    def service(self, fault): return (("service", 1),)
    def recurrent_service(self, fault): return ("service",)

def kernel_regressions():
    kernel = CyclicControl()
    templates = (Table(("go",), ("boot",), (0,), ((0,),), ((0,),)),)*3
    envelope = frozenset(Node((), x, (0, 0, 0), (0,)) for x in range(3))
    domains, constraints, _ = compile_kernel(kernel, envelope, templates, ((0, 1),)*3)
    assert not natural_join(constraints)
    assert all(semijoin(a, b) == a for a in constraints for b in constraints)
    rejected = 0
    for commands in itertools.product((0, 1), repeat=3):
        policies = tuple(Table(("go",), ("boot",), (0,), ((c,),), ((0,),)) for c in commands)
        assert not verify(kernel, policies)["winning"]
        rejected += 1
    try:
        compile_kernel(kernel, frozenset(n for n in envelope if n.state != 2),
                       templates, ((0, 1),)*3)
        raise AssertionError("Missing initialization was accepted")
    except ValueError:
        pass
    class NoService(CyclicControl):
        def outcomes(self, fault, state, observation, issued):
            yield Outcome(state, frozenset(), (), {})
    _, starving, _ = compile_kernel(NoService(), envelope, templates, ((0, 1),)*3)
    assert not natural_join(starving)
    class NoOutcome(CyclicControl):
        def outcomes(self, fault, state, observation, issued):
            return iter(())
    _, blocked, _ = compile_kernel(NoOutcome(), envelope, templates, ((0, 1),)*3)
    assert not natural_join(blocked)

    class StartupOnly:
        actors = 1
        def faults(self): return ((),)
        def compliant(self, fault, actor): return True
        def initials(self, fault): return (Initial(0, ("boot",)),)
        def initial_violations(self, fault, state):
            return ("not_startup_state",) if state != 0 else ()
        def observations(self, fault, state): return (Observation(("go",)),)
        def outcomes(self, fault, state, observation, issued):
            return (Outcome(1, frozenset(("service",)), (), {}),)
        def service(self, fault): return (("service", 1),)
        def recurrent_service(self, fault): return ("service",)
    startup = StartupOnly()
    startup_q = frozenset(Node((), x, (0,), (0,)) for x in (0, 1))
    _, startup_relations, _ = compile_kernel(startup, startup_q, templates[:1], ((0, 1),))
    assert natural_join(startup_relations)
    assert verify(startup, templates[:1])["winning"]
    class BadInitial(StartupOnly):
        def initial_violations(self, fault, state): return ("bad_initial",)
    try:
        compile_kernel(BadInitial(), startup_q, templates[:1], ((0, 1),))
        raise AssertionError("A failed initial verdict was accepted")
    except ValueError:
        pass

    return {"cyclic_control_policies_rejected": rejected, "pairwise_consistent": True,
            "actual_service_not_commanded_service": True, "empty_outcome_is_losing": True,
            "initial_coverage_checked": True, "initial_verdict_checked_only_at_initialization": True,
            "noninitial_startup_validator_failure_is_not_a_world_violation": True}


def minimal_sets(family):
    family = tuple(family)
    return frozenset(s for s in family if not any(t < s for t in family))

def powerset(items):
    items = tuple(items)
    return tuple(frozenset(c) for n in range(len(items)+1) for c in itertools.combinations(items, n))

def blocker(clutter, universe):
    return minimal_sets(s for s in powerset(universe) if all(s & c for c in clutter))


def permission_supports(joined, high_labels):
    """Extract optional compliant-HIGH permissions from the actual joined rows.

    Only policy admissibility is restricted. The kernel, fault family, Q, and
    all actual faulty commands/effects remain unchanged.
    """
    actors = tuple(sorted(high_labels))
    assert set(actors) == {v[0] for v in joined.scope}
    high_indices = {i: joined.scope.index((i, 0, high_labels[i])) for i in actors}
    used = {}
    for row in joined.rows:
        assert all(memory == 0 for _, memory, _ in joined.scope)
        assert all(value[0] in (0, 1) for value in row)
        assert all(value[0] == 0 for variable, value in zip(joined.scope, row)
                   if variable[2] != high_labels[variable[0]])
        used[row] = frozenset(i for i in actors if row[high_indices[i]][0] == 1)
    supports = minimal_sets(used.values())
    dual = blocker(supports, actors)
    assert blocker(dual, actors) == supports
    availability = []
    for enabled in powerset(actors):
        retained = frozenset(row for row in joined.rows if used[row] <= enabled)
        feasible = bool(retained)
        assert feasible == any(s <= enabled for s in supports)
        assert feasible == (not any(b <= frozenset(actors)-enabled for b in dual))
        for larger in powerset(actors):
            if enabled <= larger:
                assert retained <= frozenset(row for row in joined.rows if used[row] <= larger)
        availability.append({"enabled": sorted(enabled), "policy_rows": len(retained), "feasible": feasible})
    ordered = lambda family: sorted((sorted(s) for s in family), key=lambda s: (len(s), s))
    return {"scope": "supplied Q and selected local observation/memory class",
            "resource": "compliant program permission to issue ON at its HIGH view",
            "joined_policy_rows": len(joined.rows), "minimal_supports": ordered(supports),
            "minimal_blockers": ordered(dual), "availability": availability,
            "physical_kernel_changed": False, "fault_family_changed": False}

def permission_fault_effect_probe(kernel):
    """Actor 0 lacks program permission; its faulty hardware/program still acts."""
    state = SwitchingState(BrakeState(1, 0, ((0, 0, 0),), ()), 0)
    actuator_fault = BrakeFault(False, (), (0,))
    planner_fault = BrakeFault(False, (0,), ())
    assert actuator_fault in tuple(kernel.faults()) and planner_fault in tuple(kernel.faults())
    observation = next(iter(kernel.observations(actuator_fault, state)))
    actual = tuple(kernel.outcomes(actuator_fault, state, observation, (0, 0, 0)))
    engagements = sum(o.event["actual_engagement"][0] == 1 for o in actual)
    assert engagements > 0
    observation = next(iter(kernel.observations(planner_fault, state)))
    planned = tuple(kernel.outcomes(planner_fault, state, observation, (None, 0, 0)))
    unauthorized_faulty_commands = sum(o.event["issued"][0] == 1 for o in planned)
    assert unauthorized_faulty_commands > 0
    assert any(o.state.physical.pending[0][0] == 1 for o in planned)
    return {"enabled_compliant_programs": [1, 2], "disabled_program": 0,
            "retained_faulty_engagement_outcomes": engagements,
            "retained_faulty_command_outcomes": unauthorized_faulty_commands,
            "faulty_commands_remain_in_fifo": True}

def absent_projection_regression():
    # The real Table.react consumer masks absence before consulting either
    # outputs or updates; every local initialization map remains fixed.
    absent_reactions = set()
    for values in itertools.product(itertools.product((0, 1), repeat=2), repeat=2):
        outputs = tuple((v[0],) for v in values)
        updates = tuple((v[1],) for v in values)
        table = Table(("go",), ("boot",), (1,), outputs, updates)
        assert table.start("boot") == 1
        absent_reactions.add(table.react(1, None))
    assert absent_reactions == {(None, 1)}
    # Explicit cylindrical extension of a nonempty joint relation.
    active = [Relation(("a", "b"), frozenset(((0, 0), (1, 1)))),
              Relation(("b", "c"), frozenset(((0, 0), (1, 1))))]
    live_solutions = natural_join(active)
    ghost_values = tuple(itertools.product((0, 1), repeat=2))
    extended = [Relation(r.scope + ("absent_choice",),
                         frozenset(row + (ghost,) for row in r.rows for ghost in ghost_values))
                for r in active]
    full_solutions = natural_join(extended)
    projection = {tuple(s[v] for v in ("a", "b", "c")) for s in full_solutions}
    assert projection == {tuple(s[v] for v in ("a", "b", "c")) for s in live_solutions}
    assert len(full_solutions) == len(live_solutions) * len(ghost_values)
    return {"fixed_initial_memory": 1, "absent_tables_checked": 16,
            "issued_on_absence": None, "memory_after_absence": 1,
            "active_join_solutions": len(live_solutions), "extended_join_solutions": len(full_solutions),
            "ghost_projection_exact": True}


def relation_regressions():
    # Exhaust every binary relation on two-edge chain scopes, including emptiness.
    pair_rows = tuple(itertools.product((0, 1), repeat=2))
    all_relations = [frozenset(row for k, row in enumerate(pair_rows) if mask >> k & 1)
                     for mask in range(16)]
    count = 0
    for left, right in itertools.product(all_relations, repeat=2):
        relations = [Relation(("a", "b"), left), Relation(("b", "c"), right)]
        solved, reduced, _ = join_tree_solve(relations, (-1, 0))
        oracle = natural_join(relations)
        assert (solved is not None) == bool(oracle)
        for rel in reduced:
            assert rel.rows == frozenset(tuple(row[v] for v in rel.scope) for row in oracle)
        count += 1
    cyclic = [Relation(("a", "b"), frozenset(((0, 0), (1, 1)))),
              Relation(("b", "c"), frozenset(((0, 0), (1, 1)))),
              Relation(("a", "c"), frozenset(((0, 1), (1, 0))))]
    assert not natural_join(cyclic)
    assert all(semijoin(a, b) == a for a in cyclic for b in cyclic)
    try:
        join_tree_solve(cyclic, (-1, 0, 1))
        raise AssertionError("A cyclic join tree was accepted")
    except ValueError:
        pass
    # Joint constraints can reject independent feasibility, including nonblocking.
    contradictory = [Relation(("decision",), frozenset(((0,),))),
                     Relation(("decision",), frozenset(((1,),)))]
    assert join_tree_solve(contradictory, (-1, 0))[0] is None
    return {"exhaustive_chain_databases": count, "cyclic_pairwise_consistent": True,
            "cyclic_global_solutions": 0, "incompatible_singletons_rejected": True}

def resource_regressions():
    universe = tuple(range(4))
    families = powerset(powerset(universe))
    checked = 0
    for family in families:
        clutter = minimal_sets(family)
        if clutter != family:
            continue
        dual = blocker(clutter, universe)
        assert blocker(dual, universe) == clutter
        for available in powerset(universe):
            feasible = any(c <= available for c in clutter)
            obstructed = any(d <= frozenset(universe)-available for d in dual)
            assert feasible != obstructed
        checked += 1
    return {"ground_resources": 4, "all_clutters_checked": checked,
            "partition_dual_checked": True, "order": "optional resources with discardable extensions"}

def reproduce():
    regression = relation_regressions()
    resources = resource_regressions()
    kernel_checks = kernel_regressions()
    kernel = SwitchingBrakes()
    templates = (Table(("low", "high"), ("boot",), (0,), ((0, 0),), ((0, 0),)),)*3
    domains, constraints, counts = compile_kernel(kernel, switching_envelope(kernel), templates, ((0, 1),)*3)
    variables = tuple(sorted(domains, key=repr))
    # A local device needs a six-variable bag; no raw acyclicity is asserted.
    local_bags = bag_relations(constraints, domains, (variables,), (-1,))
    permissions = permission_supports(local_bags[0], {i: "high" for i in range(3)})
    assert permissions["minimal_supports"] == [[0, 1], [0, 2], [1, 2]]
    assert permissions["minimal_blockers"] == [[0, 1], [0, 2], [1, 2]]
    selected, reduced, _ = join_tree_solve(local_bags, (-1,))
    assert selected is not None
    policies = extract_tables(selected, templates, domains)
    replay = verify(kernel, policies, full=True)
    assert replay["winning"]
    # Enumerate the local bag only, then verify its rows against the original
    # kernel independently. This tests the adapter, not just the join code.
    for row in local_bags[0].rows:
        tables = extract_tables(dict(zip(variables, row)), templates, domains)
        assert verify(kernel, tables)["winning"]
    # A chain of J devices shares one explicitly optional binary coordination
    # variable between adjacent module contracts. All bag relations retain
    # their full local policy tuples. This demonstrates the algorithmic width
    # law separately from the physical product theorem in STRUCTURE.md.
    chain = []
    for j in range(12):
        left, right = ("boundary", j), ("boundary", j+1)
        scope = (left,) + tuple(("device", j, v) for v in variables) + (right,)
        rows = frozenset((b,) + row + (b,) for row in local_bags[0].rows for b in (0, 1))
        chain.append(Relation(scope, rows))
    chain_solution, _, passes = join_tree_solve(chain, (-1,) + tuple(range(11)))
    assert chain_solution is not None
    return {
        "scope": "exact supplied-Q closure; fixed local interface; finite row construction",
        "relations": regression, "resources": resources, "kernel_regressions": kernel_checks,
        "absent_projection": absent_projection_regression(),
        "coupled_fault_fleet": fleet_certificate(local_bags[0], domains, templates),
        "shared_planner_fleet": shared_planner_certificate(),
        "switching_brakes": {
            "strength_modes": kernel.strengths, "fault_scenarios": len(tuple(kernel.faults())),
            "counts": counts, "variables": len(domains), "largest_local_bag": len(variables),
            "local_bag_rows": len(local_bags[0].rows),
            "optional_permissions": permissions,
            "permission_fault_effects": permission_fault_effect_probe(kernel),
            "selected_outputs": [t.outputs for t in policies],
            "all_selected_bag_rows_replayed": True,
            "independent_kernel_replay": replay,
            "service_scope": "every normal motor delivers each tick; aggregate product uses at most p<J faulty motors",
        },
        "join_chain_algorithm_only": {"modules": len(chain), "largest_bag": len(chain[0].scope),
                                      "semijoin_passes": passes,
                                      "solution": True,
                                      "physical_runtime_coordination_claimed": False},
    }

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--write", action="store_true")
    args = parser.parse_args()
    result = reproduce()
    result["source_sha256_lf"] = {
        name: hashlib.sha256((HERE / name).read_bytes().replace(b"\r\n", b"\n")).hexdigest()
        for name in ("structure_model.py", "Structure.lean", "STRUCTURE.md", "STRUCTURE-SOURCES.md",
                     "../enforcement/finite_model.py")}
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    path = HERE / "structure_results.json"
    if args.write:
        path.write_text(rendered, encoding="utf-8")
    elif not path.exists() or path.read_text(encoding="utf-8") != rendered:
        raise SystemExit("Structural evidence differs: review before --write")
    print(json.dumps({"verified": True, "scope": result["scope"],
                      "switching_nodes": result["switching_brakes"]["counts"]["envelope_nodes"],
                      "local_policy_rows": result["switching_brakes"]["local_bag_rows"]}))

if __name__ == "__main__":
    main()

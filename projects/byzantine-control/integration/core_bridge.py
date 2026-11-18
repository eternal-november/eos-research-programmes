"""Concrete decision-boundary adapter to CoreBridge.lean's normal form.

Read-only imports of the existing actual-effect kernel. A model action is a
(command,next-memory) pair; irrelevant ghost pairs never reach source consumers.
The verifier counts source physical rounds, not expanded observations as ticks.
"""
from __future__ import annotations
from dataclasses import dataclass, replace
from collections import deque
from itertools import product
from pathlib import Path
import hashlib
import importlib.util
import json
import sys

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("bc_enforcement_source", ROOT / "enforcement" / "finite_model.py")
source = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = source
spec.loader.exec_module(source)

def require(condition, reason):
    if not condition:
        raise RuntimeError(reason)

def freeze_event(value):
    """Injective typed encoding of the finite structured event values used here."""
    if value is None or type(value) in (bool, int, str):
        return (type(value).__name__, value)
    if isinstance(value, dict):
        return ("dict", tuple(sorted(((freeze_event(k), freeze_event(v)) for k,v in value.items()), key=repr)))
    if isinstance(value, (tuple, list)):
        return (type(value).__name__, tuple(freeze_event(v) for v in value))
    if isinstance(value, (set, frozenset)):
        return (type(value).__name__, tuple(sorted((freeze_event(v) for v in value), key=repr)))
    raise TypeError("Event value lacks a declared lossless encoding: " + str(type(value)))

@dataclass(frozen=True)
class EffectRecord:
    issued_compliant: tuple
    delivered: frozenset
    metadata: tuple
    source_violations: tuple
    performed: bool = True

@dataclass(frozen=True)
class CoreBoundary:
    node: source.Node
    observation: source.Observation
    violations: tuple[str, ...] = ()
    terminal: str | None = None
    previous_effect: EffectRecord | None = None

def local_view(boundary, actor):
    """No fault, world, global depth, other actor view, or service age is returned."""
    return boundary.node.memory[actor], boundary.observation.local[actor]

def profile(kernel, tables, boundary):
    result = []
    for i, table in enumerate(tables):
        memory, observation = local_view(boundary, i)
        if observation is None or not kernel.compliant(boundary.node.fault, i):
            # A following-profile ghost, never a local runtime decision. Faulty
            # observation slots need not belong to the compliant table alphabet.
            result.append((table.outputs[0][0], memory))
        else:
            result.append(table.react(memory, observation))
    return tuple(result)

def masks(kernel, boundary, actions):
    issued, memories = [], []
    for i in range(kernel.actors):
        if kernel.compliant(boundary.node.fault, i) and boundary.observation.local[i] is not None:
            issued.append(actions[i][0])
            memories.append(actions[i][1])
        else:
            issued.append(None)
            memories.append(boundary.node.memory[i])
    return tuple(issued), tuple(memories)

def prepare(kernel, node, violations=(), previous_effect=None):
    """Retain the full JOINT observation relation, including its correlations."""
    observations = tuple(kernel.observations(node.fault, node.state))
    if not observations:
        return (CoreBoundary(node, source.Observation((None,) * kernel.actors),
                             tuple(violations) + ("no_observation_continuation",),
                             "no_observation_continuation", previous_effect),)
    return tuple(CoreBoundary(node, o, tuple(violations), None, previous_effect) for o in observations)

def initial_boundaries(kernel, tables):
    faults = tuple(kernel.faults())
    require(bool(faults), "Empty fault family is an invalid source instance")
    result = []
    for fault in faults:
        initials = tuple(kernel.initials(fault))
        require(bool(initials), "Every admitted fault needs a source initialization")
        for initial in initials:
            # The SAME local mu tables are used for every physical/fault scenario.
            memory = tuple(table.start(j) for table, j in zip(tables, initial.local_inputs))
            contracts = kernel.service(fault)
            ages = initial.service_ages
            if ages is None:
                ages = (0,) * len(contracts)
            require(len(ages) == len(contracts), "Service ages do not match source obligations")
            violations = list(kernel.initial_violations(fault, initial.state))
            if any(d < 1 or not 0 <= age < d for age, (_, d) in zip(ages, contracts)):
                violations.append("invalid_initial_service_age")
            node = source.Node(fault, initial.state, memory, tuple(ages))
            result.extend(prepare(kernel, node, violations))
    return tuple(result)

def core_successors(kernel, boundary, actions):
    """Each nonterminal edge performs one source effect and prepares next inputs."""
    if boundary.terminal:
        # Completed losing finite execution, with no invented delivered service.
        empty = EffectRecord((None,) * kernel.actors, frozenset(),
                             freeze_event({"terminal": boundary.terminal}), (), False)
        yield replace(boundary, previous_effect=empty), {"terminal": boundary.terminal, "delivered": ()}
        return
    issued, memories = masks(kernel, boundary, actions)
    found = False
    for outcome in kernel.outcomes(boundary.node.fault, boundary.node.state,
                                   boundary.observation, issued):
        found = True
        ages, bad = [], list(boundary.violations) + list(outcome.violations)
        for age, (name, deadline) in zip(boundary.node.ages, kernel.service(boundary.node.fault)):
            new_age = 0 if name in outcome.delivered else age + 1
            ages.append(new_age)
            if new_age >= deadline:
                bad.append("actual_service_deadline:" + name)
        next_node = source.Node(boundary.node.fault, outcome.state, memories, tuple(ages))
        record = EffectRecord(issued, outcome.delivered, freeze_event(outcome.event), outcome.violations)
        for next_boundary in prepare(kernel, next_node, tuple(sorted(set(bad))), record):
            yield next_boundary, outcome.event
    if not found:
        yield replace(boundary,
                      node=replace(boundary.node, memory=memories),
                      observation=source.Observation((None,) * kernel.actors),
                      violations=boundary.violations + ("no_effect_continuation",),
                      terminal="no_effect_continuation",
                      previous_effect=EffectRecord(issued, frozenset(),
                          freeze_event({"terminal": "no_effect_continuation"}), (), False)), {"terminal": "no_effect_continuation"}

def reference_react(kernel, node, observation, tables):
    """The source verifier's callback contract, independent of core masking."""
    commands, memories = [], []
    for i, table in enumerate(tables):
        if kernel.compliant(node.fault, i):
            command, memory = table.react(node.memory[i], observation.local[i])
        else:
            command, memory = None, node.memory[i]
        commands.append(command)
        memories.append(memory)
    return tuple(commands), tuple(memories)

def check_actual_brake_kernel():
    kernel, tables = source.PeerBrakes(), source.threshold_policy()
    boundary_initials = initial_boundaries(kernel, tables)
    require(all(not b.violations for b in boundary_initials), "Invalid positive initializer")
    queue, reached = deque(), set()
    for boundary in boundary_initials:
        if boundary.node not in reached:
            reached.add(boundary.node)
            queue.append(boundary.node)
    observation_count = edge_count = ghost_checks = 0
    digest = hashlib.sha256()
    while queue:
        node = queue.popleft()
        for observation in kernel.observations(node.fault, node.state):
            observation_count += 1
            boundary = CoreBoundary(node, observation)
            actual_profile = profile(kernel, tables, boundary)
            actual_issued, actual_memory = masks(kernel, boundary, actual_profile)
            ref_issued, ref_memory = reference_react(kernel, node, observation, tables)
            require((actual_issued, actual_memory) == (ref_issued, ref_memory),
                    "Core profile does not realize source local callbacks")
            # All bad-planner mathematical action values are ghost values: source
            # faulty commands remain generated independently by kernel.outcomes.
            ghost = tuple((1 - u, m + 19) if not kernel.compliant(node.fault, i) else (u, m)
                          for i, (u, m) in enumerate(actual_profile))
            require(masks(kernel, boundary, ghost) == (actual_issued, actual_memory),
                    "Faulty ghost output leaked to a source consumer")
            ghost_checks += 1
            for outcome in kernel.outcomes(node.fault, node.state, observation, ref_issued):
                edge_count += 1
                require(not outcome.violations, "Positive source outcome violated mission")
                new_ages = tuple(0 if name in outcome.delivered else age + 1
                                 for age, (name, _) in zip(node.ages, kernel.service(node.fault)))
                require(all(age < deadline for age, (_, deadline) in
                            zip(new_ages, kernel.service(node.fault))), "Actual service lost")
                target = source.Node(node.fault, outcome.state, actual_memory, new_ages)
                record = EffectRecord(actual_issued, outcome.delivered, freeze_event(outcome.event), outcome.violations)
                prepared = prepare(kernel, target, previous_effect=record)
                require(all(b.previous_effect == record for b in prepared),
                        "Actual source event or delivered output was erased")
                require(all(not b.violations for b in prepared), "Next source observations missing")
                require({b.observation for b in prepared} ==
                        set(kernel.observations(node.fault, outcome.state)),
                        "Joint observation correlation changed")
                # Instance-specific physical law, independently evaluated.
                actual = outcome.event["actual_engagement"]
                x = max(0, (5 * node.state.x + 10 * outcome.event["motor_input"] -
                            10 * sum(actual)) // 10)
                heat = (5 * node.state.heat + sum(actual) * node.state.x) // 10
                require((x, heat) == (outcome.state.x, outcome.state.heat),
                        "Realized effects differ from the declared source plant")
                require(outcome.event["invocation_x"] == node.state.x,
                        "Conduct evaluated at wrong source epoch")
                digest.update(repr((node, observation.local, actual_issued, target,
                                    tuple(sorted(outcome.delivered)))).encode("utf-8"))
                if target not in reached:
                    reached.add(target)
                    queue.append(target)
    # A nontrivial actual boundary is also passed through the whole macrostep function.
    probe = next(b for b in boundary_initials
                 if b.node.fault == source.BrakeFault(True, (), (0,)) and b.node.state.x == 1
                 and b.node.state.heat == 6)
    macro = tuple(core_successors(kernel, probe, profile(kernel, tables, probe)))
    require(any(e["actual_engagement"][0] and not e["issued"][0] for _, e in macro),
            "Independent faulty actuator was erased")
    require(all(not b.violations for b, _ in macro), "Macrostep positive probe failed")
    return {"reachable_source_nodes": len(reached), "joint_observation_boundaries": observation_count,
            "source_effect_edges": edge_count, "ghost_profile_checks": ghost_checks,
            "effect_correspondence_sha256": digest.hexdigest(),
            "macrostep_probe_successors": len(macro), "actual_effect_records_retained": True,
            "scope": "All positive peer-brake source nodes/observations/effects; next-boundary choice factors through the complete joint relation"}

def boundary_regressions():
    tables = source.threshold_policy()
    class Silent(source.PeerBrakes):
        def faults(self):
            return (source.BrakeFault(False),)
        def initials(self, fault):
            yield source.Initial(source.BrakeState(4, 0, ((0,0,0),), ()), ("boot",)*3, (1,))
        def observations(self, fault, state):
            yield source.Observation((None, "high", "high"), state.x)
        def service(self, fault):
            return (("target", 2),)
        def outcomes(self, fault, state, observation, issued):
            require(issued[0] is None, "Absent callback became a physical command")
            yield source.Outcome(state, frozenset(), (), {"actual_delivery": 0, "issued": issued})
    silent = Silent()
    table2 = source.Table(("low","high"), ("boot",), (0,), ((0,1),(1,0)), ((1,1),(0,0)))
    ts = (table2,) * 3
    boundary = initial_boundaries(silent, ts)[0]
    act = profile(silent, ts, boundary)
    changed = ((928,611),) + act[1:]
    require(masks(silent,boundary,act) == masks(silent,boundary,changed),
            "Absent ghost changed issued commands or memory")
    results = tuple(core_successors(silent,boundary,changed))
    require(all(b.node.memory[0] == 0 and b.node.ages == (2,) for b,_ in results),
            "Hidden global time advanced local memory or paused service")
    require(all("actual_service_deadline:target" in b.violations for b,_ in results),
            "Absent invocation incorrectly postponed physical service")
    class NoObserve(Silent):
        def observations(self, fault, state): return iter(())
    failed_obs = initial_boundaries(NoObserve(),ts)[0]
    require(failed_obs.terminal == "no_observation_continuation", "Observation deadlock was erased")
    class NoEffect(Silent):
        def outcomes(self, fault, state, observation, issued): return iter(())
    no_effect = NoEffect()
    b = initial_boundaries(no_effect,ts)[0]
    out = tuple(core_successors(no_effect,b,profile(no_effect,ts,b)))
    require(len(out) == 1 and out[0][0].terminal == "no_effect_continuation",
            "Missing effect was dropped")
    failed_effect = out[0][0]
    require(failed_effect.node.memory == masks(no_effect,b,profile(no_effect,ts,b))[1],
            "Failure completion lost the already performed invocation memory update")
    require(failed_effect.observation.local == (None,) * no_effect.actors,
            "Failure completion retained future active invocations")
    terminal, _ = next(core_successors(no_effect,failed_effect,profile(no_effect,ts,failed_effect)))
    require(terminal.node.memory == failed_effect.node.memory and
            terminal.observation.local == (None,) * no_effect.actors and
            not terminal.previous_effect.performed and not terminal.previous_effect.delivered,
            "Terminal stutter fabricated invocation or delivery")
    class BadPrivateSymbol(source.PeerBrakes):
        def faults(self):
            return (source.BrakeFault(True,(0,),()),)
        def observations(self,fault,state):
            for obs in super().observations(fault,state):
                yield source.Observation(("unused-by-source",)+obs.local[1:],obs.physical_sample)
    bad_symbol = BadPrivateSymbol()
    b_bad = initial_boundaries(bad_symbol,tables)[0]
    commands_bad, memories_bad = masks(bad_symbol,b_bad,profile(bad_symbol,tables,b_bad))
    require((commands_bad,memories_bad) == reference_react(bad_symbol,b_bad.node,b_bad.observation,tables),
            "Faulty-only symbol was consumed by an intact local callback")
    require(bool(tuple(core_successors(bad_symbol,b_bad,profile(bad_symbol,tables,b_bad)))),
            "Faulty-only observation destroyed actual source outcomes")
    class Correlated(Silent):
        def observations(self, fault, state):
            yield source.Observation(("low","high","high"),state.x)
            yield source.Observation(("high","low","high"),state.x)
    correlated = initial_boundaries(Correlated(),tables)
    require(len(correlated) == 2 and
            all(b.observation.local != ("low","low","high") for b in correlated),
            "Local projections invented a joint observation")
    require(freeze_event({"d": [1, True]}) != freeze_event({"d": (1, True)}),
            "Event encoding collapsed distinct container types")
    require(freeze_event({"d": [1]}) != freeze_event({"d": [True]}),
            "Event encoding collapsed integer and Boolean facts")
    # Fold only actual invocation observations: silent physical ticks add no input.
    signals = (None,"low",None,None,"high",None,"low")
    mem = table2.start("boot")
    events = []
    for signal in signals:
        cmd, next_mem = table2.react(mem,signal)
        if signal is not None:
            events.append((signal,cmd))
        else:
            require(cmd is None and next_mem == mem, "Silent callback changed local state")
        mem = next_mem
    replay = table2.start("boot")
    for signal, cmd in events:
        got,replay = table2.react(replay,signal)
        require(got == cmd, "Own issued action lost in local history")
    require(mem == replay, "Invocation-history factorization failed")
    return {"absent_ghost_masked_before_all_consumers": True,
            "service_advances_without_local_invocation": True,
            "preexisting_age_preserved": True, "observation_and_effect_deadlock_preserved": True,
            "faulty_observation_not_evaluated_as_compliant_input": True,
            "failed_invocation_memory_committed_and_terminal_silent": True,
            "joint_observation_correlation_preserved": True, "actual_event_metadata_retained": True,
            "invocation_history_erases_silent_ticks": True}

def main():
    import argparse
    parser=argparse.ArgumentParser()
    group=parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--write",action="store_true")
    group.add_argument("--check",action="store_true")
    args=parser.parse_args()
    result={"format":1, "actual_instance":check_actual_brake_kernel(),
            "boundary_regressions":boundary_regressions(),
            "initialization_scope":"Fixed local initializer mu, applied to every actual local input under every fault; same-arena synthesis is not inferred from this fixed-program bridge"}
    rendered=json.dumps(result,indent=2,sort_keys=True)+"\n"
    path=Path(__file__).with_name("core_bridge_results.json")
    if args.write: path.write_text(rendered,encoding="utf-8",newline="\n")
    else: require(path.read_text(encoding="utf-8")==rendered,"Bridge results changed")
    print(rendered)

if __name__=="__main__": main()

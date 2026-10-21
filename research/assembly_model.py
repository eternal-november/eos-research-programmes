"""Concrete common-core adapters and independently implemented transition projections.
The finite checks certify the stated instances, not arbitrary physical implementations.
"""
from dataclasses import dataclass
from itertools import product
import json
import digital_model as digital


@dataclass(frozen=True)
class DigitalState:
    faulty: int | None
    input: int
    epoch: int
    phase: int
    leader_signed: int
    raw: tuple
    echoes: tuple
    decisions: tuple
    terminal_signed: int
    receipts: tuple
    views: tuple


def digital_projection(prefix):
    return DigitalState(prefix.faulty, prefix.input, prefix.epoch, prefix.phase,
                        prefix.leader_signed, prefix.raw, prefix.echoes, prefix.decisions,
                        prefix.terminal_signed, prefix.receipts,
                        tuple(digital.local_view(prefix, i) for i in digital.ACTORS))


def _subsets(mask):
    # Independent of digital.submasks; enumerates subsets by individual bit choices.
    positions = [i for i in range(6) if mask & (1 << i)]
    return tuple(sum((1 << i) for i, take in zip(positions, row) if take)
                 for row in product((False, True), repeat=len(positions)))


def abstract_digital_events(state):
    """Guards depend on current abstract state, with no future data or safety filter."""
    f, phase = state.faulty, state.phase
    if phase == 0:
        for signed in range(4) if f == 0 else (1 << state.input,):
            deliveries = product(_subsets(signed), repeat=2) if f == 0 else ((signed, signed),)
            for r1, r2 in deliveries:
                yield ("raw-cutoff", (signed, r1, r2))
    elif phase == 1:
        domains = tuple(_subsets(state.leader_signed) if source == f
                        else (state.raw[source-1],) for source in (2, 1))
        for e1, e2 in product(*domains):
            yield ("echo-cutoff", (e1, e2))
    elif phase == 2:
        for faulty_values in (0,) if f is None else range(4):
            signed = sum(1 << (2*i + state.decisions[i])
                         for i in digital.PARTICIPANTS if i != f)
            if f is not None:
                signed |= sum(1 << (2*f+v) for v in (0, 1) if faulty_values & (1 << v))
            for a, b in product(_subsets(signed), repeat=2):
                yield ("terminal-send", (faulty_values, a, b))
    elif phase == 3:
        honest = sum(1 << (2*i + state.decisions[i])
                     for i in digital.PARTICIPANTS if i != f)
        domains = []
        for old in state.receipts:
            required = old | honest
            optional = state.terminal_signed & ~required
            domains.append(tuple(required | extra for extra in _subsets(optional)))
        for a, b in product(*domains):
            yield ("terminal-cutoff", (a, b))


def abstract_digital_step(state, event):
    """Factual update independently implemented from the source-prefix properties."""
    kind, data = event
    next_phase = state.phase + 1
    views = [list(v) + [("clock", next_phase)] for v in state.views]
    leader_signed, raw, echoes = state.leader_signed, state.raw, state.echoes
    decisions, signed, receipts = state.decisions, state.terminal_signed, state.receipts
    if kind == "raw-cutoff":
        leader_signed, r1, r2 = data
        raw = (r1, r2)
        views[0].append(("signed-proposal", leader_signed))
        for i in (1, 2):
            views[i].append(("raw", raw[i-1]))
    elif kind == "echo-cutoff":
        echoes = data
        decisions = tuple(None if i == state.faulty else
                          state.input if i == 0 else
                          int((raw[i-1] | echoes[i-1]) == 2) for i in (0, 1, 2))
        for i in (1, 2):
            views[i].extend((("sent-echo", echoes[2-i]), ("received-echo", echoes[i-1])))
        for i in (0, 1, 2):
            if i != state.faulty:
                views[i].append(("decision", decisions[i]))
    elif kind == "terminal-send":
        bad, a, b = data
        signed = 0
        for i in (0, 1, 2):
            values = tuple(v for v in (0, 1) if bad & (1 << v)) if i == state.faulty else (decisions[i],)
            views[i].append(("signed-terminal", values))
            signed |= sum(1 << (2*i+v) for v in values)
        receipts = (a, b)
        views[3].append(("terminal-receipts", a))
        views[4].append(("terminal-receipts", b))
    elif kind == "terminal-cutoff":
        receipts = data
        views[3].append(("terminal-receipts", data[0]))
        views[4].append(("terminal-receipts", data[1]))
    else:
        raise ValueError(("unknown event", event))
    return DigitalState(state.faulty, state.input, state.epoch, next_phase,
                        leader_signed, raw, echoes, decisions, signed, receipts,
                        tuple(map(tuple, views)))


def emitted_action(before, after, actor):
    """Recover actual issued commands from a source edge, not from policy output."""
    phase = before.phase
    if actor in digital.OBSERVERS:
        return ("observe",)
    if phase == 0:
        return ("propose", after.leader_signed) if actor == 0 else ("wait",)
    if phase == 1:
        return ("echo", after.echoes[2-actor]) if actor in (1, 2) else ("wait",)
    if phase == 2:
        mask = sum(1 << v for i, v in digital.tokens(after.terminal_signed) if i == actor)
        return ("terminal", mask)
    return ("retain",)


def digital_adapter_checks():
    level = list(digital.initials())
    states = edges = local_steps = 0
    policy = {}
    projection_sources = {}
    stage_counts = []
    for phase in range(5):
        stage_counts.append(len(level))
        next_level = []
        for source in level:
            target = digital_projection(source)
            assert target.phase == phase and target.faulty == source.faulty
            previous = projection_sources.setdefault(target, source)
            assert previous == source, "projection unexpectedly identified distinct guarded histories"
            states += 1
            for actor in digital.ACTORS:
                assert target.views[actor] == digital.local_view(source, actor)
                if actor != source.faulty:
                    key = (actor, target.views[actor])
                    issued = digital.local_action(actor, target.views[actor])
                    assert policy.setdefault(key, issued) == issued
            concrete_next = tuple(digital.successors(source))
            abstract_events = tuple(abstract_digital_events(target))
            abstract_next = {abstract_digital_step(target, e) for e in abstract_events}
            assert {digital_projection(n) for n in concrete_next} == abstract_next
            if phase < 4:
                assert concrete_next and abstract_next
            else:
                assert not concrete_next and not abstract_next
                # Successful finite mission, not a recurring-service proof by empty successors.
                assert all(digital.certificate(bundle, digital.final_value(source))
                           for bundle in source.receipts)
            for nxt in concrete_next:
                assert nxt.faulty == source.faulty and nxt.epoch == source.epoch
                assert nxt.phase == source.phase + 1
                for actor in digital.ACTORS:
                    if actor != source.faulty:
                        assert emitted_action(source, nxt, actor) == policy[(actor, target.views[actor])]
                        local_steps += 1
                assert all((new_view[:len(old_view)] == old_view)
                           for old_view, new_view in zip(target.views, digital_projection(nxt).views))
                edges += 1
            next_level.extend(concrete_next)
        level = next_level
    return {"source_states": states, "guarded_edges": edges,
            "matched_correct_action_occurrences": local_steps,
            "extracted_local_policy_classes": len(policy),
            "stage_counts": stage_counts,
            "projection_bijective_on_generated_states": True,
            "successor_images_equal": True,
            "fault_and_event_time_preserved": True,
            "finite_terminal_verdict": "success only at public certificate cutoff",
            "source_to_abstract_maps": "independent current-state guards/postconditions; local history/action identity"}


def run_checks():
    return {"digital_adapter": digital_adapter_checks()}


if __name__ == "__main__":
    print(json.dumps(run_checks(), indent=2, sort_keys=True))

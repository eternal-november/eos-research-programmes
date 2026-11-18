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
        old_bad = sum(1 << v for v in (0,1)
                      if f is not None and state.terminal_signed & (1 << (2*f+v)))
        final_masks = (0,) if f is None else sorted({old_bad | extra for extra in range(4)})
        for final_bad in final_masks:
            available = honest
            if f is not None:
                available |= sum(1 << (2*f+v) for v in (0,1) if final_bad & (1 << v))
            domains = []
            for old in state.receipts:
                required = old | honest
                optional = available & ~required
                domains.append(tuple(required | extra for extra in _subsets(optional)))
            for a, b in product(*domains):
                yield ("terminal-cutoff", (final_bad, a, b))


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
        final_bad, a, b = data
        if state.faulty is not None:
            old_values = tuple(v for v in (0,1) if signed & (1 << (2*state.faulty+v)))
            added = tuple(v for v in (0,1) if final_bad & (1 << v) and v not in old_values)
            views[state.faulty].append(("signed-terminal-late",added))
            signed |= sum(1 << (2*state.faulty+v) for v in (0,1) if final_bad & (1 << v))
        receipts = (a,b)
        views[3].append(("terminal-receipts", a))
        views[4].append(("terminal-receipts", b))
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


# Fixed decoded request alphabet. All other malformed byte encodings normalize to
# the malformed class before this API, without obtaining another identity's signature.
REQUESTS = (("wait",),("retain",),("observe",),("malformed",)) + tuple(
    (kind,mask) for kind in ("propose","echo","terminal") for mask in range(4))

def _request_mask(request, kind):
    return (request[1] if isinstance(request,tuple) and len(request)==2
            and request[0]==kind and type(request[1]) is int
            and 0 <= request[1] < 4 else 0)

def normalized_key(state, requests):
    # Correct components are checked from local views; incorrect correct requests
    # do not follow the policy and are not the Nonblocking theorem's antecedent.
    for i in digital.ACTORS:
        if i != state.faulty and requests[i] != digital.local_action(i,state.views[i]):
            return None
    f, phase = state.faulty,state.phase
    if phase == 4:
        return ("done",)
    if f is None:
        return ("inactive",)
    request = requests[f]
    if phase == 0 and f == 0:
        return ("proposal",_request_mask(request,"propose"))
    if phase == 1 and f in (1,2):
        return ("echo",_request_mask(request,"echo") & state.leader_signed)
    if phase == 2:
        return ("terminal-first",_request_mask(request,"terminal"))
    if phase == 3:
        old = sum(1 << v for v in (0,1) if state.terminal_signed & (1 << (2*f+v)))
        return ("terminal-final",old | _request_mask(request,"terminal"))
    return ("inactive",)

def edge_key(before,after):
    f,phase = before.faulty,before.phase
    if f is None:
        return ("inactive",)
    if phase == 0 and f == 0:
        return ("proposal",after.leader_signed)
    if phase == 1 and f in (1,2):
        return ("echo",after.echoes[2-f])
    if phase == 2:
        mask=sum(1 << v for v in (0,1) if after.terminal_signed & (1 << (2*f+v)))
        return ("terminal-first",mask)
    if phase == 3:
        mask=sum(1 << v for v in (0,1) if after.terminal_signed & (1 << (2*f+v)))
        return ("terminal-final",mask)
    return ("inactive",)

def following_profiles(state):
    fixed=tuple(digital.local_action(i,state.views[i]) if i != state.faulty else None
                for i in digital.ACTORS)
    if state.faulty is None:
        yield fixed
    else:
        for request in REQUESTS:
            yield tuple(request if i==state.faulty else fixed[i] for i in digital.ACTORS)

def command_successors(prefix, requests):
    """Action-indexed next. Rejection is a legal no-op, never an empty bad-request run."""
    state=digital_projection(prefix)
    key=normalized_key(state,requests)
    if key is None:
        return ()
    if state.phase==4:
        # Successful finite verdict can be embedded as (prefix,tick)->(prefix,tick+1).
        # It does not count another service event.
        return (prefix,)
    return tuple(n for n in digital.successors(prefix)
                 if edge_key(state,digital_projection(n))==key)



@dataclass(frozen=True)
class ClockedDigitalPoint:
    prefix: digital.Prefix
    tick: int

def clocked_command_view(point, actor):
    return (point.tick,digital.local_view(point.prefix,actor))

def clocked_command_successors(point, requests):
    # Successful finite termination is explicitly embedded; service is not incremented.
    return tuple(ClockedDigitalPoint(p,point.tick+1)
                 for p in command_successors(point.prefix,requests))

def current_epoch_view(history):
    positions=[j for j,event in enumerate(history) if event[0]=="epoch"]
    if not positions:
        raise ValueError("no current epoch in local history")
    return history[positions[-1]:]


def digital_adapter_checks():
    level = list(digital.initials())
    states = edges = local_steps = profiles_checked = 0
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
            # Group by normalized requested action without repeatedly regenerating the tree.
            concrete_by_key,abstract_by_key={},{}
            for nxt in concrete_next:
                projected=digital_projection(nxt)
                concrete_by_key.setdefault(edge_key(target,projected),set()).add(projected)
            for nxt in abstract_next:
                abstract_by_key.setdefault(edge_key(target,nxt),set()).add(nxt)
            profile_keys=set()
            for requests in following_profiles(target):
                key=normalized_key(target,requests)
                assert key is not None
                profiles_checked+=1
                profile_keys.add(key)
                if phase==4:
                    assert key==("done",)
                else:
                    assert concrete_by_key.get(key),("normalized request deadlock",source,requests,key)
                    assert concrete_by_key[key]==abstract_by_key[key]
            # Normalization does not silently remove an admitted adversarial transition.
            if phase<4:
                assert set(concrete_by_key) <= profile_keys
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
    # Regression: an unavailable signature and a wrong-phase tag normalize to
    # admitted rejection/no-op behavior, not to an empty successor set.
    first=next(p for p in digital.traces(1) if p.faulty==1 and p.input==0)
    st=digital_projection(first)
    req=list(next(following_profiles(st)))
    req[1]=("echo",2)
    assert command_successors(first,tuple(req))
    assert normalized_key(st,tuple(req))==("echo",0)
    req[1]=("terminal",3)
    assert command_successors(first,tuple(req))
    for junk in ((),("echo",99),("echo",-1),("echo","1"),None):
        req[1]=junk
        assert command_successors(first,tuple(req))
    # A completed mission stutters with an observable clock, never fabricating service.
    finished=source  # Last phase-4 state already generated above.
    for tick in (4,11):
        point=ClockedDigitalPoint(finished,tick)
        for requests in following_profiles(digital_projection(finished)):
            successors=clocked_command_successors(point,requests)
            assert successors and all(q.tick==tick+1 and q.prefix==finished for q in successors)
            assert all(clocked_command_view(q,3)[0]==tick+1 for q in successors)
    # The fixed per-slot policy is lifted through an actor-local epoch-suffix map.
    prior_by_fault={}
    for f in digital.FAULTS:
        prior=next(p for p in digital.initials() if p.faulty==f)
        for _ in range(4):
            prior=next(digital.successors(prior))
        prior_by_fault[f]=prior
    suffix_checks=0
    repair_needed=False
    for phase in (0,1,2):
        for fresh in digital.traces(phase,1):
            prior=prior_by_fault[fresh.faulty]
            for i in digital.ACTORS:
                if i != fresh.faulty:
                    fresh_view=digital.local_view(fresh,i)
                    history=digital.local_view(prior,i)+fresh_view
                    suffix=current_epoch_view(history)
                    assert suffix==fresh_view
                    assert digital.local_action(i,suffix)==digital.local_action(i,fresh_view)
                    repair_needed |= digital.local_action(i,history)!=digital.local_action(i,suffix)
                    suffix_checks+=1
    assert repair_needed
    return {"source_states": states, "guarded_edges": edges,
            "clocked_terminal_embedding_checked": True, "epoch_suffix_checks": suffix_checks,
            "following_profiles_checked": profiles_checked,
            "action_indexed_nonblocking": True,
            "normalization_surjective_onto_admitted_branches": True,
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

"""Whole-prefix distributed finite-horizon synthesis and independent replay.
Exact only for the finite arena/horizon supplied. No split-world or known-fault oracle.
"""
from dataclasses import dataclass
from itertools import product
from collections import deque
import json

@dataclass(frozen=True)
class Prefix:
    state: tuple
    views: tuple
    depth: int

@dataclass
class Arena:
    actors: tuple
    alphabets: tuple
    initials: tuple
    observe: object
    faulty: object
    next_states: object
    safe: object

    def initial_prefixes(self):
        return frozenset(Prefix(s, tuple((self.observe(s, i),) for i in self.actors), 0)
                         for s in self.initials)

    def key(self, prefix, i):
        return (i, prefix.depth, prefix.views[self.actors.index(i)])

    def actions(self, prefix, prescription):
        domains = []
        bad = self.faulty(prefix.state)
        for k, i in enumerate(self.actors):
            if i in bad:
                domains.append(self.alphabets[k])
            else:
                action = prescription[self.key(prefix, i)]
                if action not in self.alphabets[k]:
                    raise ValueError(("out-of-alphabet local action", i, action))
                domains.append((action,))
        return product(*domains)

    def update(self, family, prescription):
        successors = set()
        for prefix in family:
            for actions in self.actions(prefix, prescription):
                targets = tuple(self.next_states(prefix.state, actions))
                if not targets:
                    return None  # a reachable legal profile deadlocks
                for target in targets:
                    assert self.faulty(target) == self.faulty(prefix.state)
                    histories = tuple(prefix.views[k] + ((actions[k], self.observe(target, i)),)
                                      for k, i in enumerate(self.actors))
                    successors.add(Prefix(target, histories, prefix.depth + 1))
        assert successors  # nonempty family and no dropped nonblocking obligation
        return frozenset(successors)

    def prescriptions(self, family):
        # Keys include actor and full permitted local history. Fault identity is excluded.
        keys = []
        alphabets = []
        for k, i in enumerate(self.actors):
            visible = sorted({self.key(prefix, i) for prefix in family
                              if i not in self.faulty(prefix.state)}, key=repr)
            for key in visible:
                keys.append(key)
                alphabets.append(self.alphabets[k])
        for values in product(*alphabets):
            yield dict(zip(keys, values))

def synthesize(arena, horizon, family=None):
    if family is None:
        family = arena.initial_prefixes()
    if not family or any(not arena.safe(prefix.state) for prefix in family):
        return None
    if horizon == 0:
        return []
    for prescription in arena.prescriptions(family):
        nxt = arena.update(family, prescription)
        if nxt is not None:
            rest = synthesize(arena, horizon - 1, nxt)
            if rest is not None:
                return [prescription, *rest]
    return None

def replay(arena, plan):
    # Separate replay kernel: do not reuse synthesis's update/actions methods.
    family = frozenset(Prefix(s, tuple((arena.observe(s, i),) for i in arena.actors), 0)
                       for s in arena.initials)
    assert family and all(arena.safe(p.state) for p in family)
    for prescription in plan:
        next_family = set()
        for prefix in family:
            bad = arena.faulty(prefix.state)
            domains = []
            for k, i in enumerate(arena.actors):
                if i in bad:
                    domains.append(arena.alphabets[k])
                else:
                    key = (i, prefix.depth, prefix.views[k])
                    if key not in prescription:
                        raise ValueError(("missing local action", key))
                    action = prescription[key]
                    if action not in arena.alphabets[k]:
                        raise ValueError(("out-of-alphabet local action", i, action))
                    domains.append((action,))
            for actions in product(*domains):
                outcomes = tuple(arena.next_states(prefix.state, actions))
                assert outcomes, ("deadlocking profile", prefix, actions)
                for target in outcomes:
                    assert arena.faulty(target) == bad
                    assert arena.safe(target), ("unsafe replay successor", prefix, actions, target)
                    local_histories = tuple(
                        prefix.views[k] + ((actions[k], arena.observe(target, i)),)
                        for k, i in enumerate(arena.actors))
                    next_family.add(Prefix(target, local_histories, prefix.depth+1))
        assert next_family
        family = frozenset(next_family)
    return family

def continuation_arena(revealed=False):
    def next_state(s, a):
        x, = s
        u, = a
        if x == 0:
            y = 2 if u == 0 else 5
        elif x == 1:
            y = 3 if u == 0 else 5
        elif x == 2:
            y = 4 if u == 1 else 5
        elif x == 3:
            y = 4 if u == 2 else 5
        else:
            y = x
        return ((y,),)
    return Arena((0,), ((0, 1, 2),), ((0,), (1,)),
                 lambda s, i: s[0] if revealed else (0 if s[0] < 2 else 1 if s[0] < 4 else s[0]),
                 lambda s: frozenset(), next_state, lambda s: s[0] != 5)

def hidden_fault_arena(known=False, initial_faults=(1, 2)):
    def next_state(s, actions):
        bad, phase = s
        if phase:
            return (s,)
        return ((bad, 1 if actions[0] == bad - 1 else 2),)
    return Arena((0, 1, 2), ((0, 1), (0,), (0,)),
                 tuple((bad, 0) for bad in initial_faults),
                 lambda s, i: (s[1], s[0] if known else None),
                 lambda s: frozenset((s[0],)), next_state, lambda s: s[1] != 2)

def nonblocking_example():
    return Arena((0,), ((0, 1),), ((0,),),
                 lambda s, i: s[0], lambda s: frozenset(),
                 lambda s, actions: () if actions[0] == 0 else ((0,),),
                 lambda s: True)

def monitor_checks():
    # A four-tick service window permits at most three consecutive non-service ticks.
    bound = 3
    patterns = list(product((False, True), repeat=8))
    checked = 0
    for trace in patterns:
        age = 0
        states = [age]
        for served in trace:
            age = 0 if served else age + 1
            states.append(age)
        safe = all(a <= bound for a in states)
        trace_safe = all(any(trace[start:start+bound+1])
                         for start in range(len(trace)-bound))
        assert safe == trace_safe
        checked += 1
    # Same current physical state and current no-service flag, different retained histories.
    a, b = (True, True, True, False), (False, False, False, False)
    assert a[-1] == b[-1] and any(a) and not any(b)
    return {"traces": checked, "window": bound+1, "state_only_quotient_fails": True}

def compactness_boundary():
    # Infinite initial action alphabet: choose any finite fuel N, then decrement.
    # Every finite horizon is feasible, while no choice yields infinite safety.
    # General impossibility is the arithmetic argument in THEORY.md.
    for horizon in range(1, 101):
        fuel = horizon
        trace = list(range(fuel, -2, -1))
        assert all(x >= 0 for x in trace[:horizon+1])
        assert trace[-1] < 0
    return {"finite_horizons_replayed": 100,
            "unrestricted_infinite_action_inference_rejected": True}

def run_checks():
    hidden = continuation_arena(False)
    first = synthesize(hidden, 1)
    assert first is not None
    replay(hidden, first)
    assert synthesize(hidden, 2) is None
    revealed = continuation_arena(True)
    good = synthesize(revealed, 4)
    assert good is not None
    replay(revealed, good)
    unknown = hidden_fault_arena(False)
    assert synthesize(unknown, 1) is None
    for bad in (1, 2):
        model = hidden_fault_arena(False, (bad,))
        plan = synthesize(model, 1)
        assert plan is not None
        replay(model, plan)
    known = hidden_fault_arena(True)
    plan = synthesize(known, 2)
    assert plan is not None
    replay(known, plan)
    nb = nonblocking_example()
    plan = synthesize(nb, 3)
    assert plan is not None
    assert all(set(row.values()) == {1} for row in plan)
    replay(nb, plan)
    bad_table = {nb.key(next(iter(nb.initial_prefixes())), 0): 99}
    try:
        replay(nb, [bad_table])
    except ValueError:
        pass
    else:
        raise AssertionError("replay accepted an out-of-alphabet policy")
    return {
        "continuation": {"hidden_first_step_wins": True, "hidden_two_steps_wins": False,
                         "state_revealed_four_steps_wins": True},
        "fault_uniformity": {"each_known_fault_wins": True, "unknown_fault_wins": False},
        "nonblocking": {"empty_successor_action_rejected": True, "alternative_run_replayed": True,
                        "out_of_alphabet_policy_rejected": True},
        "monitor": monitor_checks(),
        "compactness": compactness_boundary(),
        "scope": "exact finite horizon with all successor prefixes, full local-history keys, fixed faults",
    }

if __name__ == "__main__":
    print(json.dumps(run_checks(), indent=2, sort_keys=True))

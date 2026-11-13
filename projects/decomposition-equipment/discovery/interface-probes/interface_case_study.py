"""Finite checks for safety, diagnosis, observation transport, and probe composition.

Run with Python 3.10 or later. No third-party packages are required.
All choices below are adversarial possibilities, not probabilities.
"""
from __future__ import annotations

from functools import lru_cache
from itertools import product
import json
from typing import Callable, Iterable


def powerset(items: Iterable):
    items = tuple(items)
    for bits in product((False, True), repeat=len(items)):
        yield frozenset(x for x, keep in zip(items, bits) if keep)


def diagnostic_decoders(outcomes: dict[int, frozenset]):
    """All deterministic reports, required correct for every allowed outcome."""
    alphabet = tuple(sorted(set().union(*outcomes.values()), key=repr))
    result = []
    for values in product((0, 1), repeat=len(alphabet)):
        decoder = dict(zip(alphabet, values))
        if all(decoder[y] == h for h, ys in outcomes.items() for y in ys):
            result.append(decoder)
    return result


# Eight plant/monitor states. Correctness of a report is NOT exposed to the tester.
Q = tuple(("unprobed", h) for h in (0, 1))
P = tuple(("probed", h) for h in (0, 1))
D = tuple(("done", h, k) for h in (0, 1) for k in (0, 1))
STATES = Q + P + D
ACTIONS = ("probe", "report0", "report1")
BAD = frozenset(s for s in D if s[1] != s[2])


def transitions(channel: str, state: tuple, action: str):
    """Return (observation, next_state) pairs; empty means action disabled."""
    if action == "probe" and state[0] == "unprobed":
        h = state[1]
        if channel == "revealing":
            y = h
        elif channel == "inverted":
            y = 1 - h
        elif channel == "blind":
            y = "*"
        else:
            raise ValueError(f"Unknown channel: {channel}")
        return ((y, ("probed", h)),)
    if action in ("report0", "report1") and state[0] != "done":
        k = int(action[-1])
        # Only the report is observed, not whether it is correct.
        return ((f"reported{k}", ("done", state[1], k)),)
    return ()


def wp(channel: str, action: str, postcondition: frozenset):
    """State-only total-correctness WP of an atomic, terminating action."""
    result = set()
    for s in STATES:
        successors = transitions(channel, s, action)
        if successors and all(t in postcondition for _, t in successors):
            result.add(s)
    return frozenset(result)


def universally_safe(channel: str, script: tuple[str, ...]):
    current = frozenset(Q)
    for action in script:
        if any(not transitions(channel, s, action) for s in current):
            return False
        current = frozenset(
            t for s in current for _, t in transitions(channel, s, action)
        )
        if current & BAD:
            return False
    return True


def synthesize(worlds: tuple[tuple[int, ...], ...],
               probes: dict[str, Callable[[tuple[int, ...]], int]]):
    """Exact finite synthesis; each probe may be used at most once.

    The first coordinate of each world is its true classification. A policy
    either issues a uniformly correct report or selects an unused probe and
    supplies a winning continuation for EVERY feasible observation.
    """
    @lru_cache(None)
    def solve(belief: frozenset, unused: tuple[str, ...]):
        classes = {w[0] for w in belief}
        if len(classes) == 1:
            return {"report": next(iter(classes))}
        for action in unused:
            partition: dict[int, set] = {}
            for w in belief:
                partition.setdefault(probes[action](w), set()).add(w)
            rest = tuple(a for a in unused if a != action)
            branches = {}
            for y, group in sorted(partition.items()):
                continuation = solve(frozenset(group), rest)
                if continuation is None:
                    break
                branches[y] = continuation
            else:
                return {"probe": action, "branches": branches}
        return None
    return solve(frozenset(worlds), tuple(sorted(probes)))


def outcome_relation(worlds, probes_in_order):
    return {
        h: frozenset(tuple(p(w) for p in probes_in_order)
                     for w in worlds if w[0] == h)
        for h in (0, 1)
    }


def main():
    # Strong separation: all 256 state predicates, for all three actions.
    wp_cases = 0
    for postcondition in powerset(STATES):
        for action in ACTIONS:
            assert wp("revealing", action, postcondition) == wp("blind", action, postcondition)
            wp_cases += 1
    assert wp_cases == 768

    scripts = ((), ("probe",), ("report0",), ("report1",),
               ("probe", "report0"), ("probe", "report1"))
    safety = {}
    for script in scripts:
        left = universally_safe("revealing", script)
        right = universally_safe("blind", script)
        assert left == right
        safety["; ".join(script) or "empty"] = left

    channels = {
        "revealing": {0: frozenset({0}), 1: frozenset({1})},
        "inverted": {0: frozenset({1}), 1: frozenset({0})},
        "blind": {0: frozenset({"*"}), 1: frozenset({"*"})},
    }
    decoders = {name: diagnostic_decoders(rel) for name, rel in channels.items()}
    assert decoders["revealing"] == [{0: 0, 1: 1}]
    assert decoders["inverted"] == [{0: 1, 1: 0}]
    assert decoders["blind"] == []

    # Every nonempty binary observation relation satisfies the separation theorem.
    supports = tuple(x for x in powerset((0, 1)) if x)
    channel_cases = 0
    for ys0, ys1 in product(supports, repeat=2):
        assert bool(diagnostic_decoders({0: ys0, 1: ys1})) == ys0.isdisjoint(ys1)
        channel_cases += 1
    assert channel_cases == 9

    shared_worlds = tuple(product((0, 1), repeat=2))  # (h,r)
    shared = {"a": lambda w: w[1], "b": lambda w: w[1] ^ w[0]}
    fresh_worlds = tuple(product((0, 1), repeat=3))  # (h,r_a,r_b)
    fresh = {"a": lambda w: w[1], "b": lambda w: w[2] ^ w[0]}

    for action in ("a", "b"):
        marginal_shared = outcome_relation(shared_worlds, (shared[action],))
        marginal_fresh = outcome_relation(fresh_worlds, (fresh[action],))
        assert marginal_shared == marginal_fresh
        assert diagnostic_decoders(marginal_shared) == []

    shared_joint = outcome_relation(shared_worlds, (shared["a"], shared["b"]))
    fresh_joint = outcome_relation(fresh_worlds, (fresh["a"], fresh["b"]))
    shared_decoders = diagnostic_decoders(shared_joint)
    fresh_decoders = diagnostic_decoders(fresh_joint)
    assert shared_decoders == [{(0, 0): 0, (0, 1): 1, (1, 0): 1, (1, 1): 0}]
    assert fresh_decoders == []
    # Minimal residual interfaces for the fixed grammar a; b; report.
    # A residual signature lists which complete continuation policies are safe.
    stage1_signatures = {}
    stage2_signatures = {}
    binary_decoders = tuple(product((0, 1), repeat=2))
    for first in (0, 1):
        belief = tuple(w for w in shared_worlds if shared["a"](w) == first)
        stage1_signatures[first] = tuple(
            all(decoder[shared["b"](w)] == w[0] for w in belief)
            for decoder in binary_decoders
        )
        for second in (0, 1):
            final_belief = tuple(w for w in belief if shared["b"](w) == second)
            stage2_signatures[(first, second)] = tuple(
                all(k == w[0] for w in final_belief) for k in (0, 1)
            )
    residual_counts = (1, len(set(stage1_signatures.values())),
                        len(set(stage2_signatures.values())))
    assert residual_counts == (1, 2, 2)
    assert stage1_signatures[0] != stage1_signatures[1]
    assert stage2_signatures[(0, 0)] == stage2_signatures[(1, 1)]
    assert stage2_signatures[(0, 1)] == stage2_signatures[(1, 0)]
    policy = synthesize(shared_worlds, shared)
    assert policy is not None
    assert synthesize(fresh_worlds, fresh) is None

    print(json.dumps({
        "equal_state_only_wp_cases": wp_cases,
        "open_loop_universal_safety": safety,
        "one_probe_winning_decoder_counts": {k: len(v) for k, v in decoders.items()},
        "exhaustive_binary_channel_cases": channel_cases,
        "two_probe_decision_tables_checked_per_channel": 16,
        "shared_mask_winning_decoder_count": len(shared_decoders),
        "fresh_masks_winning_decoder_count": len(fresh_decoders),
        "minimal_nonterminal_residual_states_by_phase": residual_counts,
        "minimal_nonterminal_residual_states_total": sum(residual_counts),
        "synthesized_shared_mask_strategy": policy,
        "all_assertions_passed": True,
    }, indent=2))


if __name__ == "__main__":
    main()

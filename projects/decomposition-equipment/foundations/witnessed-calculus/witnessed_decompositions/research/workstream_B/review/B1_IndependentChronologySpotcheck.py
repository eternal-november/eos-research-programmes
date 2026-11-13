#!/usr/bin/env python3
"""Reviewer-owned finite check; no imports from the author's tree/checker code.

This validates one six-event mixed-interface chronology against an independently
maintained frontier list and internal-address set. It is C support, not proof of
the unrestricted P result.
"""
from itertools import permutations
from math import factorial
import json

P, X, Q, W = (0, 1), (1, 1), (1, 2), (0, 2)
initial = [((0,), P), ((1,), X), ((2,), X), ((3,), Q)]
events = {
    (1,): ("binary", X, (X, X)),
    (1, 0): ("unary", X, (X,)),
    (1, 1): ("nullary", X, ()),
    (2,): ("other-binary", X, (X, X)),
    (2, 0): ("unary", X, (X,)),
    (2, 1): ("unary", X, (X,)),
}

def precedes(a, b):
    return len(a) < len(b) and b[:len(a)] == a

def execute(order):
    frontier = list(initial)
    internal = {()}
    for address in order:
        _, output, inputs = events[address]
        positions = [i for i, entry in enumerate(frontier) if entry == (address, output)]
        if len(positions) != 1:
            return None
        rank = positions[0]
        old = list(frontier)
        replacement = [(address + (i,), component) for i, component in enumerate(inputs)]
        frontier[rank:rank+1] = replacement
        internal.add(address)
        assert address in internal
        assert all(address != a for a, _ in frontier)
        for j, entry in enumerate(old):
            if j != rank:
                expected = j if j < rank else j + len(inputs) - 1
                assert frontier[expected] == entry
    return frontier, internal

def main():
    expected_frontier = [((0,), P), ((1, 0, 0), X), ((2, 0, 0), X),
                         ((2, 1, 0), X), ((3,), Q)]
    legal, extensions = set(), set()
    for order in permutations(events):
        result = execute(order)
        if result is not None:
            legal.add(order)
            assert result == (expected_frontier, {()} | set(events))
        ranks = {event: i for i, event in enumerate(order)}
        if all(ranks[a] < ranks[b] for a in events for b in events if precedes(a, b)):
            extensions.add(order)
    assert legal == extensions
    # Each of the two three-element rooted branches has its root first.
    assert len(legal) == factorial(6) // (3 * 3) == 80
    seen = {next(iter(legal))}
    pending = list(seen)
    swaps = 0
    while pending:
        order = pending.pop()
        for i in range(5):
            a, b = order[i:i+2]
            if not precedes(a, b) and not precedes(b, a):
                swapped = order[:i] + (b, a) + order[i+2:]
                assert swapped in legal
                swaps += 1
                if swapped not in seen:
                    seen.add(swapped)
                    pending.append(swapped)
    assert seen == legal
    assert execute(((1, 0), (1,), (1, 1), (2,), (2, 0), (2, 1))) is None
    print(json.dumps({"status": "PASS", "evidence_class": "C only",
                      "candidate_orders": factorial(6), "legal_orders": len(legal),
                      "all_interchange_connected": True,
                      "directed_adjacent_swap_checks": swaps,
                      "typed_initial_frontier": [list(c) for _, c in initial],
                      "final_leaf_count": len(expected_frontier),
                      "nullary_address_retained_as_internal": True,
                      "dependent_reversal_rejected": True}, indent=2))

if __name__ == "__main__":
    main()

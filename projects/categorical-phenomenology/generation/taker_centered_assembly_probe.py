"""Finite, executable probe: two independent sources classified by a taker.

Tests three interfaces:
  (1) a joint-source closure/readout T @ (A x B),
  (2) a closure-free declaration with an optional proof-relevant ground,
  (3) a (taker-indexed) proof-relevant span of grounded episodes.

Claims about *interpretation* in the accompanying analysis are design claims;
this script checks only the finite set-theoretic assertions.
"""
from itertools import product

BITS = (0, 1)
PAIRS = tuple(product(BITS, repeat=2))


def grounds(taker: str, a: int, b: int) -> tuple[str, ...]:
    """Which admissible grounds the evaluator has for asserting ALERT."""
    if taker == "either":
        return (("left",) if a else ()) + (("right",) if b else ())
    if taker == "both":
        return ("joint",) if (a and b) else ()
    raise ValueError(taker)


def raw_claim(taker: str, a: int, b: int) -> tuple[str, int, int, str]:
    """An assertion is formable even when it has no admissible ground."""
    return (taker, a, b, "alert")


def extensional_relation(taker: str) -> frozenset[tuple[int, int]]:
    return frozenset((a, b) for a, b in PAIRS if grounds(taker, a, b))


def witness_span(taker: str) -> tuple[tuple[int, int, str], ...]:
    return tuple((a, b, w) for a, b in PAIRS for w in grounds(taker, a, b))


def difunctional(relation: set[tuple[int, int]] | frozenset[tuple[int, int]]) -> bool:
    # aRb, a'Rb, a'Rb' => aRb'
    return all(
        (a, b_prime) in relation
        for a, a_prime, b, b_prime in product(BITS, repeat=4)
        if (a, b) in relation and (a_prime, b) in relation
        and (a_prime, b_prime) in relation
    )


def cospan_equalizer_relation(da: tuple[int, int], db: tuple[int, int]):
    return frozenset((a, b) for a, b in PAIRS if da[a] == db[b])


def jointly_match_readout(a: int, b: int, report: int) -> bool:
    """Single, legitimate joint-source closure: d: A x B -> Bool is OR;
    occurrence map p: T -> Bool is identity on the report states.
    """
    return int(bool(a or b)) == report


def preferred_followup_action(a: int, b: int) -> str:
    """A declared operational rule: route to left if present, else right, else idle."""
    return "left" if a else ("right" if b else "idle")


def run_checks() -> None:
    either = extensional_relation("either")
    both = extensional_relation("both")
    assert either == {(1, 0), (0, 1), (1, 1)}
    assert both == {(1, 1)}
    assert not difunctional(either)
    assert sum(bool(grounds("either", a, b)) for a, b in PAIRS) == 3
    assert {pair: len(grounds("either", *pair)) for pair in PAIRS} == {
        (0, 0): 0, (0, 1): 1, (1, 0): 1, (1, 1): 2
    }
    assert len(witness_span("either")) == 4
    assert len({(a, b) for a, b, w in witness_span("either")}) == 3

    # A fixed cospan of unary maps A -> X <- B cannot represent OR
    # via equality matching. Exhaustive for finite codomains sizes 1..4;
    # difunctionality supplies the size-independent proof.
    checked = 0
    for n in range(1, 5):
        for da in product(range(n), repeat=2):
            for db in product(range(n), repeat=2):
                checked += 1
                assert cospan_equalizer_relation(da, db) != either

    # But one joint-source closure d:A x B -> Bool does it exactly,
    # with the original endpoints still available as named input ports.
    assert {(a, b) for a, b in PAIRS if jointly_match_readout(a, b, 1)} == either

    # The raw assertion is available even at (0,0); groundedness is extra.
    assert raw_claim("either", 0, 0) == ("either", 0, 0, "alert")
    assert grounds("either", 0, 0) == ()

    # No action using *only the one-bit alert* can implement routing.
    # Both (1,0) and (0,1) produce alert=1 but require different actions.
    actions = ("left", "right", "idle")
    assert not any(
        all(q[int(bool(a or b))] == preferred_followup_action(a, b)
            for a, b in PAIRS)
        for q in product(actions, repeat=2)
    )

    # Joint compatibility of independently acceptable constraints differs
    # from accepting each constraint with independent witness choices.
    g11 = set(grounds("either", 1, 1))
    left = {"left"}
    right = {"right"}
    assert (g11 & left) and (g11 & right) and not (g11 & left & right)
    assert any(x in left and y in right for x, y in product(g11, repeat=2))

    # Changing only the taker's rubric changes the interpreted relation,
    # not the independently stipulated source state space/distribution.
    assert either != both
    assert set(PAIRS) == set(product(BITS, BITS))
    assert sum((1 / 4) for _ in PAIRS) == 1

    print("PASS: independent sources; differing taker rubrics; unsupported claims")
    print("PASS: 3 supported endpoint pairs but 4 distinct support witnesses")
    print(f"PASS: OR support is non-difunctional; {checked} unary-cospan cases excluded")
    print("PASS: joint-source closure realizes OR; unary equalizer cannot")
    print("PASS: provenance-sensitive action cannot factor through OR alone")
    print("PASS: pairwise grounds need not share a single selected witness")
    print("NOTE: exact semantic comparison of presentation styles remains a design judgment")


if __name__ == "__main__":
    run_checks()

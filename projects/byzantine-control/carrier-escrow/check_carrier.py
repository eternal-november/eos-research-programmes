"""One interrupted transfer on the discrete carrier source in OPERATION.md."""
from collections import Counter
from dataclasses import dataclass
from itertools import product
from pathlib import Path
import sys

PORT = Path(__file__).resolve().parents[1] / "portability"
sys.path.insert(0, str(PORT))
from constructors import PhaseEdge, phase_family_budget, projected_support


def check(condition, message):
    if not condition:
        raise ValueError(message)


DOCKS = ("P", "Q")
# This query concerns direct local stroke opportunities over both visits.
# The sender cutoff can leave a material descendant, but cannot disable a dock.
QUERY = "dock stroke on this pass"
FOOTPRINTS = {
    "dispatch cut": {QUERY: frozenset()},
    "P": {QUERY: frozenset({"P"})},
    "Q": {QUERY: frozenset({"Q"})},
}


def frozen_budget():
    # Work covers belt and both possible local strokes, even on an empty pocket.
    # The old source kick was already funded. Its stock is accounted separately.
    stages = ("staged", "departed", "at P", "past P", "at Q",
              "past Q", "home", "inspection")
    bounds = [(2, 2), (3, 3), (1, 2), (2, 2), (1, 2), (3, 3), (1, 1)]
    laws = ["indexed launch dog", "first three-pitch span", "P dwell and cell",
            "two-pitch span", "Q dwell and cell", "three-pitch return", "home detent"]
    edges = [PhaseEdge(a, b, dt, work, law)
             for (a, b), (dt, work), law in zip(zip(stages, stages[1:]), bounds, laws, strict=True)]
    ranks = {s: len(stages) - i - 1 for i, s in enumerate(stages)}
    return phase_family_budget(ranks, frozenset({"inspection"}), edges, stages[:2])


@dataclass(frozen=True)
class Timing:
    launch: int
    first_leg: int
    middle_leg: int
    return_leg: int
    fall_p: int
    fall_q: int


def timings():
    for args in product((0, 1, 2), (2, 3), (1, 2), (2, 3), (1, 2), (1, 2)):
        yield Timing(*args)


def fresh_stroke(levels):
    """Both samples are taken after alignment; a held level cannot rearm a new visit."""
    first, second = levels
    return not first and second


def trace(timing, bad, commands, settle_first):
    """Follow one physical pass. One visit's receipt never supplies a later command."""
    disabled = projected_support(("dispatch cut", *bad), FOOTPRINTS, QUERY)
    p_stroke = timing.launch + timing.first_leg + 1
    q_stroke = p_stroke + timing.middle_leg + 1
    home = q_stroke + timing.return_leg
    inspect = home + 1
    pocket = 1
    chutes = {dock: 0 for dock in DOCKS}
    bins = {dock: 0 for dock in DOCKS}
    cell_spent = {dock: 0 for dock in DOCKS}
    cell_dumped = {dock: 0 for dock in DOCKS}
    due = {}
    first_credit = None
    views = {}
    for tick in range(inspect + 1):
        dock_here = "P" if tick == p_stroke else "Q" if tick == q_stroke else None
        actions = ("land", "stroke") if settle_first else ("stroke", "land")
        for action in actions:
            if action == "land":
                for dock in DOCKS:
                    if due.get(dock) == tick:
                        check(chutes[dock] == 1, "A chute settled an absent tile")
                        chutes[dock] -= 1
                        bins[dock] += 1
                        if first_credit is None:
                            first_credit = tick
            elif dock_here is not None:
                dock = dock_here
                # Healthy logic reads only dock contact and pocket occupancy.
                # A faulty dock may spend its cell against an empty stop.
                # Pocket occupancy is stable between the entry sample and this stroke.
                levels = commands[dock] if dock in disabled else (False, bool(pocket))
                if fresh_stroke(levels):
                    cell_spent[dock] += 1
                    if pocket:
                        pocket -= 1
                        chutes[dock] += 1
                        delay = timing.fall_p if dock == "P" else timing.fall_q
                        due[dock] = tick + delay
                # Trailing-edge cam opens the drive and bleeds the remainder once.
                cell_dumped[dock] = 1 - cell_spent[dock]
            check(pocket + sum(chutes.values()) + sum(bins.values()) == 1,
                  "Material lost or duplicated at an intermediate cut")
            check(sum(bins.values()) <= 1, "Duplicate credited delivery")
        if tick == 4:
            # Sender knows the clock and home contact. All ACKs are absent.
            views[tick] = ((tick, tick >= home, None), tuple(bins.values()))

    check(not any(chutes.values()) and home > 1, "Outstanding old physical action at inspection")
    check(max(cell_spent.values()) <= 1, "A dock spent twice")
    dock_work = sum(cell_spent.values()) + sum(cell_dumped.values())
    check(dock_work == 2, "Each endowment must be spent or dumped at its own dock")
    return tuple(bins.values()), first_credit, inspect, pocket == 0, dock_work, views


def main():
    budget = frozen_budget()
    check((budget.time_bound, budget.work_bound) == (13, 15), "Unexpected frozen budget")
    terminal = Counter()
    max_credit = max_inspect = max_work = 0
    for timing in timings():
        for bad in ((), ("P",), ("Q",)):
            levels = tuple(product((False, True), repeat=2))
            for choices in product(levels, repeat=len(bad)):
                commands = dict(zip(bad, choices))
                results = [trace(timing, bad, commands, order) for order in (True, False)]
                check(results[0] == results[1], "An admitted settlement order changed the result")
                for bins, credit, inspect, empty, spent, _ in results:
                    check(sum(bins) == 1 and empty and credit <= 11 and inspect < 14,
                          "Missing receipt or empty reusable pocket")
                    check(inspect <= budget.time_bound and inspect + spent <= budget.work_bound,
                          "Frozen scalar budget exceeded")
                    terminal[bins] += 1
                    max_credit = max(max_credit, credit)
                    max_inspect = max(max_inspect, inspect)
                    max_work = max(max_work, inspect + spent)
    check(set(terminal) == {(1, 0), (0, 1)}, "Both delivery alternatives must be possible")
    check((max_credit, max_inspect, max_work) == (11, 13, 15), "Lost sharp timing or work witness")

    timing = Timing(0, 2, 2, 2, 1, 1)
    seen_p = trace(timing, ("P",), {"P": (False, True)}, True)[-1][4]
    seen_transit = trace(timing, ("P",), {"P": (True, True)}, True)[-1][4]
    check(seen_p[0] == seen_transit[0] and (seen_p[1], seen_transit[1]) == ((1, 0), (0, 0)),
          "Sender observation should agree while actual service differs")
    # A single mobile fault misses P then Q. Passing both visits on time is still possible.
    p_end = timing.launch + timing.first_leg + 1
    q_end = p_end + timing.middle_leg + 1
    visits = {"P": (p_end - 1, p_end), "Q": (q_end - 1, q_end)}
    peak = max(sum(start <= tick <= end for start, end in visits.values())
               for tick in range(q_end + 1))
    check(peak == 1, "The two faulty visit intervals must not overlap")
    no_service = trace(timing, tuple(visits), dict.fromkeys(visits, (True, True)), True)
    check(not fresh_stroke((True, True)) and fresh_stroke((False, True)),
          "A stale level was accepted at a freshly funded visit")
    check(no_service[0] == (0, 0) and not no_service[3], "Mobile-fault boundary lost")
    print(f"{terminal.total()} schedule/command/tie cases; settlements {dict(terminal)}")
    print(f"latest receipt {max_credit}; inspected home {max_inspect}; belt+docks work {max_work}")
    print(f"old source parcel <=1 separately; total <= {max_work + 1}")
    print(f"same sender view {seen_p[0]} at tick 4, credited {seen_p[1]} or {seen_transit[1]}")
    print(f"mobile omissions: peak {peak}, receipts {no_service[0]}, empty pocket {no_service[3]}")


if __name__ == "__main__":
    main()

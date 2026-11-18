"""Bind the joint-window rule to the original carrier's timed source."""
from itertools import product
from pathlib import Path
import sys

from cover import Blocked, RouteTime, certify, deadline_profile, minimal_blockers, project_windows

CARRIER = Path(__file__).resolve().parents[1] / "carrier-escrow"
sys.path.insert(0, str(CARRIER))
import check_carrier as source


def fault_windows(mobile):
    sites = ("healthy", "P", "Q")
    def visit(dock):
        return lambda site: [(site, {dock} if dock == site else set())]
    def between(site):
        return [(other, set()) for other in (sites if mobile else (site,))]
    return project_windows(sites, (visit("P"), between, visit("Q")))


def run():
    routes = [frozenset({dock}) for dock in source.DOCKS]
    windows = fault_windows(mobile=False)
    masks = tuple(windows)
    source.check(set(masks) == {frozenset(), *routes}, "Unsound fixed-site window projection")
    check = source.check
    times = [RouteTime(routes[0], 6), RouteTime(routes[1], 9)]
    bound, profile = deadline_profile(times, masks)
    check(bound == 9 and minimal_blockers(routes) == {frozenset(source.DOCKS)},
          "Wrong latest commitment or denial obstruction")
    worst = {mask: 0 for mask in masks}
    count = 0
    earlier_alternative = False
    for timing in source.timings():
        for mask in masks:
            witness = profile[mask]
            for levels in product(tuple(product((False, True), repeat=2)), repeat=len(mask)):
                commands = dict(zip(mask, levels))
                for order in (True, False):
                    counts, landed, inspect, empty, work, _ = source.trace(timing, mask, commands, order)
                    check(sum(counts) == 1 and empty, "Physical single receipt or empty return failed")
                    owner = source.DOCKS[counts.index(1)]
                    # No ACK timestamp is used. These are the real terminal and the
                    # delay of the chute entered on the SAME schedule.
                    fall = timing.fall_p if owner == "P" else timing.fall_q
                    stroke = landed - fall
                    check(stroke <= witness.commit_by and landed <= witness.commit_by + 2,
                          "Surviving local opportunity did not certify this run in time")
                    check(inspect < 14 and inspect + work + 1 <= 16,
                          "Source-specific retirement or resource bound changed")
                    if witness.route == {"Q"} and owner == "P":
                        earlier_alternative = True
                    worst[mask] = max(worst[mask], landed)
                    count += 1
    check(earlier_alternative, "The proof route need not be the physical winner")
    check(worst == {frozenset(): 8, frozenset({"P"}): 11, frozenset({"Q"}): 8},
          "Per-window settled deadlines changed")
    # One bad participant may move between the separated visits on this larger grade.
    timing = source.Timing(0, 2, 2, 2, 1, 1)
    missed = frozenset(source.DOCKS)
    mobile_path = fault_windows(mobile=True)[missed]
    check(mobile_path[0].before == "P" and mobile_path[-1].before == "Q"
          and all(a.after == b.before for a, b in zip(mobile_path, mobile_path[1:])),
          "The obstruction must belong to one actual moving-site history")
    try:
        certify(routes, [missed])
    except Blocked as exc:
        check(exc.mask == missed and len(exc.hits) == 2, "Lost blocking witnesses")
    else:
        raise AssertionError("Both physical visits can be missed")
    counts, _, _, empty, _, _ = source.trace(timing, missed, dict.fromkeys(missed, (True, True)), True)
    check(counts == (0, 0) and not empty, "This obstructing mask has a source witness")
    return count, bound, worst


if __name__ == "__main__":
    n, deadline, latest = run()
    print(f"{n} source schedules; commitment by {deadline}; settled by {max(latest.values())}; "
          "settlement 8/11/8 for no/P/Q denial; mobile two-visit loss reproduced.")

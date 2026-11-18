"""Check the unchanged threshold helper's abort commands and conditional time budgets.

Run from any directory using unoptimized Python 3.12. The calls below exercise
private continuations of the compiled helper. The supplied input words are
observation fixtures, not a constructed timeline of physical publications.
"""
from fractions import Fraction
import json
from pathlib import Path
import sys

import threshold_design as design
import threshold_program_model as program


HERE = Path(__file__).resolve().parent
Q = Fraction


def record(name):
    return json.loads((HERE / name).read_text(encoding="utf-8"))


def check_helper(isa, compiled, bounds):
    constants = compiled.constants
    ports = program.ports_class(isa)(compiled)
    base = constants["TARGET_BASE"]
    machine, view = program.helper_fixture(isa, compiled, ports, 0, 0)
    # Begin with a finished stage-27 qualification, not an asserted boot history.
    machine.W[base + constants["STAGE_ID"]] = 27
    machine.W[base + constants["STAGE_WAIT"]] = 0
    cases = [
        # name, FULL, ENTERING, NORMAL_STOP, anchor-cam-entry, expected MODE, expected X
        ("cleanup-verified", 1, 0, 0, 1, -20, 1),
        ("reentry-with-old-owner", 0, 1, 0, 0, -20, 1),
        ("repeat-reentry-visit", 0, 1, 0, 0, -20, 1),
        ("seat-starts-post-wait", 0, 0, 1, 1, -20, 1),
        ("lost-seat-observation", 0, 1, 0, 0, -20, 1),
    ]
    limit = bounds["instruction_upper_bounds"]["helper"] + 100
    for name, full, entering, normal, anchor, expected_mode, expected_x in cases:
        view[constants["ABORT_FULL"]] = full
        view[constants["MODE"]] = entering
        view[constants["NORMAL_STOP"]] = normal
        view[constants["CAM_ENTRY_A"]] = anchor
        ports.set_view(0, view)
        program.call(isa, compiled, ports, "helper", (0,), limit, machine)
        command = next(event for event in reversed(ports.events) if event[0] == "command")
        assert command[2] == 26 and command[5] == expected_mode, name
        assert machine.W[base + constants["EXITING_ABORT"]] == expected_x, name
        if name == "seat-starts-post-wait":
            assert machine.W[base + constants["EXIT_OBSERVED"]] == 1
            assert machine.W[base + constants["EXIT_WAIT"]] == constants["POST_STAGE_FRAMES"]
        if name == "lost-seat-observation":
            assert machine.W[base + constants["EXIT_OBSERVED"]] == 0
            assert machine.W[base + constants["EXIT_WAIT"]] == 0

    for full, entering, cam_entry in [(0, 1, 0), (1, 0, 0)]:
        ports = program.ports_class(isa)(compiled)
        clean, view = program.helper_fixture(isa, compiled, ports, 0, 0)
        clean.W[base + constants["STAGE_ID"]] = 27
        clean.W[base + constants["ABORT"]] = 1
        clean.W[base + constants["TIMER"]] = 0
        for field, value in [("MODE", entering), ("NORMAL_STOP", 0),
                             ("ABORT_FULL", full), ("CAM_ENTRY_A", cam_entry)]:
            view[constants[field]] = value
        ports.set_view(0, view)
        program.call(isa, compiled, ports, "helper", (0,), limit, clean)
        command = next(event for event in reversed(ports.events) if event[0] == "command")
        assert (command[2], command[4], command[5]) == (26, 0, 20)
        assert clean.W[base + constants["EXITING_ABORT"]] == 0
        if full:
            # The abort signature wait mutes the fresh substantive action,
            # while the positive mode command survives the same flush.
            assert command[6] == 0 and command[8] == 0



def check_bounds(c, geometry, itinerary):
    phase = geometry["arithmetic"]
    age = Q(record("publication_timing_results.json")["receipts"]["maintenance"]["singleton_age"])
    minimum, maximum = (Q(phase["frames"][name]) for name in ("min", "max"))
    poll = Q(phase["polling"])
    settle = Q(phase["ordinary_settle"])
    boot = Q(phase["vectors"]["boot"])
    half = Q(itinerary["fresh_half_allocation"])
    assert half == Q(phase["fresh_half_time"])
    # L needs no stale private FULL stage, and U additionally needs all the
    # persistent contacts/coverage listed in the accompanying proof.
    lower = (c["ENTRY_FRAMES"] + c["POST_STAGE_FRAMES"] - 1) * minimum
    upper = boot + (c["ENTRY_FRAMES"] + 1) * maximum + 2 * poll
    upper += (c["POST_STAGE_FRAMES"] + 1) * maximum + 2 * poll + 15
    distance = Q(11, 10) * (upper - lower)
    assert lower == Q(619500, 101) and upper == Q(465985497733, 67108864)
    assert Q(891) < distance < 892

    # From any healthy normal band, its next 26 completed phase endpoints
    # include a phase-10 old-side cutoff on each half. Partial first bands
    # require the source's ordinary remaining-edge bound; the calculation
    # assigns the full first band conservatively.
    edge_times = {int(name.split("_", 1)[0]): Q(cost)
                  for name, cost in phase["phase_bounds"].items()}
    assert set(edge_times) == set(range(13))
    band = Q(phase["band_travel"]) / 13
    for start in range(26):
        cut_sides = set()
        elapsed = Q(0)
        for offset in range(26):
            side, phase_index = divmod((start + offset) % 26, 13)
            elapsed += edge_times[phase_index] + band
            if phase_index == 10:
                cut_sides.add(side)
        assert cut_sides == {0, 1} and elapsed == 2 * half

    def force_floor(ambiguous_good_hosts):
        return (2 * (34 - ambiguous_good_hosts)
                - Q(44, 10) * (6 + ambiguous_good_hosts) - Q(11, 10) - Q(324, 1000))

    assert force_floor(0) == Q(5022, 125)
    assert force_floor(1) > 29 + 2 and force_floor(2) < 28
    entering_edge = age + poll + maximum + 1 + 2 * half + settle + 10000
    assert entering_edge == Q(144430816876333325, 4718592)
    assert entering_edge + Q(itinerary["corrected_sequence_allocation"]) < Q(itinerary["H"])
    return {"first_eligible_exit_lower": str(lower), "joined_by_if_return_persists": str(upper),
            "distance_after_first_possible_exit_before_join": str(distance),
            "conditional_entering_edge": str(entering_edge), "force_floor_one_ambiguous_pair": str(force_floor(1))}


def main():
    if sys.version_info[:2] != (3, 12) or not __debug__:
        raise SystemExit("Use unoptimized Python 3.12")
    isa = program.load_isa()
    compiled = program.compile_program(isa, design.design(isa))
    geometry = record("threshold_geometry_results.json")
    itinerary = record("interrupted_renewal_results.json")
    image = program.hash_text(json.dumps(compiled.image))
    assert image == geometry["changed_image_sha256"] == itinerary["actual_image_sha256"]
    bounds = program.bounds(isa, compiled)
    assert bounds == geometry["bounds"]
    check_helper(isa, compiled, bounds)
    print(json.dumps(check_bounds(compiled.constants, geometry, itinerary), indent=2))
    print("PASS conditional abort branch and budget checks; source recovery by H remains open")


if __name__ == "__main__":
    main()

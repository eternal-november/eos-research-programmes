"""A local phase-9 handoff pulse into the existing two physical trip circuits."""

from fractions import Fraction as Q

from handoff_contact import retiring_side

import a80_g3 as joined
import a80_return_seat as seat

src = joined.src
g = joined.g
need = joined.require


class HandoffTrip(joined.JoinedSeat):
    def _funded_sample(self, actual):
        # Two already located cam bands, two actual blend contacts, one native
        # local sample. No actor can call this through the instruction set.
        need(
            self.sampler.remaining == 0 and not self.held_plane and self.U >= seat.PRICE,
            "No funded predecessor edge",
        )
        old = retiring_side(self.carriage.normal, self.carriage.phase,
                            self.positions["cam"], self.positions["blend"],
                            self.p["SEGMENT"], self.p["BLEND_LIMIT"])
        result = super()._funded_sample(actual)
        if old is not None:
            self.trips[old].enabled = False
            # The other orientation's phase-1 predecessor is precisely all
            # eighty ACT zeros of this old bank, captured by this same paid edge.
            if not self.output[f"cam-stop:{13*(1-old)+1}"]:
                self.trips[old].armed = False
            self.output[f"trip{old}"] = 0
            return "planned-trip"
        return result


def handoff(p, up, old, *, budget=None, offset=None, blend=None, stage=9):
    new = 1 - old
    seg = p["SEGMENT"]
    cam = (13 * old + stage) * seg + (seg // 2 if offset is None else offset)
    h = joined.fixture(p, up, "NORMAL", 0, cam, keeper=new, upstream=budget, fixture_type=HandoffTrip)
    cap = Q(p["EMAX"])
    tc = Q(up["point"]["per_bank_transit_capacity"])
    h.E[:] = [(cap + p["EON"]) / 2] * 2
    h.T[:] = [tc] * 2
    for b in (old, new):
        h.positions[f"cut{b}"] = h.positions[f"shunt{b}"] = 0
        h.positions[f"act{b}:0"] = p["WARM_AT"]
        h.positions[f"carrier{b}"] = p["SEAT_LIMIT"]
        for j in range(80):
            h.positions[f"seat{b}:{j}"] = p["SEAT_LIMIT"]
    # This is the reached case with a genuine old and a genuine new grant.
    # Arbitrary raw acquisition of a trip line instead has its paid held-plane branch.
    h.positions["blend"] = new * p["BLEND_LIMIT"] if blend is None else Q(blend)
    h.sampler.remaining = 0
    h.refresh_surviving_levels()
    return h


def checks(p, up):
    for old in (0, 1):
        new = 1 - old
        h = handoff(p, up, old)
        h.trips[old].armed = True  # Challenge a pre-existing high-position arm.
        initial_U = h.U
        before = h.frame()
        need(h.endpoint_ports()["cpu_enabled"] == (True, True), "No overlap of actual endpoints")
        need(
            h.sampler.strobe() == "planned-trip" and h.U == initial_U - seat.PRICE, "Unpaid planned trip"
        )
        need(
            before == h.frame()
            and not h.endpoint_ports()["cpu_enabled"][old]
            and h.endpoint_ports()["cpu_enabled"][new],
            "Planned trip erased stores or dropped the successor",
        )
        # Neither high E, still-high ACT nor an attempted power edge at the
        # same high activation can legitimately produce a fresh grant.
        stale = h.trips[old]
        need(not stale.enabled and not stale.armed, "Old intact bank retained a fresh zero arm")
        need(not stale.transition(h.E[old], p["EOFF"], p["EON"], power=True)[0], "High old ACT replay")
        # Actual subsequent reset: retract every old activation, then later
        # power only a new cut/repowered seated body. Pending old work can veto this edge.
        h.positions[f"act{old}:0"] = 0
        need(all(h.positions[f"act{old}:{j}"] == 0 for j in range(80)), "Not actually all-zero")
        stale.transition(h.E[old], p["EOFF"], p["EON"], zero=True)
        h.positions[f"act{old}:17"] = p["POWER_AT"]
        need(
            not stale.transition(h.E[old], p["EOFF"], p["EON"], power=True, old_done=False)[0],
            "New grant ignored a retained native claim",
        )
        need(not stale.enabled and stale.armed, "Unfunded/blocked crossing invented a grant")
        # A later *new* physical upward crossing is necessary. Recharging
        # or accepting the previous failed event a second time is not allowed.
        h.positions[f"act{old}:17"] = 0
        stale.transition(h.E[old], p["EOFF"], p["EON"], zero=True)
        h.positions[f"act{old}:17"] = p["POWER_AT"]
        need(
            stale.transition(h.E[old], p["EOFF"], p["EON"], power=True, old_done=True)[0],
            "No real rearm",
        )

        for stage, offset, blend in (
            (8, p["SEGMENT"] // 2, new * p["BLEND_LIMIT"]),
            (9, p["SEGMENT"] // 4, new * p["BLEND_LIMIT"]),
            (9, p["SEGMENT"] // 2, Q(p["BLEND_LIMIT"], 2)),
        ):
            other = handoff(p, up, old, stage=stage, offset=offset, blend=blend)
            need(
                other.sampler.strobe() == "observed" and other.trips[old].enabled,
                "False old-bank retirement",
            )
        poor = handoff(p, up, old, budget=4095)
        need(poor.sampler.strobe() == "unfunded" and poor.trips[old].enabled, "Partial strobe tripped")
        prior = handoff(p, up, old)
        prior.submit("hold", f"trip{old}", 1)
        need(
            prior.sampler.strobe() == "held" and prior.endpoint_ports()["cpu_enabled"][old],
            "Held takeover was repaired by a paid-sampler label",
        )
        after = handoff(p, up, old)
        need(after.sampler.strobe() == "planned-trip", "Expected the other tie order")
        need(
            after.submit("hold", f"trip{old}", 1) == "held"
            and after.endpoint_ports()["cpu_enabled"][old],
            "Independently paid failure cannot bypass the local grant",
        )


def parent_case(p, up):
    old = 0
    h = handoff(p, up, old)
    native = src.old_module("program_model.py")
    compiled = native.Compiler(native.Design()).compile()
    cpu = native.Machine(compiled)
    cpu.C[0] = native.encode(native.STOREC, 3, 4)
    cpu.R[3] = 991
    cpu.R[4] = 7
    h.body_machines[old, 0] = cpu
    cells, capture = joined.layout(h)
    cell = cells[old]
    need(
        cell.source.fixture is h and h.endpoint_ports()["cpu_enabled"][old], "Wrong real budget or grant"
    )
    dt = Q(3, 4 * 2**26)
    need(
        cell.offer(h.now, ("native", old, 0), dt) and cpu.launch(funded=cell.active),
        "Old launch refused",
    )
    saved = cpu.pending_instruction
    # The receiver's owner-U-funded capture has a different terminal. Stopping
    # old CPU/driver launches does not close the independent receipt island.
    capture.records[old, 0] = 771
    capright = capture.launch(h.now, old, 0)
    need(capright is not None, "No preexisting raw capture")
    before_e = tuple(h.E)
    before_t = tuple(h.T)
    need(
        h.sampler.strobe() == "planned-trip"
        and cpu.pending_instruction is saved
        and tuple(h.E) == before_e
        and tuple(h.T) == before_t,
        "Quench erased the captured parent or bank stores",
    )
    h.advance(cells, capture, src.DELTA, **h.endpoint_ports())
    need(
        capture.finish(h.now, capright)
        and capture.snapshot == 771
        and not capture.finish(h.now, capright),
        "Lost or doubled the earlier receiver capture",
    )
    h.advance(cells, capture, src.DELTA, **h.endpoint_ports())
    need(capture.energy == 1024, "Unrelated U-fed receiver cell failed to refill")
    h.advance(
        cells,
        capture,
        dt - 2 * src.DELTA,
        native_returns={
            old: lambda _: need(
                cpu.complete(native.RawPorts(compiled)), "Retained STOREC did not complete"
            )
        },
        **h.endpoint_ports(),
    )
    need(
        cpu.C[7] == 991
        and not cell.active
        and cpu.pending_instruction is None
        and not h.endpoint_ports()["cpu_enabled"][old],
        "Early trip manufactured a clean C or a new grant",
    )


def main():
    p, _, up = g.parameters()
    checks(p, up)
    parent_case(p, up)
    band = Q(p["SEGMENT"], 4)
    need(0 < seat.DELTA < band and 2296 + 32 <= seat.PRICE, "Travel or common paid logic margin missing")
    need(34 * 2 - (6 * Q(22, 5) + Q(11, 10) + Q(1, 1000)) > 0, "No physical orientation margin")
    print(f"Planned old-bank trip on both orientations with a genuine zero old world weight.")
    print(
        f"Strict full-supply sample slack before the next contact {band-seat.DELTA}q; amended local work <=2328/4096."
    )
    print("Old native word 991 survives; partial work and held faults preserve their distinct outcomes.")


if __name__ == "__main__":
    main()

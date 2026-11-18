"""A80's live seated-word comparator, its frozen alternatives, and physical timing margins."""

from fractions import Fraction as Q
from itertools import combinations
import sys

import a80_return_seat as seat


OFFSETS = tuple(range(-20, 0)) + tuple(range(1, 21))
N = 6 * (12 * (6 + 2**98) + 2)


def need(test, message):
    if not test:
        raise AssertionError(message)


def neighbors(owner):
    return tuple((owner + offset) % N for offset in OFFSETS)


class Head:
    """Physical target rows for one code-head origin. No target program is consulted."""

    def __init__(self, provider, target, side, bay, body, hot_read):
        self.ordinal = neighbors(provider).index(target)
        self.binding = (self.ordinal, side, bay)
        self.body = body
        self.seated = True
        self.hot_read = hot_read

    def get(self, lookup, missing):
        target, side, bay, address = lookup
        if (target, side, bay) != self.binding or not self.seated:
            return missing
        if self.body.powered and not self.hot_read:
            return missing
        return self.body.C[address] if 0 <= address < len(self.body.C) else missing


def publish(isa, compiled, bounds, client, target, bank, body, hot, bay, address):
    origins = [o for o in neighbors(client) if o in neighbors(target)][:13]
    need(len(set(origins)) == 13 and target not in origins, "Invalid fixed code-observation roster")
    reader = neighbors(client).index(target)
    c = compiled.constants
    key = (c["BAYS"] + bay) * c["IMAGE_CELLS"] + address
    actual = {}
    for slot, provider in enumerate(origins):
        tx = isa.RawPorts(compiled)
        head = Head(provider, target, 1, bay, body, hot)
        tx.target_cells = head
        client_slot = 2 * neighbors(provider).index(client) + bank
        port = (client_slot, head.ordinal)
        tx.slot_inputs[port] = key
        machine = isa.Machine(compiled, poison=0)
        machine.W[c["QUERY_CURSOR"]] = client_slot * c["DEGREE"] + head.ordinal
        machine.enter("publish_queries")
        result = machine.run(
            tx, budget=bounds["instruction_upper_bounds"]["publish_queries"] + 8, until_yield=False
        )
        need(result == "halt", "Bounded physical slot visit did not return")
        pub = [row for row in tx.publications if row[1] == port]
        need(len(pub) == 1, "Physical reply directed to the wrong target or client")
        # Socket slots are fixed by the installation. Bank selection alternates
        # here to exercise an OR that cannot be reduced to a universal bank 0.
        actual[slot, slot % 2, reader] = pub[0][2]
    return key, actual


def visit_helper(isa, compiled, bounds, machine, ports, t):
    machine.enter("helper", (t,))
    need(
        machine.run(ports, budget=bounds["instruction_upper_bounds"]["helper"] + 32, until_yield=False)
        == "halt",
        "Actual helper exceeded its bound",
    )
    return next(e for e in reversed(ports.events) if e[0] == "command" and e[1] == t)


def scan_branch(isa, compiled, bounds, body, hot):
    client, target, bank = 0, 1, 1
    t = neighbors(client).index(target)
    c = compiled.constants
    base = c["TARGET_BASE"] + t * c["TARGET_WORDS"]
    i = isa.Machine(compiled, poison=0)
    ports = isa.RawPorts(compiled)
    ports.set_view(t, isa.populated_view(compiled, 0, 8))

    def state(**fields):
        for k, v in fields.items():
            i.W[base + c[k]] = v

    state(
        STAGE_ID=9,
        STAGE_WAIT=0,
        WATCH_HALF=1,
        LAST_PHASE=8,
        TIMER=1234567,
        RANK_VALID=1,
        HIGH=2**100,
        SELECTED=1,
        SCAN_MATCH=1,
        SCAN_BAY=0,
        SCAN_ADDRESS=c["IMAGE_CELLS"] - 1,
        PENDING=1,
    )
    addr = c["IMAGE_CELLS"] - 1
    key, records = publish(isa, compiled, bounds, client, target, bank, body, hot, 0, addr)
    # Six correlated origin slots may contribute false negatives in both banks.
    for (slot, srcbank, row), value in records.items():
        ports.replies[slot, srcbank, row] = value if slot >= 6 else isa.WORD_MASK
    state(CELL_KEY=key, CELL_WAIT=0)
    visit_helper(isa, compiled, bounds, i, ports, t)
    need(
        i.W[base + c["ACCEPTED"]] == int(hot),
        "Powered body's last comparison failed to reach its real bit",
    )
    # Other comparisons: bay 1 has passed; bay 79 has already mismatched.
    # The linear fold proof accounts for the intermediate physical visits.
    i.W[base + c["ACCEPTED"] + 1] = 1
    endkey = (2 * c["BAYS"] - 1) * c["IMAGE_CELLS"] + addr
    state(SCAN_BAY=79, SCAN_ADDRESS=addr, SCAN_MATCH=0, PENDING=1, CELL_KEY=endkey, CELL_WAIT=0)
    ev = visit_helper(isa, compiled, bounds, i, ports, t)
    need(
        i.W[base + c["SELECTED"]] == (1 if hot else 2)
        and i.W[base + c["ABORT"]] == int(not hot)
        and i.W[base + c["TIMER"]] == 1234567
        and ev[5] == (0 if hot else 20),
        "Unexpected repeated-scan abort or selection",
    )
    # Exercise the independent actual running-image monitor on the same live read route.
    p9 = isa.populated_view(compiled, 0, 9)
    p9[c["ACT_POWER_A"] + c["BAYS"]] = 1
    ports.set_view(t, p9)
    state(
        STAGE_ID=10,
        WATCH_HALF=1,
        LAST_PHASE=9,
        ABORT=0,
        VERIFY_ADDRESS=addr,
        PENDING=1,
        CELL_KEY=key,
        CELL_WAIT=0,
    )
    e9 = visit_helper(isa, compiled, bounds, i, ports, t)
    need(
        e9[5] == (0 if hot else 20) and i.W[base + c["ABORT"]] == int(not hot),
        "Powered running-cell verdict did not reach the literal MODE record",
    )
    return ev[5], e9[5]


def custody(isa, c):
    """One actual paid earlier writer with distinct producer, cell and fetch identities."""
    ports = seat.source.old_module("port_model.py")
    writer_host = neighbors(1)[0]
    writer_bank = 0
    bay = 2 * neighbors(1).index(writer_host) + writer_bank
    body = isa.Machine(c, poison=0)
    saved = body.C[0]
    body.powered = False
    body.C[0] ^= 64
    lead = Head(writer_host, 1, 1, bay, body, True)
    cell = (lead.ordinal, 1, bay, 0)
    need(lead.get(cell, isa.WORD_MASK) != saved, "Copy discriminator is already formed")
    funds = ports.Reservoir.filled(4096)
    op = ports.Slot(funds)
    op.recharge(ports.DELTA)
    # Material owner/address are captured at issue. Binding comes from the
    # installed writer endpoint. Its input has no foreign producer/bay field.
    need(op.offer(0, (body, 0, saved), Q(6)), "No paid copy")
    opened = True

    def apply(descriptor):
        target, address, value = descriptor
        if opened and not target.powered:
            target.C[address] = value

    op.elapse(6, apply)
    ports.conservation(funds, [op])
    need(lead.get(cell, isa.WORD_MASK) == saved and funds.spent == 4096, "Wrong leaf or unpaid write")
    opened = False
    body.powered = True
    need(
        lead.get(cell, isa.WORD_MASK) == saved
        and body.launch()
        and body.pending_instruction[1] == saved,
        "Passive reader, native fetch and remote writer do not share one current code word",
    )
    need(not op.elapse(7, apply), "Paid old write applied twice")
    return body


def margins(c, cert, g):
    f = Q(cert["frame_max"])
    fmin = Q(cert["frame_min"])
    q = Q(cert["query_period"])
    life = Q(cert["query_receipt_lifetime"])
    minimum = (c.constants["READ_WAIT_FRAMES"] - 1) * fmin
    # Worst path: two q for the request lead, a full sweep after stable arrival,
    # one full frame as an additional post-capture processing allowance, then two for DATA.
    establish = 2 + q + f + 2
    repeat = q + f + 2
    need(
        establish < minimum and repeat < (life - 1) * Q(100, 101),
        "One functioning provider has no guaranteed live reply at this actual read",
    )
    v = Q(11, 10)
    pp = dict(g["design"]["physical_parameters"])
    hold = (pp["WARM_AT"] - pp["POWER_AT"]) / v
    scan = Q(cert["complete_scan"])
    need(
        hold > 2 * scan + Q(cert["query_age"]), "No full repeat scan is forced by this geometric witness"
    )
    pressure = 6 * Q(22, 5) + Q(11, 10) + Q(1, 1000)
    need(
        pressure < 28 and 34 * 2 - pressure > 29 + 2, "Host effort proof lost strict stiction or service"
    )
    return minimum - establish, (life - 1) * Q(100, 101) - repeat, hold - 2 * scan - Q(cert["query_age"])


def main():
    isa, c, bounds, cert, _, geom, _, _ = seat.compile_images()
    need(
        isa.definite_assignment(c)["every_nominal_local_read_assigned"]
        and all(node[0] != isa.STOREC for node in c.nodes),
        "A80 formation or native C-writer exclusion changed",
    )
    need(
        all(isa.encode(*isa.decode(word)) == word for word in c.image),
        "A80 actual writable image encoding changed",
    )
    body = custody(isa, c)
    need(scan_branch(isa, c, bounds, body, True) == (0, 0), "Mounted live head failed")
    need(scan_branch(isa, c, bounds, body, False) == (20, 20), "Cold-only source did not discriminate")
    wait, lifetime, rescan = margins(c, cert, geom)
    need(
        all(len(set(range(13)) - set(bad)) >= 7 for bad in combinations(range(13), 6)),
        "Failed to maintain seven independent good origins",
    )
    print(
        "Mounted and cold-only heads yield MODE (0,0) and (20,20) in the A80 repeated scan and running monitor."
    )
    print(
        f"Strict held-key start margin {wait}q, repeated-receipt margin {lifetime}q, post-power repeated scan margin {rescan}q."
    )


if __name__ == "__main__":
    if not __debug__ or sys.version_info[:2] != (3, 12):
        raise SystemExit("Use unoptimized Python 3.12")
    main()

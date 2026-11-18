"""Replay the limiting 512-cell paced RX tail against its ordered FIFO prefix projection."""
from collections import deque
from fractions import Fraction as Q
import sys

import input_lifecycle as raw
import native_clock_source as native


def check_rx_prefixes():
    isa, image, _ = native.retirement.source_inputs()
    suffix = Q(raw.RX_WORK, raw.RX_POWER)
    last_capture = Q(512, 2048)
    last_parser = last_capture + suffix
    service_end = last_parser + 2 * raw.RECORD_DELAY
    initial = {}
    clock_specs = {}

    def full_lane(source, payer):
        lane = raw.RawLane(source.population, raw.LaneId(2, 0, 0, 0), payer)
        record = next(r for r in lane.ordered if r.lifetime == 8)
        symbol = raw.symbols(record.source_key, 19)[0]
        words = [symbol] * 508 + list(raw.symbols(record.source_key, 731))
        # A supplied coherent initial FIFO. These 512 initial words are not a
        # burst of new source emissions on an initially empty physical lead.
        for word in words:
            assert lane.queue.offer(word) == "accepted"
        initial.update(record=record, words=words)
        clock_specs[record.key] = (Q(5001, 5000), last_parser)
        return lane

    clock, cpu, source, _ = native.native_fixture(isa, image, receive=full_lane, receipt_clock_specs=clock_specs)
    lane = clock.lanes[0]
    record = initial["record"]
    key = record.key
    assert source.rx_phase == 0
    clock.cut()
    operating_start = cpu.bank.stock
    upstream_start = lane.payer.stock
    reference = deque(enumerate(initial["words"], start=1))
    captured = None
    captures = 0
    prefixes = 0
    while clock.now < service_end:
        clock.advance_to(min(clock.next_boundary(), service_end))
        while clock.due():
            events = clock.due()
            # A true countdown root tied with the last parser commit wins here.
            event = ("tick", key) if ("tick", key) in events else events[0]
            if event == "RX" and source.rx_phase == 1 and reference:
                assert captured is None
                captured = reference[0]
                captures += 1
                assert clock.now == Q(captures, 2048)
            if event == "rx-commit" and captured is not None:
                assert clock.now == Q(captured[0], 2048) + suffix
                idx = lane.queue.number(0, 9)
                assert lane.queue.values[idx] == captured[1]
                assert reference.popleft() == captured
                captured = None
            clock.edge(event)
            assert lane.queue.number(9, 10) == len(reference)
            assert bool(lane.rx[608]) == (captured is not None)
            if captured is not None:
                assert lane.queue.number(609, 9) == (captured[0]-1) % 512
            if clock.now < service_end:
                assert record.ttl == 0 and record.readable() == raw.MASK
            prefixes += 1
    assert captures == 512 and not reference and record.readable() == 731
    assert upstream_start - lane.payer.stock == 512*(32+32+64) + 11584 + 2048 + raw.TICK_WORK
    assert cpu.steps == 0 and cpu.bank.stock == operating_start
    assert last_parser == Q(32769, 131072) and service_end == Q(32785, 131072)
    assert Q(513, 2048) - service_end == Q(47, 131072)
    clock.end_check()
    return prefixes, last_parser, service_end


if __name__ == "__main__":
    if sys.version_info[:2] != (3, 12) or not __debug__:
        raise SystemExit("Use unoptimized Python 3.12")
    n, parsed, committed = check_rx_prefixes()
    print(f"{n} ordered clock-event prefixes matched, last pop at {parsed}, record commit at {committed}")

#!/usr/bin/env python3
"""Deterministic finite replay for substitution at a maintenance-lane deadline."""
import argparse
import itertools as it
import json
from pathlib import Path

CUT, JOINT_FINISH, SOLO_FINISH = 2, 4, 5

def powerset_of_size(seq, size):
    return tuple(frozenset(q) for q in it.combinations(seq, size))

def setup(n, chosen):
    occupied, events = {}, []
    for ix, lane in enumerate(chosen):
        assert 0 <= lane < n and lane not in occupied
        ident = f"old{ix}"
        occupied[lane] = ident
        events.append([0, 'old-accept-and-reserve', ident, lane, SOLO_FINISH])
    events.append([1, 'replace-instrument', 'old-authority-ends', 'old-work-survives'])
    return occupied, events

def incumbent(read):
    """Fixed receiver: unwrap a timely window guarantee, or do not dispatch."""
    if read is None:
        return None
    lo, hi, lane = read
    return lane if lo <= CUT and JOINT_FINISH <= hi else None

def original(n, r, active):
    readings = tuple(j not in active for j in range(n))
    return max(j for j, v in enumerate(readings) if v), len(readings), CUT

def changed(n, r, active):
    # Different instrument: parallel bank, no other cell readable.
    readings = tuple(j not in active for j in range(r + 1))
    return next(j for j, v in enumerate(readings) if v), len(readings), CUT

def late(n, r, active):
    tag, reads, _ = changed(n, r, active)
    return tag, reads, CUT + 1

def run(n, r, lanes, sensor, forced=None, stand_alone=False):
    active, events = setup(n, lanes)
    tag, reads, arrival = sensor(n, r, active.copy())
    cert = (CUT, SOLO_FINISH, tag)
    launch = arrival if stand_alone else CUT
    # At the joint cut a later message cannot appear in the receiver input.
    decision = (tag if stand_alone else incumbent(cert if arrival <= CUT else None))
    if forced is not None:
        decision = forced
    if arrival <= launch:
        events.append([arrival, 'report', *cert])
    service = False
    safety = True
    if decision is not None:
        # The independent resource denies conflict at admission. This denial
        # is not usable as a second try at the same irrevocable cut.
        if decision in active:
            events.append([launch, 'refused-old-reservation', decision])
        elif 0 <= decision < n:
            safety = all(decision not in active for _ in range(launch, launch + 2))
            service = (launch + 2 <= (SOLO_FINISH if stand_alone else JOINT_FINISH)) and safety
            events.append([launch, 'dispatch', decision])
            events.append([launch + 2, 'complete-new-service', decision])
        else:
            raise AssertionError('invalid lane')
    else:
        events.append([launch, 'no-timely-certificate'])
    if arrival > launch:
        events.append([arrival, 'report', *cert])
    for lane, ident in active.items():
        events.append([SOLO_FINISH, 'old-complete-and-release', ident, lane])
    events.sort(key=lambda e: e[0])
    return {'report': cert, 'arrival': arrival, 'events': events,
            'reads': reads, 'service': service, 'safety': safety,
            'old_completed': sum(e[1] == 'old-complete-and-release' for e in events)}

def physical_oracle(n, trace, due):
    """Replay resource occupancy from raw events, without sensor or decoder."""
    reserved, inflight = {}, {}
    returned, completed = 0, []
    for tick, event, *body in trace:
        if event == 'old-accept-and-reserve':
            ident, lane, end = body
            assert tick == 0 and 0 <= lane < n and lane not in reserved
            reserved[lane] = (ident, end)
        elif event == 'old-complete-and-release':
            ident, lane = body
            assert reserved.pop(lane) == (ident, tick)
            returned += 1
        elif event == 'dispatch':
            lane, = body
            assert 0 <= lane < n and lane not in reserved and lane not in inflight
            inflight[lane] = tick + 2
        elif event == 'complete-new-service':
            lane, = body
            assert inflight.pop(lane) == tick
            completed.append(tick)
        assert set(inflight).isdisjoint(reserved)
    assert not reserved and not inflight
    return returned, len(completed) == 1 and completed[0] <= due


def decision_possible(n, r, early_count, bundle=1):
    """Independent direct search over decoded action menus, no theorem use."""
    blocked = powerset_of_size(range(n), r)
    actions = powerset_of_size(range(n), bundle)
    # Bound this exact direct search to small replay envelopes only.
    for menu in it.combinations(actions, early_count):
        if all(any(not (a & b) for a in menu) for b in blocked):
            return True
    return False

def check_all():
    reach = suite = adaptations = trace_checks = 0
    example = None
    for n in range(2, 9):
        for r in range(1, n):
            seen = set()
            for B in it.combinations(range(n), r):
                a, b, c = (run(n, r, B, instrument) for instrument in (original, changed, late))
                solo = [run(n, r, B, s, stand_alone=True) for s in (original, changed, late)]
                # Physical audit independent of incumbent decoder.
                for ix, z in enumerate([a, b, c] + solo):
                    due = JOINT_FINISH if ix < 3 else SOLO_FINISH
                    assert physical_oracle(n, z['events'], due) == (r, z['service'])
                    assert z['old_completed'] == r and z['safety']
                    assert tuple(e[3] for e in z['events'] if e[1] == 'old-accept-and-reserve') == B
                    for e in z['events']:
                        if e[1] == 'dispatch':
                            assert e[2] not in B
                    trace_checks += 1
                assert a['service'] and b['service'] and not c['service']
                assert all(z['service'] for z in solo)
                assert b['report'] == c['report'] and b['arrival'] == CUT < c['arrival']
                assert a['reads'] == n and b['reads'] == r + 1
                # This offline forced move works on this trace: it is not an
                # implementable function of the shared empty decision view.
                assert run(n, r, B, late, forced=b['report'][-1])['service']
                seen.add(b['report'][-1])
                adaptations += a['report'][-1] != b['report'][-1]
                if (n, r, B) == (4, 1, (0,)):
                    example = [a, b, c, solo[-1]]
                reach += 1
            assert len(seen) == r + 1
            suite += 1
    menus = []
    for n in range(2, 8):
        for r in range(1, n):
            assert not decision_possible(n, r, r)
            assert decision_possible(n, r, r + 1)
            menus.append([n, r, r + 1])
    bundles = []
    for n, r, b, k in [(5, 1, 2, 2), (6, 2, 2, 3), (5, 3, 2, 10), (5, 2, 2, 4)]:
        assert not decision_possible(n, r, k - 1, bundle=b)
        assert decision_possible(n, r, k, bundle=b)
        bundles.append([n, r, b, k])
    # Every proper subset of the n blocked-singleton histories has a common
    # lane, but the whole family fails. Enumerate all subfamilies.
    hyper = []
    for n in range(2, 11):
        full = (1 << n) - 1
        for blocked_union in range(full + 1):
            assert bool(full & ~blocked_union) == (blocked_union != full)
        hyper.append([n, full + 1])
    return {'parameter_suites': suite, 'reachable_joint_cuts': reach,
            'separate_physical_trace_checks': trace_checks,
            'positive_action_changes': adaptations,
            'direct_single_lane_menus': menus,
            'direct_bundle_menus_n_r_b_k': bundles,
            'proper_subfamily_tests_n_count': hyper,
            'example_order_original_changed_late_late_standalone': example}

if __name__ == '__main__':
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument('--verify', action='store_true')
    opts = cli.parse_args()
    out = json.dumps(check_all(), indent=2, sort_keys=True) + '\n'
    if opts.verify:
        assert out == Path(__file__).with_name('results.json').read_text()
    print(out, end='')

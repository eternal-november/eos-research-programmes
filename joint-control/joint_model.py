"""Finite local machine and same-run source checks; see REALIZATION.md.

Only LocalMachine.step implements the prescribed target decision program.
It receives a bounded mailbox, never x, fault labels, or a repair-success flag.
Absolute simulation time, effect provenance and exposure sets are audit ghosts.
"""
from __future__ import annotations

import argparse
from collections import defaultdict
from dataclasses import dataclass
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path

from information_model import fixed_packet, parse_packet, median_group

N, ROWS, GROUP, BLOCK_BYTES = 13, 42, 21, 1024
GRID, PERIOD, SPACING, EXTENDED, HORIZON = 1_000_000, 455, 35, 34, 489
GAIN, DELTA, RADIUS, ETA = F(8, 5), F(1, 1000), F(4, 5), F(3, 50)
OP_ADMIT, OP_QUERY, OP_MEDIAN, OP_COMMAND, OP_CLOCK = 1, 2, 3, 4, 5
OP_NEGATIVE, OP_ROGUE_REQUEST = 6, 7
PROGRAM = bytes((OP_ADMIT, OP_QUERY, OP_MEDIAN, OP_COMMAND, OP_CLOCK, 0))
BAD_PROGRAM = bytes((OP_NEGATIVE, OP_ROGUE_REQUEST, OP_CLOCK, 0))


def nearest(q):
    """Nearest integer, ties away from zero, including adversarial negatives."""
    return (q.numerator * 2 + q.denominator) // (2*q.denominator) if q >= 0 else -nearest(-q)


def put16(block, offset, value):
    block[offset:offset+2] = int(value & 65535).to_bytes(2, 'little')


def get16(block, offset):
    return int.from_bytes(block[offset:offset+2], 'little')


def signed16(block, offset):
    value = get16(block, offset)
    return value - 65536 if value >= 32768 else value


def image(target, initial=False):
    """Eight physically bounded blocks; no true state or unknown model data."""
    blocks = [bytearray(BLOCK_BYTES) for _ in range(8)]
    blocks[0][:len(PROGRAM)] = PROGRAM
    blocks[2][:6] = bytes((target, ROWS, GROUP, 8, 5, 10))
    blocks[4][0] = 12                   # commissioning and boot both drain
    blocks[4][1] = 0                    # round age modulo10
    blocks[4][2] = 0                    # epoch bit
    blocks[4][3] = 0                    # a round is pending
    blocks[4][4] = 0                    # no published estimate at boot
    return blocks


@dataclass(frozen=True)
class Command:
    value: tuple[int, int]              # milliunits, physical bound[-2000,2000]
    estimate: tuple[int, int] | None    # ghost provenance; not policy input
    certified_dispatch: bool           # ghost provenance; not policy input
    issued: int = 0                     # simulator time only


class LocalMachine:
    def __init__(self, target, initial=True):
        self.mem = image(target, initial)
        self.halted = False
        self.write_seen = set()         # audit only
        self.contaminated = False       # audit only
        self.last_estimate = None       # audit only

    def poison(self, target):
        # Actual persistent hostile instruction image and malformed mutable data.
        self.mem[0][:] = bytes(BLOCK_BYTES)
        self.mem[0][:len(BAD_PROGRAM)] = BAD_PROGRAM
        self.mem[3][:] = bytes([255])*BLOCK_BYTES
        self.mem[4][0] = 0
        self.mem[7][:8] = bytes([255])*8
        self.contaminated = True

    def halt(self):
        self.halted = True
        self.write_seen = set()

    def write(self, address, value):
        # Nominal primitive suppresses resident writes while halted.
        if self.halted and 0 <= address < 8 and len(value) == BLOCK_BYTES:
            self.mem[address][:] = value
            self.write_seen.add(address)

    def boot(self, target):
        # The audit observes actual image equality. Dispatch does not consume it.
        actual_image = self.mem == image(target)
        self.halted = False
        if actual_image:
            self.contaminated = False
        return actual_image

    def step(self, mailbox):
        """Total bounded opcode interpreter. State is entirely the eight blocks.

        A malformed configuration produces no request/command, a safe *syntax*
        fallback only; source safety counts this path as impaired. HALT holds.
        Any code image executes at most16 instructions per invocation.
        """
        if self.halted:
            return [], None, 0, 0, None
        m = self.mem
        requests, outgoing, admissions, ops, published = [], None, 0, 0, None
        config = tuple(m[2][:6])
        if not (config[0] < N and config[1:] == (42, 21, 8, 5, 10)):
            return [], None, 6, 0, None
        target = config[0]
        draining = m[4][0] > 0
        age, epoch = m[4][1] % 10, m[4][2] & 1
        # Every arrival is bounded by the physical ingress. No dynamic allocation.
        mailbox = mailbox[:16]
        for pc in range(16):
            m[1][0] = pc
            opcode = m[0][pc]
            ops += 1
            if opcode == 0:
                break
            # Corrupt code may repeat expensive instructions. A local hardware
            # instruction budget gives a total timeout/hold outcome, never an
            # assertion deleting the run. The48 reserve pays queue extraction.
            bound = {OP_ADMIT:2368,OP_QUERY:126,OP_MEDIAN:1008,
                     OP_COMMAND:24,OP_CLOCK:140,OP_NEGATIVE:2,
                     OP_ROGUE_REQUEST:84}.get(opcode,1)
            if ops+bound+48 > 10000:
                break
            if opcode == OP_ADMIT:
                for origin, word in mailbox:
                    # Explicit fixed-width scan:128 executed elementary steps.
                    checksum = 0
                    for bit in range(64):
                        checksum ^= (word >> bit) & 1
                        ops += 2
                    ops += 16
                    value = parse_packet(word, origin, epoch, ROWS)
                    if not draining and m[4][3] and 1 <= age <= 5 and value is not None:
                        off = origin*3
                        if m[3][off] == 0:
                            m[3][off] = 1
                            put16(m[3], off+1, value)
                            admissions += 1
                            ops += 4
            elif opcode == OP_QUERY:
                if not draining and age == 0:
                    m[3][:ROWS*3] = bytes(ROWS*3)
                    m[4][3] = 1
                    for row in range(ROWS):
                        #16-bit request:6-bit row,1-bit epoch, upper bits zero.
                        word = row | (epoch << 6)
                        put16(m[5], row*2, word)
                        requests.append(word)
                        ops += 3
                    m[5][84] = ROWS
            elif opcode == OP_MEDIAN:
                if not draining and age == 8 and m[4][3]:
                    estimate = []
                    for coordinate in range(2):
                        values = []
                        for row in range(coordinate*GROUP, (coordinate+1)*GROUP):
                            off = row*3
                            values.append(signed16(m[3], off+1) if m[3][off] == 1 else None)
                            ops += 2
                        med, comparisons, shifts = median_group(values, sentinel=0)
                        ops += comparisons + shifts + 2*GROUP
                        # Packet parser bounds values; sentinel is also in range.
                        estimate.append(int(med))
                    for j, value in enumerate(estimate):
                        put16(m[7], j*2, value)
                    m[4][4] = 1
                    published = tuple(estimate)
            elif opcode == OP_COMMAND:
                if not draining and m[4][4] == 1:
                    estimate = tuple(signed16(m[7], j*2) for j in range(2))
                    value = tuple(max(-2000, min(2000, nearest(F(8*v, 5)))) for v in estimate)
                    outgoing = Command(value, estimate, True)
                    for j, v in enumerate(value):
                        put16(m[6], j*2, v)
                    m[6][4] = 1
                    ops += 24
            elif opcode == OP_NEGATIVE:
                outgoing = Command((-2000, -2000), None, False)
                put16(m[6],0,-2000)
                put16(m[6],2,-2000)
                m[6][4] = 1
                ops += 2
            elif opcode == OP_ROGUE_REQUEST:
                if not draining:
                    for row in range(ROWS):
                        put16(m[5],row*2,row | (epoch << 6))
                    m[5][84] = ROWS
                    ops += 2*ROWS
            elif opcode == OP_CLOCK:
                if draining:
                    m[4][0] = max(0, m[4][0]-1)
                    m[4][3] = m[4][4] = m[5][84] = m[6][4] = 0
                    ops += 4
                    if m[4][0] == 0:
                        m[3][:ROWS*3] = bytes(ROWS*3)
                        ops += ROWS*3
                else:
                    m[4][1] = (age+1) % 10
                    if age == 9:
                        m[4][2] = epoch ^ 1
                put16(m[7], 8, (get16(m[7], 8)+1) % PERIOD)
                ops += 8
            else:
                # Unknown opcodes are inert bounded instructions, not Python code.
                ops += 1
        # Physical local queues are the addressed image fields, not ghost lists.
        requests = [get16(m[5],2*r) for r in range(min(ROWS,m[5][84]))]
        m[5][84] = 0
        if m[6][4] == 1:
            actual_value = tuple(max(-2000,min(2000,signed16(m[6],2*j))) for j in range(2))
            outgoing = Command(actual_value, outgoing.estimate if outgoing else None,
                               outgoing.certified_dispatch if outgoing else False)
            m[6][4] = 0
        else:
            outgoing = None
        ops += len(requests)+6
        assert ops <= 10000  # concrete bounded word-operation machine capacity
        return requests, outgoing, ops, admissions, published


class Provider:
    """One raw-row apparatus; request-origin quota is physical-endpoint indexed."""
    def __init__(self, row):
        self.row = row
        self.cooldown = bytearray(N)
        self.live_epoch = bytearray(N)

    def tick(self):
        for i in range(N):
            self.cooldown[i] = max(0, self.cooldown[i]-1)
            if self.cooldown[i] == 0:
                self.live_epoch[i] = 0

    def admit(self, origin, word):
        # The origin is a physical requester endpoint, not a report credential.
        if not (0 <= origin < N and 0 <= word < (1 << 16)) or word >> 7:
            return False
        row, epoch = word & 63, (word >> 6) & 1
        if row != self.row or self.cooldown[origin]:
            return False
        self.cooldown[origin] = 9
        self.live_epoch[origin] = epoch
        return True


def within_interval_envelope(costs, rate=F(1153), burst=F(6500)):
    # All intervals in O(T):prefix(t)-rate*t minus its running minimum.
    prefix, least, worst = F(0), F(0), F(0)
    for c in costs:
        prefix += c-rate
        worst = max(worst, prefix-least)
        least = min(least, prefix)
    return worst <= burst, worst


def simulate(name, ticks=5000, repair=True, source_only=False, metadata=False,
             full_power=False, weighted=False, dependency_mode=False, x0=(500000, -500000),
             a=F(11,200), c=F(9,200)):
    actors = [LocalMachine(i) for i in range(N)]
    providers = [Provider(row) for row in range(ROWS)]
    # Legitimate initial residual state is nonempty, but cannot be consumed as
    # fresh. Commissioning begins the same actual drain as later reconstruction.
    for actor in actors:
        actor.mem[4][4] = 1
        for row in range(ROWS):
            actor.mem[3][row*3] = 1
            put16(actor.mem[3],row*3+1,1000)
        put16(actor.mem[7],0,1000)
        put16(actor.mem[7],2,1000)
    for provider in providers:
        provider.cooldown[:] = bytes([9])*N
    actors[0].poison(0)
    actors[12].poison(12)
    exposure, known_keys, persistent = {0, 12}, {0, 12}, {12}
    hardware_exposed = {0}  # tool12 leaks a report key; it cannot drive raw sensors
    # Audit labels and causal events belong to the source, never to Local.step.
    active, dirty_since = {}, {0:0, 12:0}
    acquired_targets = []
    acquire_at = {100+490*k: ((13+k) if source_only else (k+1)) for k in range(8)}
    requests_due, samples_due, replies_due, effects_due = defaultdict(list), defaultdict(list), defaultdict(list), defaultdict(list)
    # Already accepted nominal jobs complete raw sampling at tick0. Duplicate
    # old requests also arrive, exercise live cooldown, and are rejected.
    samples_due[0] = [(origin,row,0) for origin in range(N) for row in range(ROWS)]
    requests_due[0] = [(origin,row) for origin in range(N) for row in range(ROWS)]
    output = [Command((0,0), None, False) for _ in range(N)]
    output[0] = output[12] = Command((-2000,-2000), None, False)
    # Initial world commands survive writes. All expire within L_init=4.
    for lag in range(4):
        for target in range(12):
            baseline = (-2000,-2000) if target == 0 else (0,0)
            effects_due[lag].append((target, Command(baseline, None, False, -1)))
    tool_clock = [0]*N
    maintenance_until = [0]*N
    x, energy = tuple(x0), F(6500)
    weights = ([F(101,1300)]*6+[F(99,1300)]*6+[F(100,1300)]) if weighted else [F(1,13)]*N
    costs, information_costs = [], []
    max_state, min_service, min_energy = F(0), F(100), energy
    max_effect_error, max_observed_bad = F(0), 0
    max_ingress, max_egress, max_ops, max_samples, max_side_operations = 0,0,0,0,0
    counters = defaultdict(int)
    functional_returns, release_persistence, inequality_views = [], [], False
    correct_disagreement = None
    last_view = [None]*N
    violation = None
    trace_digest = hashlib.sha256()
    # Every timing bound is implemented with queues; absolute indices are the
    # simulator representation of bounded delays, absent from target policies.
    for tick in range(ticks):
        acquisition_ops = 0
        if tick in acquire_at:
            domain = acquire_at[tick]
            exposure.add(domain)
            known_keys.add(domain)
            hardware_exposed.add(domain)
            acquisition_ops = 1
            counters['acquisitions'] += 1
            if domain < N:
                if dependency_mode:
                    actors[domain].mem[2][1] = 255  # common parser/config rejects whole bundle
                    actors[domain].contaminated = True
                    counters['dependency_config_acquisitions'] += 1
                else:
                    actors[domain].poison(domain)
                active[domain] = tick+6
                dirty_since[domain] = tick
                acquired_targets.append(domain)
        for target in list(active):
            if tick == active[target]:
                del active[target]
                assert actors[target].contaminated and target in known_keys
                release_persistence.append(target)
        assert len(active) <= 1 and len(exposure) <= 10
        for provider in providers:
            provider.tick()
        row_sample, row_egress, row_cpu = [0]*ROWS, [0]*ROWS, [26]*ROWS
        endpoint_bits, endpoint_cpu = [0]*N, [0]*N
        operation_count, maintenance_cost = acquisition_ops, F(0)
        # Bad tool12 has target-only reach. It issues actual recurrent code writes.
        actors[12].mem[0][:] = bytes(BLOCK_BYTES)
        actors[12].mem[0][:len(BAD_PROGRAM)] = BAD_PROGRAM
        actors[12].contaminated = True
        maintenance_cost += 2
        operation_count += 1
        counters['bad_tool_writes'] += 1
        for i in range(N):
            phase = (tool_clock[i]-i*SPACING) % PERIOD
            if repair and i != 12:
                if phase == 0:
                    actors[i].halt()
                    maintenance_until[i] = tick+EXTENDED
                    maintenance_cost += 2
                    operation_count += 1
                    counters['halts'] += 1
                elif 1 <= phase <= 8:
                    actors[i].write(phase-1, image(i)[phase-1])
                    maintenance_cost += 2
                    operation_count += 1
                    counters['image_block_writes'] += 1
                elif phase == 9:
                    complete = actors[i].boot(i)
                    counters['boots'] += 1
                    maintenance_cost += 2
                    operation_count += 1
                    if complete and i in dirty_since and i not in active:
                        # This is memory completion; functional return is below.
                        counters['actual_image_reconstructions'] += 1
            tool_clock[i] = (tool_clock[i]+1) % PERIOD
        assert maintenance_cost <= 4
        mail = [[] for _ in range(N)]
        for recipient, row, word in replies_due.pop(tick, []):
            if len(mail[recipient]) < 16:
                mail[recipient].append((row, word))
            else:
                counters['physical_ingress_drops'] += 1
        max_ingress = max(max_ingress, *(len(box)*64 for box in mail))
        for i, actor in enumerate(actors):
            req, cmd, ops, admitted, published = actor.step(mail[i])
            if dependency_mode and i in dirty_since and i not in (0,12) and actor.mem[2][1] == 255:
                assert not req and cmd is None and published is None
                counters['whole_bundle_dependency_suppressed_ticks'] += 1
            endpoint_cpu[i] += ops
            counters['actual_target_word_operations'] += ops
            counters['admitted_packets'] += admitted
            if published is not None:
                counters['median_publications'] += 1
                last_view[i] = published
                if not actor.contaminated:
                    error = max(abs(F(published[j],1000)-F(x[j],GRID)) for j in range(2))
                    assert error < F(223,5000), (name,tick,i,'publish',error)
                available = [v for v in last_view if v is not None]
                inequality_views |= len(set(available)) > 1
            for word in req:
                requests_due[tick+1].append((i,word))
            endpoint_bits[i] += 16*len(req)
            counters['request_words16'] += len(req)
            if cmd is not None:
                cmd = Command(cmd.value, cmd.estimate, cmd.certified_dispatch, tick)
                effects_due[tick+4].append((i,cmd))
                counters['issued_commands'] += 1
        # Raw acquisition occurs only in response to an actual admitted request.
        for origin, word in requests_due.pop(tick, []):
            row = word & 63
            if row >= ROWS:
                continue
            provider = providers[row]
            row_cpu[row] += 12
            if not provider.admit(origin, word):
                counters['quota_or_header_rejections'] += 1
                continue
            counters['accepted_row_jobs'] += 1
            samples_due[tick+1].append((origin,row,(word>>6)&1))
        sampled = {}
        for origin,row,epoch in samples_due.pop(tick, []):
            if row not in sampled:
                coordinate = row//GROUP
                sample = nearest(F(x[coordinate],1000))+((row+tick)%3)-1
                sampled[row] = max(-4000,min(4000,sample))
                row_sample[row] += 1
                operation_count += 1
                counters['raw_samples'] += 1
            domain = row%GROUP
            raw = sampled[row]
            if domain in exposure:
                if metadata and (row+origin+tick)%4 == 0:
                    reply = 1 << 40             # malformed fixed word
                    counters['malformed_forgeries'] += 1
                elif metadata and (row+origin+tick)%4 == 1:
                    reply = fixed_packet(row, epoch^1, 1000)
                    counters['old_epoch_forgeries'] += 1
                else:
                    reply = fixed_packet(row,epoch,-4000 if origin%2 else 4000)
                    counters['credential_forged_replies'] += 1
            else:
                reply = fixed_packet(row,epoch,raw)
            # Three fixed destination lanes:14 rows at offsets+3,+4,+5.
            replies_due[tick+1+row//14].append((origin,row,reply))
            row_egress[row] += 64
            row_cpu[row] += 12
            counters['reply_words64'] += 1
        assert max(row_sample) <= 1 and max(row_egress) <= 1024
        assert max(endpoint_bits) <= 1024
        # Actual nominal energy is counted once. Admission executes CPU work;
        # its <=1/job accounting allowance is not a second physical energy sink.
        info_cost = sum(F(2*s)+F(b,64)+F(o,10000) for s,b,o in zip(row_sample,row_egress,row_cpu))
        info_cost += sum(F(b,64)+F(o,10000) for b,o in zip(endpoint_bits,endpoint_cpu))
        nominal_info_cost = info_cost
        if full_power:
            # Actual rogue hardware fills remaining individual capacities. No
            # intact software quota is assumed to restrict that hardware.
            for domain in hardware_exposed:
                for row in (domain, GROUP+domain):
                    extra_samples = 2-row_sample[row]
                    info_cost += 5*extra_samples+F(1024-row_egress[row],64)+F(10000-row_cpu[row],10000)
                    operation_count += extra_samples
                    counters['rogue_extra_samples'] += extra_samples
                    row_sample[row], row_egress[row], row_cpu[row] = 2,1024,10000
                if domain in active and not dependency_mode:
                    info_cost += F(1024-endpoint_bits[domain],64)+F(20000-endpoint_cpu[domain],10000)
                    endpoint_bits[domain], endpoint_cpu[domain] = 1024,20000
            assert info_cost-nominal_info_cost <= 72*len(exposure)
        max_egress = max(max_egress,*row_egress,*endpoint_bits)
        max_ops = max(max_ops,*endpoint_cpu)
        max_samples = max(max_samples,*row_sample)
        for target,command in effects_due.pop(tick, []):
            output[target] = command
            if actors[target].halted and not command.certified_dispatch:
                counters['old_hostile_world_commands_applied_during_halt'] += 1
        for target in active:
            if not dependency_mode:
                output[target] = Command((-2000,-2000),None,False,tick)
        current_bad = set(persistent) | set(active)
        for i,actor in enumerate(actors):
            if actor.contaminated or tick < maintenance_until[i]:
                current_bad.add(i)
            # Pending old effects are included until the complete operation span.
            if tick >= 24 and i not in current_bad:
                cmd = output[i]
                assert cmd.certified_dispatch and cmd.estimate is not None, (name,tick,i,'no feedback')
                effect_error = max(abs(F(cmd.value[j],1000)/GAIN-F(x[j],GRID)) for j in range(2))
                assert effect_error <= ETA, (name,tick,i,'effect error',effect_error)
                max_effect_error = max(max_effect_error,effect_error)
                if i in dirty_since:
                    functional_returns.append({'target':i,'acquired':dirty_since[i], 'returned':tick, 'elapsed':tick-dirty_since[i]})
                    del dirty_since[i]
        max_observed_bad = max(max_observed_bad,len(current_bad))
        if tick >= 24 and correct_disagreement is None:
            correct = [i for i in range(N) if i not in current_bad and output[i].estimate is not None]
            for left in correct:
                for right in correct:
                    if output[left].estimate != output[right].estimate and output[left].value != output[right].value:
                        correct_disagreement = {'tick':tick,'recipients':[left,right],
                            'effect_estimates_milliunits':[list(output[left].estimate),list(output[right].estimate)],
                            'actual_effects_milliunits':[list(output[left].value),list(output[right].value)]}
                        break
                if correct_disagreement is not None:
                    break
        if repair:
            assert len(current_bad) <= 4
        actual_u = [tuple(F(v,1000) for v in command.value) for command in output]
        assert all(-2 <= u <= 2 for pair in actual_u for u in pair)
        Y = tuple(sum(weights[i]*(2+actual_u[i][j]) for i in range(N)) for j in range(2))
        actuation_cost = sum(2+v for pair in actual_u for v in pair)
        assert 0 <= actuation_cost <= 104
        cost = info_cost+maintenance_cost+actuation_cost+2*acquisition_ops
        energy = min(F(7500), energy+1154-cost)
        costs.append(cost)
        information_costs.append(nominal_info_cost)
        min_energy, min_service = min(min_energy,energy), min(min_service,*Y)
        assert operation_count <= 820
        max_side_operations = max(max_side_operations,operation_count)
        # Exact declared source dynamics with grid residue charged to omega.
        omega = (F(9,1000), F(-9,1000)) if (tick//97)%2 == 0 else (F(-9,1000),F(9,1000))
        varpi = (F(operation_count,100000),F(-operation_count,100000))
        next_x = []
        for j in range(2):
            flow = a*F(x[j],GRID)+c*F(x[1-j],GRID)-sum(weights[i]*actual_u[i][j] for i in range(N))
            exact_increment = GRID*DELTA*(flow+omega[j]+varpi[j])
            grid_increment = nearest(exact_increment)
            residue = (F(grid_increment)-exact_increment)/(GRID*DELTA)
            assert abs(residue) <= F(1,2000) and abs(omega[j]+residue) <= F(1,100)
            assert abs(varpi[j]) < F(1,100)
            next_x.append(x[j]+grid_increment)
        x = tuple(next_x)
        radius = max(abs(F(v,GRID)) for v in x)
        max_state = max(max_state,radius)
        trace_digest.update(f'{tick}:{x}:{energy}:{Y}:{len(current_bad)}\n'.encode())
        if radius > 1 or min(Y) < F(3,10) or energy < 0:
            violation = {'tick':tick,'state':[str(F(v,GRID)) for v in x], 'service':[str(y) for y in Y], 'energy':str(energy)}
            if repair:
                raise AssertionError((name,'mission violation',violation))
            break
    envelope, worst = within_interval_envelope(costs)
    nominal_envelope, nominal_worst = within_interval_envelope(information_costs,F(325),F(6500))
    assert envelope and nominal_envelope
    if repair:
        assert len(functional_returns) == len(acquired_targets)+1, (name,functional_returns)
        assert all(r['elapsed'] <= HORIZON+6 for r in functional_returns)
        assert release_persistence == acquired_targets and inequality_views and correct_disagreement is not None
        assert max_state <= RADIUS and min_service >= F(3,10) and min_energy >= 0
    else:
        assert violation is not None
    return {'name':name,'ticks_executed':len(costs),'repair_enabled':repair,'weighted':weighted,
            'same_run_checks':'physical state, actual service, resource stock, raw inquiry, stored program, addressed repair, retained credentials and queued effects',
            'max_abs_state':str(max_state),'minimum_actual_coordinate_service':str(min_service),
            'minimum_resource_stock':str(min_energy),'max_effect_error_for_derived_good_paths':str(max_effect_error),
            'maximum_derived_impaired_paths':max_observed_bad,'cumulative_bad_report_domains':len(exposure),
            'unequal_local_estimates_observed':inequality_views,'functional_returns':functional_returns,
            'unequal_correct_estimates_and_effects_witness':correct_disagreement,
            'release_preserved_dirty_code_and_known_keys':release_persistence,
            'maximum_recipient_ingress_bits_per_tick':max_ingress,'maximum_apparatus_egress_bits_per_tick':max_egress,
            'maximum_requester_word_operations_per_tick':max_ops,'maximum_row_samples_per_tick':max_samples,
            'maximum_physical_side_effect_operations_per_tick':max_side_operations,
            'actual_cost_interval_excess_above_1153L':str(worst),
            'nominal_information_interval_excess_above_325L':str(nominal_worst),
            'violation':violation,'counters':dict(sorted(counters.items())),'trace_sha256':trace_digest.hexdigest()}


def local_checks():
    # All mutable policy state is restored through actual writes. These checks
    # compare state transitions, not a contamination label masquerading as code.
    actor = LocalMachine(3)
    actor.poison(3)
    assert actor.step([])[1].value == (-2000,-2000)
    arbitrary = LocalMachine(3)
    arbitrary.mem[0][:16] = bytes([OP_ADMIT])*16
    _,_,bounded_ops,_,_ = arbitrary.step([(r,1<<63) for r in range(16)])
    assert bounded_ops <= 10000
    maximum_corrupt_ops = 0
    for opcode in range(256):
        for age in (0,3,8,9):
            machine = LocalMachine(3)
            machine.mem[0][:16] = bytes([opcode])*16
            machine.mem[4][0] = 0
            machine.mem[4][1], machine.mem[4][3], machine.mem[4][4] = age,1,1
            for row in range(ROWS):
                machine.mem[3][3*row] = 1
                put16(machine.mem[3],3*row+1,4000-100*row)
            _,command,count,_,_ = machine.step([(r,fixed_packet(r,0,0)) for r in range(16)])
            maximum_corrupt_ops = max(maximum_corrupt_ops,count)
            assert count <= 10000 and (command is None or all(-2000 <= v <= 2000 for v in command.value))
    actor.halt()
    for block in range(1,8):
        actor.write(block,image(3)[block])
    assert not actor.boot(3)
    for _ in range(12):
        actor.step([])
    assert actor.step([])[1].value == (-2000,-2000)
    actor.halt()
    for block in range(8):
        actor.write(block,image(3)[block])
    assert actor.boot(3)
    assert actor.step([])[1] is None  # no fabricated postboot estimate
    assert actor.mem[4][0] == 11
    # Merely declaring contamination absent has no effect on the dispatched code.
    actor.poison(3)
    actor.contaminated = False
    assert actor.step([])[1].value == (-2000,-2000)
    # Actor observations/program state identical => same prescribed actions,
    # despite changed analyst labels. No true state/fault/cure argument exists.
    first, second = LocalMachine(2), LocalMachine(2)
    second.contaminated = True
    for t in range(30):
        incoming = [(row,fixed_packet(row,(t//10)&1,100+row)) for row in range(14)] if t%10==3 else []
        assert first.step(incoming) == second.step(incoming)
        assert first.mem == second.mem
    # Provider is total on malformed requests and has expiring bounded memory.
    provider = Provider(0)
    assert not provider.admit(0,1<<15) and not provider.admit(13,0)
    assert provider.admit(0,0)
    assert not provider.admit(0,0)
    for _ in range(9): provider.tick()
    assert provider.admit(0,0)  # reuse after expiry, not permanent epoch rejection
    # Correct fixed-word packets plus forged metadata: all outcomes explicit.
    for row in range(ROWS):
        assert parse_packet(fixed_packet(row,0,4000),row,0,ROWS)==4000
        assert parse_packet(fixed_packet(row,0,4000),row,1,ROWS) is None
        assert parse_packet(fixed_packet(row,0,4000)|(1<<63),row,0,ROWS) is None
    assert ROWS*16 == 672 <= 1024
    assert 14*64 == 896 <= 1024 and N*64 == 832 <= 1024
    # False READY is just unknown/malformed input, never a repair predicate.
    false_ready = (63, (1<<63)|123)
    clean = LocalMachine(4)
    before = clean.mem[4][4]
    clean.step([false_ready])
    assert clean.mem[4][4] == before == 0
    # Corrupting a consumed local validity field changes a real command, while
    # source mission evaluation remains external to this mutable monitor state.
    nominal, altered = LocalMachine(5), LocalMachine(5)
    for machine in (nominal,altered):
        machine.mem[4][0] = 0
        machine.mem[4][1] = 3
        put16(machine.mem[7],0,1000)
        put16(machine.mem[7],2,1000)
    altered.mem[4][4] = 1
    assert nominal.step([])[1] is None
    changed_command = altered.step([])[1]
    assert changed_command.value == (1600,1600)
    return {'partial_image_still_dispatches_actual_hostile_program':True,
            'full_addressed_image_boot_requires_drain_and_new_evidence':True,
            'analyst_fault_labels_do_not_change_local_policy':True,
            'false_ready_cannot_publish_or_boot':True,
            'corrupt_expensive_code_has_total_bounded_timeout':True,
            'repeated_corrupt_opcode_cases':1024,'maximum_corrupt_opcode_word_operations':maximum_corrupt_ops,
            'corrupt_consumed_validity_field_changes_actual_command':[1600,1600],
            'request_bits_per_round':672,'reply_lane_bits':896,'provider_reply_bits':832,
            'image_blocks':8,'bytes_per_block':BLOCK_BYTES,'write_bits_per_tick':8*BLOCK_BYTES,
            'packet_metadata_cases':3*ROWS,'quota_expiry_and_malformed_requests':True}


def checks():
    local = local_checks()
    scenarios = [
        simulate('joint_evolving_targets',metadata=True,full_power=True),
        simulate('heterogeneous_weights_and_initial_corner',weighted=True,x0=(-500000,500000),a=F(9,200),c=F(11,200)),
        simulate('source_only_acquisitions_same_budget',source_only=True,metadata=True),
        simulate('common_dependency_loss_and_actual_reconstruction',dependency_mode=True,metadata=True),
        simulate('same_mission_no_repair_actual_code_counterexample',repair=False,x0=(500000,500000))]
    root = Path(__file__).parent
    names = ('joint_model.py','REALIZATION.md','information_model.py')
    hashes = {name:hashlib.sha256((root/name).read_bytes().replace(b'\r\n',b'\n')).hexdigest() for name in names}
    return {'status':'passed','scope':'finite same-run execution checks, not universal source-policy verification',
            'sources_sha256_lf':hashes,'local_checks':local,'scenarios':scenarios}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--check',action='store_true')
    parser.add_argument('--write-results',action='store_true')
    args = parser.parse_args()
    result = checks()
    path = Path(__file__).with_name('joint_results.json')
    if args.check:
        assert json.loads(path.read_text(encoding='utf-8')) == result, 'joint source/results mismatch'
    if args.write_results:
        path.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,indent=2))


if __name__ == '__main__':
    main()

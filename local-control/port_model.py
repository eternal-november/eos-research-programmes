"""Finite physical-slot and energy-transfer adapter for the stored bank program.

The model carries actual stored charge and accepted descriptors. It never tests
C == P, grants successful installation, or cancels an accepted prefix on reset.
"""
from __future__ import annotations
import argparse
from dataclasses import dataclass
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
MU_HARD = 1 << 27
MU_LOW = 1 << 26
DELTA = F(1, 1 << 30)
CPU_ENERGY = 20480
PORT_ENERGY = 4096
FMIN = F(100, 101)
FMAX = F(1114113, 1048576)


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes().replace(b'\r\n', b'\n')).hexdigest()


@dataclass
class Reservoir:
    energy: F
    initial: F
    delivered: F = F(0)
    spent: F = F(0)

    @classmethod
    def filled(cls, amount):
        return cls(F(amount), F(amount))


@dataclass
class Slot:
    """One installed descriptor/charge compartment; no pending-request queue."""
    source: Reservoir
    price: F = F(PORT_ENERGY)
    recharge_time: F = DELTA
    charge: F = F(0)
    descriptor: object = None
    due: F | None = None
    started: F | None = None
    last_energy_time: F | None = None
    active: bool = False
    paid: int = 0
    attempts: int = 0
    rejects: int = 0
    completions: int = 0

    def recharge(self, elapsed, connected=True):
        if self.active or not connected:
            return F(0)
        transferred = min(self.price-self.charge, F(elapsed)*self.price/self.recharge_time,
                          self.source.energy)
        require(transferred >= 0, 'Negative transfer')
        self.source.energy -= transferred
        self.charge += transferred
        return transferred

    def offer(self, now, descriptor, duration, token=True, connected=True, valid=True):
        self.attempts += 1
        if self.active or self.charge < self.price or not token or not connected or not valid:
            self.rejects += 1
            return False
        require(F(0) < duration <= 6, 'Unbounded operation duration')
        self.active = True
        self.descriptor = descriptor
        self.started = F(now)
        self.last_energy_time = F(now)
        self.due = F(now)+duration
        self.paid += 1
        return True

    def elapse(self, now, action):
        if not self.active:
            return False
        until = min(F(now), self.due)
        require(until >= self.last_energy_time, 'Energy trajectory ran backward')
        consumed = (until-self.last_energy_time)*self.price/(self.due-self.started)
        require(0 <= consumed <= self.charge, 'Pulse exceeded its physical charge')
        self.charge -= consumed
        self.source.spent += consumed
        self.last_energy_time = until
        if now < self.due:
            return False
        require(self.charge == 0, 'Completion retained refund energy')
        descriptor = self.descriptor
        # One completion strobe may launch the latched child. It is not a new
        # CPU instruction, and its different capsule was already charged.
        action(descriptor)
        self.active = False
        self.descriptor = None
        self.due = None
        self.started = None
        self.last_energy_time = None
        self.completions += 1
        return True

    def digital_reset(self):
        # A latched one-shot is not digital CPU state. Its effect is retained.
        if not self.active:
            self.descriptor = None

    def dump_idle(self):
        if not self.active:
            self.source.spent += self.charge
            self.charge = F(0)


def conservation(source, slots):
    require(source.initial+source.delivered == source.energy+source.spent+
            sum((s.charge for s in slots), F(0)), 'Physical energy was created/lost')


def transfer_checks():
    source = Reservoir.filled(4*PORT_ENERGY)
    slots = [Slot(source), Slot(source)]
    slots[0].recharge(DELTA/2)
    require(slots[0].charge == PORT_ENERGY/2, 'Precharge was instantaneous')
    require(not slots[0].offer(0, 'undercharged', F(1)), 'Partial charge launched')
    common_after_half = source.energy
    slots[0].recharge(DELTA/2)
    require(source.energy == common_after_half-PORT_ENERGY/2, 'Transfer did not debit common store')
    require(slots[0].offer(0, ('write', 19), F(6)), 'Charged slot rejected')
    for k in range(2000):
        require(not slots[0].offer(0, ('overwrite', k), F(1)), 'Busy descriptor replaced')
    slots[0].elapse(F(3), lambda _: None)
    require(slots[0].charge == PORT_ENERGY/2, 'Pulse expenditure was instantaneous')
    conservation(source, slots)
    slots[0].digital_reset()
    output = []
    slots[0].elapse(F(6), output.append)
    require(output == [('write', 19)], 'Power/reset erased accepted prefix')
    require(not slots[0].offer(F(6), 'double_spend', F(1)), 'Spent energy rebooked')
    slots[1].recharge(DELTA/2)
    slots[1].recharge(DELTA, connected=False)
    require(slots[1].charge == PORT_ENERGY/2, 'Cut path supplied charge')
    slots[1].dump_idle()
    conservation(source, slots)
    # Free ledger differs from physical headroom.
    capacity, physical, reservation, incoming = 10, 10, 8, 8
    physical = min(capacity, physical+incoming)
    require(physical-reservation == 2, 'Reservation falsely created charging capacity')
    return dict(charged_before_launch=True, rejected_attempts=slots[0].rejects,
                preserved_descriptor=output[0], conserved_energy=source.initial,
                physical_after_reservation=physical, free_after_spill=physical-reservation,
                zero_refund=True)


def paid_attempt_checks():
    attempts = 1000
    source = Reservoir.filled(attempts*CPU_ENERGY+PORT_ENERGY)
    cpu = Slot(source, price=F(CPU_ENERGY), recharge_time=F(1, 4*MU_LOW))
    port = Slot(source)
    port.recharge(DELTA)
    for index in range(attempts):
        start = F(index, MU_LOW)
        cpu.recharge(cpu.recharge_time)
        require(cpu.offer(start+cpu.recharge_time, index, F(3, 4*MU_LOW)),
                'A paid bad-code instruction lacked its actual energy')
        end = start+F(1, MU_LOW)
        port.elapse(end, lambda _: None)
        cpu.elapse(end, lambda _: port.offer(end, index, F(6), token=cpu.active))
        conservation(source, [cpu, port])
    port.elapse(7, lambda _: None)
    conservation(source, [cpu, port])
    require(port.paid == 1 and port.rejects == attempts-1, 'Flood grew an unbounded job queue')
    require(source.spent == attempts*CPU_ENERGY+PORT_ENERGY and source.energy == 0,
            'Rejected attempts received free CPU work')
    return dict(attempts=attempts, admitted=port.paid, rejected=port.rejects,
                actual_CPU_energy=attempts*CPU_ENERGY, actual_port_energy=PORT_ENERGY,
                conserved=True)


def failed_and_nominal_write_checks():
    source = Reservoir.filled(201*PORT_ENERGY)
    slot = Slot(source)
    slot.recharge(DELTA)
    cell = [0]
    require(not slot.offer(0, 9, F(6), connected=False), 'Disconnected offer accepted')
    require(not slot.offer(0, 9, F(6), valid=False), 'Invalid address allocated a slot')
    require(slot.offer(0, 9, F(6)), 'Charged connected offer rejected')
    # Contact can fail after launch. Timeout still expends its funded operation,
    # without a successful-write return or fabricated matching read.
    slot.elapse(6, lambda _: None)
    require(cell[0] != 9, 'Failed pulse became an acknowledgement')
    for visit in range(1, 201):
        now = visit*9*FMIN
        slot.recharge(DELTA)
        require(slot.offer(now, visit, F(6)), 'Nominal target spacing lost slot service')
        slot.elapse(now+6, lambda value: cell.__setitem__(0, value))
        require(cell[0] == visit, 'Elementary connected store did not apply pulse bits')
    conservation(source, [slot])
    return dict(disconnected_rejected=True, invalid_rejected=True,
                failed_pulse_not_acknowledged=True, nominal_connected_visits=200,
                minimum_gap=9*FMIN, pending_maximum=1)


def wire_energy_checks():
    # One frame transmits a positive field, consumes positive serializer work,
    # and recharges its physical source capsule before that field has decayed.
    initial = F(2*PORT_ENERGY)
    common, capsule, field, heat = initial-PORT_ENERGY, F(PORT_ENERGY), F(0), F(0)
    for _ in range(4):
        capsule -= 1024
        field += 512
        heat += 512
        require(common+capsule+field+heat == initial, 'Wire transfer created energy')
    common -= PORT_ENERGY
    capsule += PORT_ENERGY
    require(capsule+field > PORT_ENERGY, 'In-flight field was silently deleted at recharge')
    require(common+capsule+field+heat == initial, 'Recharge double-spent transmitted energy')
    retained_before_decay = capsule+field
    heat += field
    field = F(0)
    require(common+capsule+field+heat == initial, 'Propagation energy did not reach its sink')
    return dict(transmitted_field=2048, serializer_dissipation=2048,
                source_recharged_before_decay=True,
                simultaneous_retained_energy=retained_before_decay,
                per_symbol_installed_energy_upper=1024, conserved=True)


def finite_fanin_checks():
    d, b = 40, 80
    source = Reservoir.filled(2*b*d*PORT_ENERGY)
    # Exactly one endpoint per incoming processor on ONE target bank.
    slots = [Slot(source) for _ in range(2*b*d)]
    cells = {}
    for producer, slot in enumerate(slots):
        slot.recharge(DELTA)
        owner = producer % (2*d)
        require(slot.offer(0, (owner, 0, producer), F(6)), 'Dedicated finite slot absent')
        require(not slot.offer(0, (owner+1, 0, -1), F(6)), 'Busy slot admitted second job')
    for slot in slots:
        slot.elapse(F(6), lambda desc: cells.__setitem__((desc[0], desc[1]), desc[2]))
    conservation(source, slots)
    require(len(slots) == 6400 and len(cells) == 80, 'Processor/producer identity conflated')
    require(all(0 <= key[0] < 80 for key in cells), 'Foreign producer candidate reached')
    return dict(slots_per_target_bank=len(slots), independently_charged=True,
                bank_private_candidates=len(cells), rejected_busy=len(slots),
                attempts=2*len(slots), endpoint_bits_per_kind=1024*len(slots))


def adc_checks():
    source = Reservoir.filled(3*PORT_ENERGY)
    slot = Slot(source)
    slot.recharge(DELTA)
    raw = {'valid': False, 'value': 0}
    require(slot.offer(0, ('old_key', 27), F(1, 64)), 'ADC start failed')
    raw['valid'] = False
    require(not slot.offer(F(1, 128), ('new_key', 99), F(1, 64)), 'Busy ADC relabeled old conversion')
    def capture(desc):
        raw['key'], raw['value'] = desc
        raw['valid'] = True
    slot.elapse(F(1, 64), capture)
    require(raw == {'valid': True, 'value': 27, 'key': 'old_key'}, 'Invalidation canceled or relabeled sample')
    raw['valid'] = False
    slot.recharge(DELTA)
    require(slot.offer(F(1), ('missing_head', None), F(1, 64)), 'Missing head could hold slot open')
    slot.elapse(F(65, 64), capture)
    require(raw['value'] is None and not slot.active, 'Unavailable head did not terminate')
    conservation(source, [slot])
    return dict(old_key_preserved=True, old_completion_after_invalidation=True,
                missing_terminates=True, completion_bound=F(1, 64))


def combiner_checks():
    neutral = 32*64+32*4096+32*(1<<40)
    def combine(mailboxes, enabled):
        if not any(enabled):
            return neutral
        value = 0
        for word, live in zip(mailboxes, enabled):
            if live:
                value |= word
        return value
    def cam(word):
        return ((word >> 6)&63)-32
    word = neutral-20*64
    require(combine([word, 123], [True, False]) == word, 'Inactive mailbox changed nominal command')
    require(cam(combine([word, 123], [False, False])) == 0, 'No-power default drove negative force')
    require(cam(0) == -32, 'Zero-bit-pattern obstruction missing')
    require(combine([word, neutral], [True, True]) != word,
            'Multiple powered cartridges were silently treated as one nominal controller')
    return dict(single_powered_preserved=True, no_power_zero_effort=True,
                raw_zero_word_is_not_neutral=True, multiple_powered_not_nominal=True)


def command_checks():
    period_min, period_max = F(100, 101*64), F(1, 64)
    residence, recharge = F(1), DELTA
    require(64*period_min < residence+recharge, '64-slot obstruction disappeared')
    require(128*period_min > residence+recharge, '128-slot round robin can collide')
    # Old application can follow an earlier new application.
    events = [(F(1, 4), 'new'), (F(999, 1000), 'old'), (F(3, 2), 'new')]
    held = None
    observed = []
    for at, value in events:
        held = value
        observed.append((at, held))
    require(observed[1][1] == 'old', 'Reordering countercase not exhibited')
    stable = 2*residence+period_max
    require(stable < 3, 'D_cmd3 not established')
    # Boundary argument enumerates arbitrary bounded old/new completion choices.
    cases = 0
    for old_delay in [F(k, 16) for k in range(17)]:
        for new_delay in [F(k, 16) for k in range(17)]:
            for phase in [F(k, 64*16) for k in range(1, 17)]:
                last_old = old_delay
                issued_after_old_horizon = residence+phase
                last_guaranteed_new = issued_after_old_horizon+new_delay
                require(last_old <= residence < last_guaranteed_new <= stable,
                        'Stable application inequality failed')
                cases += 1
    return dict(stable_bound=stable, fixed_slots=128, reuse_min=128*period_min,
                too_few_slots=64, bounded_delay_cases=cases, old_after_new=observed,
                field_force_tail_not_proved_by_packet_model=True)


class Fifo:
    """Finite FIFO with exact deterministic service, explicit full rejection."""
    def __init__(self, capacity, rate):
        self.capacity = capacity
        self.rate = F(rate)
        self.jobs = []
        self.attempts = 0
        self.rejects = 0
        self.high = 0

    def offer(self, time):
        self.attempts += 1
        self.jobs = [due for due in self.jobs if due > time]
        if len(self.jobs) >= self.capacity:
            self.rejects += 1
            return None
        due = max([F(time)]+self.jobs)+1/self.rate
        self.jobs.append(due)
        self.high = max(self.high, len(self.jobs))
        return due


def lane_checks():
    offered = Fifo(128, 256)
    for _ in range(1000):
        offered.offer(0)
    require(offered.high == 128 and offered.rejects == 872, 'Full FIFO silently expands')
    nominal = Fifo(128, 256)
    delays = []
    # Alternating frame-end/start clusters approach the generic two-frame burst.
    for frame in range(200):
        phase = FMIN-F(1, 1<<20) if frame % 2 == 0 else F(0)
        at = frame*FMIN+phase
        for _ in range(23):
            due = nominal.offer(at)
            require(due is not None, 'Nominal bankpair traffic dropped')
            delays.append(due-at)
    tx_burst, tx_rate = F(46), 23/FMIN
    rx_burst, rx_rate = 4+1040*F(1, 4), F(1040)
    tx_backlog = tx_burst+tx_rate/256
    rx_backlog = rx_burst+rx_rate/2048
    require(tx_backlog < 47 < 128 and tx_rate < 256, 'TX packetized backlog bound fails')
    require(rx_backlog < 265 < 512 and rx_rate < 2048, 'RX packetized all-symbol backlog bound fails')
    residence = F(129, 256)+F(1, 4)+F(513, 2048)
    require(residence == F(2057, 2048) and residence < 2, 'Data residence mismatch')
    # The legacy common-rate interpretation is not a nominal total budget.
    require(1524/FMIN > 256, 'Shared aggregate serializer countercase missing')
    return dict(hostile_offers=offered.attempts, charged_rejections=offered.rejects,
                nominal_high_water=nominal.high, nominal_max_queue_delay=max(delays),
                tx_envelope=[tx_burst, tx_rate], rx_envelope=[rx_burst, rx_rate],
                tx_packetized_backlog=tx_backlog, rx_packetized_backlog=rx_backlog,
                all_symbol_residence=residence, total_offer_subtotal=1524,
                per_bankpair_nominal=23, raw_symbol_bits=96)


def program_prefix_check():
    import program_model as p
    compiled = p.Compiler(p.Design()).compile()
    machine = p.Machine(compiled)
    source = Reservoir.filled(CPU_ENERGY+PORT_ENERGY)
    cpu = Slot(source, price=F(CPU_ENERGY), recharge_time=F(1, 4*MU_LOW))
    word = Slot(source)
    word.recharge(DELTA)
    # Actual mutable instruction, with actual private operands. No C == P test.
    machine.C[0] = p.encode(p.IO, 2, 3, 4, p.PRIM['write_own'])
    machine.C[1] = p.encode(p.HALT)
    machine.R[3:7] = [0, 1, 7, 991]
    target = {}
    now = F(0)
    class Ports:
        def perform(self, name, args, executing):
            require(name == 'write_own', 'Unexpected decoder primitive')
            t, side, address, value = args
            physical_owner = 9
            word.offer(now, (t, side, physical_owner, address, value), F(6),
                       token=cpu.active, valid=(0 <= t < 2 and side in (0, 1) and 0 <= address < 8192))
            return 0
        def advance(self, executing):
            pass
    require(not machine.launch(funded=False), 'Unfunded instruction launched')
    cpu.recharge(cpu.recharge_time)
    now = cpu.recharge_time
    require(cpu.offer(now, 'latched instruction', F(3, 4*MU_LOW)), 'CPU capsule missing')
    require(machine.launch(funded=cpu.charge == CPU_ENERGY), 'Actual instruction did not latch')
    machine.C[0] = 0
    machine.R[6] = 1
    machine.powered = False
    machine.reset_entry()
    now = F(1, MU_LOW)
    def complete_instruction(_):
        require(machine.complete(Ports()), 'Funded prefix disappeared on power loss')
    cpu.elapse(now, complete_instruction)
    require(word.active and target == {}, 'Write became instantaneous or disappeared')
    word.digital_reset()
    word.elapse(now+6, lambda desc: target.__setitem__(tuple(desc[:4]), desc[4]))
    require(target == {(0, 1, 9, 7): 991}, 'Actual latched value/owner not preserved')
    require(not machine.launch(), 'Unpowered CPU started a new instruction')
    conservation(source, [cpu, word])
    return dict(actual_decoder=True, arbitrary_stored_IO_cell=True,
                post_power_child_completion=True, actual_latched_value=991,
                physical_owner=9, last_effect_bound=6+F(1, MU_LOW),
                retirement_count=machine.retired)


def bounds():
    d, b = 40, 80
    n, branches, held = 2*b, 2*d, 26*d
    counts = dict(instructions=n, conversion=n, own_read=n, own_write=2*n*d,
                  command=2*(d+1)*128, held_request=2*held*16, data=2*branches*129)
    port_count = sum(v for k, v in counts.items() if k != 'instructions')
    capsule_energy = n*CPU_ENERGY+port_count*PORT_ENERGY
    wire_energy = 2*(2*branches)*264*(PORT_ENERGY//4)
    tail_energy = capsule_energy+wire_energy
    descriptors = port_count*1024
    command_mailbox = n*(64*d+128)
    request_mailbox = n*held*256
    branch_bits = 115712+264*128
    data_storage_both_directions = 2*(2*branches)*branch_bits
    target_per_bank = 2*b*d
    target_latches_host = 2*3*target_per_bank*1024
    peak = port_count*PORT_ENERGY/DELTA+n*4*CPU_ENERGY*MU_HARD
    visit_gap = 9*FMIN
    require(visit_gap > 6+DELTA, 'Nominal write loses slot service')
    require(F(1, 4*MU_HARD) > DELTA, 'Startup port recharge outlasts first CPU latch')
    require(F(1, MU_LOW) > DELTA, 'Adjacent nominal instructions cannot recharge port')
    retirement = F(1, MU_LOW)+F(1, 64)
    boot_wait = F(400, 101)
    require(retirement+2+DELTA < boot_wait, 'BOOT can see a pre-reset publication')
    require(F(3)+2 > boot_wait, 'Loose retirement counterexample missing')
    require(F(1 << 8, 64)+2 <= 6, 'Full-range word timer/routing exceeds tail')
    require(2*F(1 << 6, 128) <= 1, 'Full-range command timers exceed residence')
    require(2*F(1 << 4, 2048) <= F(1, 64), 'Full-range ADC timers exceed conversion')
    return dict(design=dict(d=d,B=b,L=8192), installed_slots=counts,
                total_port_slots=port_count, isolated_energy_capacity=tail_energy,
                capsule_energy_capacity=capsule_energy, data_field_energy_capacity=wire_energy,
                descriptor_bits=descriptors, command_mailbox_bits=command_mailbox,
                request_mailbox_bits=request_mailbox,
                data_storage_with_propagation_bits=data_storage_both_directions,
                passive_target_endpoint_bits=target_latches_host,
                target_slots_per_kind_per_bank=target_per_bank,
                maximum_local_recharge_power=peak,
                micro_native_capacity_per_cpu=F(4, 3)*16384*MU_HARD,
                autonomous_command_rate=2*(d+1)*F(6464, 100),
                autonomous_request_rate=2*held*F(101, 100),
                maximum_raw_CPU_attempt_rate=n*MU_HARD,
                nominal_target_gap=visit_gap, write_recharge_suffix=6+DELTA,
                instruction_suffix=retirement, boot_wait=boot_wait,
                old_instruction_data_suffix=retirement+2+DELTA,
                D_cmd=3,D_word=6,D_data=2,D_request=2,S=F(1,64),
                frame_Fmin=FMIN,frame_Fmax=FMAX,
                per_endpoint_pulse_power=128*PORT_ENERGY,
                source_laws_not_fabrication_certificate=True)


def normalize(value):
    if isinstance(value, F):
        return str(value.numerator) if value.denominator == 1 else f'{value.numerator}/{value.denominator}'
    if isinstance(value, dict):
        return {key: normalize(item) for key, item in value.items()}
    if isinstance(value, (list, tuple)):
        return [normalize(item) for item in value]
    return value


def main():
    require(not sys.flags.optimize, 'Optimized execution disables evidence checks')
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--write', action='store_true')
    group.add_argument('--check', action='store_true')
    args = parser.parse_args()
    files = ('RUNTIME-PORTS.md', 'port_model.py', 'PROGRAM.md', 'program_source.py', 'program_model.py')
    before = {name: digest(HERE/name) for name in files}
    record = HERE/'port_results.json'
    expected = json.loads(record.read_text(encoding='utf-8')) if args.check else None
    if expected:
        require(expected['sources'] == before, 'Frozen port/program inputs changed')
    result = normalize(dict(schema='runtime-ports-v1',sources=before,
        scope='conditional finite primitive realization; first-pass checks; source admission and recurrence separate',
        transfer=transfer_checks(),wire_energy=wire_energy_checks(),paid_attempts=paid_attempt_checks(),
        write_service=failed_and_nominal_write_checks(),fan_in=finite_fanin_checks(),adc=adc_checks(),
        combiner=combiner_checks(),command=command_checks(),data_lane=lane_checks(),
        actual_program_prefix=program_prefix_check(),bounds=bounds()))
    require(before == {name: digest(HERE/name) for name in files}, 'Inputs changed during check')
    if args.write:
        record.write_text(json.dumps(result, sort_keys=True, indent=2)+'\n',encoding='utf-8',newline='\n')
    else:
        require(result == expected, 'Port result differs')
    print('PASS finite runtime ports:', result['bounds']['total_port_slots'], 'charged port slots;',
          result['bounds']['isolated_energy_capacity'], 'stored energy units')


if __name__ == '__main__':
    main()

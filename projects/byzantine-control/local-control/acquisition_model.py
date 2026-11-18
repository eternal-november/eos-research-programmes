"""Finite physical-origin publication, receipt age, and logical-bank read checks.

Analyst sample times, physical keys and fault footprints are diagnostic ghosts.
The consumer receives only direct comparison flags; no good-set or true-time API.
"""
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product, combinations
from pathlib import Path
from math import ceil
import argparse
import hashlib
import importlib.util
import json
import os
import subprocess
import sys

HERE = Path(__file__).resolve().parent
LEAN = Path(os.environ['USERPROFILE']) / '.elan/toolchains/leanprover--lean4---v4.33.0/bin/lean.exe'


def require(value, message):
    if not value:
        raise RuntimeError(message)


def serial(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): serial(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [serial(v) for v in value]
    return value


@dataclass(frozen=True)
class Packet:
    key: int
    value: int
    claimed_time: int
    sampled: F  # Ghost; never consulted by admission, expiry, or comparisons.
    physical_key: int  # Ghost trace of the actual head selected.


class Cache:
    """One source-side raw I cache, initialized by actual ordinary writes."""
    def __init__(self, lifetime=F(2)):
        self.packet = None
        self.remaining = F(0)
        self.lifetime = lifetime
        self.work = 0

    def invalidate(self):
        self.packet = None
        self.remaining = F(0)
        self.work += 2

    def completed(self, packet):
        self.packet = packet
        self.remaining = self.lifetime
        self.work += 2

    def elapse(self, duration):
        self.remaining = max(F(0), self.remaining-duration)
        self.work += 1

    def request(self, token, clear=False):
        # Public tokens, claimed time and CLEAR do not prolong this cache.
        self.work += 1
        if clear:
            self.invalidate()

    def emit(self):
        self.work += 1
        return self.packet if self.remaining > 0 else None


class Receipt:
    """One physically separate origin/bank/key I word and bounded raw timer.

    Gate and counter are faultable input state. Counter decrement is a nominal
    raw-circuit law; a stuck circuit is a persistent path defect, not recovery.
    """
    def __init__(self, lifetime, maximum=2000):
        self.lifetime = int(lifetime)
        self.cap = (1 << max(1, self.lifetime.bit_length()))-1
        self.maximum = maximum
        self.word = maximum+1
        self.remaining = F(0)
        self.output_connected = True
        self.clock_powered = True
        self.packet = None  # Ghost diagnostic; read_compare never sees it.
        self.work = self.receipts = self.comparisons = 0

    def receive(self, packet):
        self.word = packet.value
        self.remaining = F(self.lifetime)
        self.packet = packet
        self.work += 2
        self.receipts += 1

    def raw_corrupt(self, value, counter=None):
        self.word = value
        self.packet = None
        if counter is not None:
            require(0 <= counter <= self.cap, 'Counter corruption escapes actual finite word')
            self.remaining = F(counter)
        self.work += 1

    def elapse(self, duration, clock_rate=F(1)):
        require(F(1) <= clock_rate <= F(101,100), 'Nominal clock outside admitted rate')
        if self.clock_powered:
            self.remaining = max(F(0), self.remaining-duration*clock_rate)
            self.work += 1

    def mask(self):
        self.output_connected = False

    def pause(self):
        self.output_connected = False
        self.clock_powered = False

    def resume_initialized(self):
        # Actual two field writes before actual reconnection, not a healthy flag.
        self.remaining = F(0)
        self.word = self.maximum+1
        self.packet = None
        self.work += 2
        self.clock_powered = True
        self.output_connected = True

    def read_compare(self, operation, threshold):
        require(operation in ('le','eq'), 'Unknown direct word operation')
        self.comparisons += 1
        self.work += 1
        raw_operand = self.word if self.output_connected and self.remaining > 0 else self.maximum+1
        return raw_operand <= threshold if operation == 'le' else raw_operand == threshold

    def nominal_age(self, now):
        if self.output_connected and self.remaining > 0 and self.packet is not None:
            return now-self.packet.sampled
        return None


class Lane:
    """One actual origin/bank bounded queue, with all attempts charged."""
    def __init__(self, capacity=128):
        self.capacity = capacity
        self.items = []
        self.offers = self.rejections = self.examinations = self.deliveries = 0
        self.cut = False

    def offer(self, packet, offered, delay):
        self.offers += 1
        self.examinations += 1
        if self.cut or len(self.items) >= self.capacity:
            self.rejections += 1
            return False
        require(delay >= 0, 'Negative raw transport delay')
        self.items.append((offered+delay, packet))
        return True

    def poll(self, now, records):
        # Bounded hardware queue and fixed-width decode; no supplied arrival list.
        keep = []
        for due, packet in self.items:
            self.examinations += 1
            if due <= now:
                if packet.key in records:
                    records[packet.key].receive(packet)
                    self.deliveries += 1
                else:
                    self.rejections += 1
            else:
                keep.append((due, packet))
        self.items = keep


def logical_compare(a, b, operation, threshold):
    first = a.read_compare(operation, threshold)
    second = b.read_compare(operation, threshold)
    return first or second


def inference(records, maximum=2000, threshold=None):
    """Private derived state only. Two raw flags per auxiliary logical origin."""
    private = {'lo':0, 'hi':maximum, 'count':0, 'pivot':0, 'passes':0, 'reads':0, 'work':14}
    if threshold is not None:
        private['pivot'] = threshold
        for origin,(a,b) in enumerate(records):
            private['count'] += logical_compare(a,b,'le',threshold)
            private['reads'] += 2
            private['work'] += 10
        private['work'] += 3
        return private['count'] >= 7, private
    while private['lo'] < private['hi']:
        private['pivot'] = (private['lo']+private['hi'])//2
        private['count'] = 0
        private['passes'] += 1
        private['work'] += 7
        for origin,(a,b) in enumerate(records):
            private['count'] += logical_compare(a,b,'le',private['pivot'])
            private['reads'] += 2
            private['work'] += 10
        if private['count'] >= 7:
            private['hi'] = private['pivot']
        else:
            private['lo'] = private['pivot']+1
        private['work'] += 3
    private['work'] += 3
    return private['lo'], private


def record(value=None, lifetime=64, remaining=None):
    r = Receipt(lifetime)
    if value is not None:
        r.receive(Packet(0,value,0,F(0),0))
    if remaining is not None:
        r.remaining = F(remaining)
    return r


def parameter_checks():
    kf, bf, bs, fanout = 643,16,1,80
    maximum, n = 2000,13
    passes = maximum.bit_length()
    row = 14+passes*(10*n+10)+3
    require(row == 1557, 'Incorrect two-bank word-work bound')
    raw = 160*(64+64)
    work = (bf+bs)*(22+4*fanout)+2*row+584+256+4*raw
    elapsed = F(bf+bs,64)+F(work,262144)
    minimum = F(4*raw,1)/F(262144*101,100)
    require(elapsed < 1 and F(17,1)/minimum < 64, 'Frame/egress rates do not close')
    pf = ceil(F(kf,bf))+1
    require(F(64,1)/F(101,100) > pf+2, 'Fast receipt lifetime cannot bridge publications')
    age = 1+2+2+64+2+3
    error = F(5,1000)+F(3316,1000)*F(age,250000)
    require(error <= F(2,100), 'Plant accuracy allocation fails')
    sizes = []
    for cells in (1,257,8192,65536):
        slow = 40*2*80*cells
        period = slow+1
        lifetime = ceil(F(101,100)*(period+3))
        cap = (1 << lifetime.bit_length())-1
        a_slow = 5+lifetime
        wait = ceil(F(101,100)*(a_slow+1))
        require(F(wait,1)/F(101,100) > a_slow, 'Freeze wait not strictly long enough')
        require(F(lifetime,1)/F(101,100) > slow+2, 'Slow lifetime cannot bridge publications')
        sizes.append(dict(image_cells=cells,slow_keys=slow,slow_period=period,receipt_lifetime=lifetime,
            corrupted_counter_cap=cap,read_age=a_slow,freeze_local_wait=wait,
            initial_unknown_tail_after_last_receipt=cap,target_scan=10*(80*cells+2),
            conservative_records_per_receiver=160*(slow+kf),
            raw_timer_tick_operations_per_unit_upper=F(101,100)*160*(slow+kf)))
    return dict(fast_keys=kf,fast_period=pf,frame_word_work=work,frame_elapsed_upper=elapsed,
        deliberate_minimum_frame=minimum,nominal_source_record_rate_upper=F(17,1)/minimum,
        raw_admission_attempt_bound=raw,two_row_word_work=2*row,
        two_row_raw_reads=4*13*passes,fast_read_age=69,fast_sample_to_effect_age=age,
        plant_error=error,fast_corrupted_counter_cap=127,image_sizes=sizes)


def cache_and_age_cases():
    count = retained = 0
    for conversion, emission, delay, lifetime, clock, retention in product(
            (0,1),(0,1,2),(0,1,2),(1,3,7),(F(1),F(101,100)),(F(0),F(1,2),F(1))):
        sample = F(0)
        cache = Cache(F(2))
        cache.completed(Packet(0,800,65535,sample,0))
        cache.elapse(F(emission))
        before = cache.remaining
        for nonce in range(5):
            cache.request(nonce)
        require(cache.remaining == before, 'Public requests refreshed source cache')
        packet = cache.emit()
        if packet is None:
            require(emission == 2, 'Unexpected nominal cache expiry')
            count += 1
            continue
        receipt = Receipt(lifetime)
        receipt.receive(packet)
        elapsed = retention*F(lifetime)/clock
        receipt.elapse(elapsed,clock)
        now = F(conversion+emission+delay)+elapsed
        if receipt.remaining > 0:
            age = receipt.nominal_age(now)
            require(age <= conversion+2+delay+lifetime, 'Actual age exceeds causal bound')
            require(receipt.read_compare('le',800), 'Nominal word disappeared before expiry')
            retained += 1
        else:
            require(not receipt.read_compare('le',800), 'Expired word remains a vote')
        count += 1
    arbitrary = 0
    for nominal_life in (1,2,3,7,8,15,64):
        r = Receipt(nominal_life)
        for counter in range(r.cap+1):
            r.raw_corrupt(0,counter)
            r.elapse(F(r.cap))
            require(not r.read_compare('le',1000), 'Bounded unknown timer did not expire')
            arbitrary += 1
    return dict(causal_age_cases=count,live_receipt_cases=retained,arbitrary_initial_counter_cases=arbitrary,
                source_cache_requests_never_refresh=True,forged_payload_timestamps_ignored=True)


def cyclic_publication_cases():
    cases = live_checks = raw_deliveries = 0
    largest_age = F(0)
    # A small table exhausts timing/phase cases, with the table-size law checked
    # separately at all actual inventory scales in parameter_checks.
    for phase, frame, delay, client_phase, drift in product(range(4),(2,3,4),(0,1,2),range(3),(F(1),F(101,100))):
        keys, lifetime = 5,32
        records = {key:Receipt(lifetime) for key in range(keys)}
        lane = Lane(128)
        cursor = 0
        for t in range(180):
            for r in records.values():
                r.elapse(F(1),drift if t%2 else F(1))
            if t >= phase and (t-phase)%frame == 0:
                packet = Packet(cursor,800+cursor,-100000,F(t),cursor)
                require(lane.offer(packet,F(t),F(delay)), 'Nominal source queue overflowed')
                cursor = (cursor+1)%keys
            # Each client has a different bounded admission phase, not a common poll.
            if (t-client_phase)%3 == 0:
                lane.poll(F(t),records)
            if t >= phase+keys*frame+delay+3:
                for key,r in records.items():
                    require(r.read_compare('eq',800+key), 'Periodic eligible key is unavailable')
                    age = r.nominal_age(F(t))
                    require(age is not None and age <= 5+32, 'Current-key age claim failed')
                    largest_age = max(largest_age,age)
                    live_checks += 1
        require(lane.rejections == 0, 'Nominal finite queue lost an eligible sample')
        raw_deliveries += lane.deliveries
        cases += 1
    return dict(timing_phase_cases=cases,live_key_reads=live_checks,delivered_records=raw_deliveries,
                largest_actual_age=largest_age,client_phase_variation=True)


def overlap_cases():
    cases = 0
    for width in range(1,9):
        intervals = []
        # Alternating physical A/B identities, reused, with exact width overlap.
        for k in range(12):
            intervals.append((k*10,k*10+10+width,k%2))
        for start in range(100):
            for separation in range(width+1):
                a_read,b_read = start,start+separation
                available_a = any(bank == 0 and lo <= a_read <= hi for lo,hi,bank in intervals)
                available_b = any(bank == 1 and lo <= b_read <= hi for lo,hi,bank in intervals)
                require(available_a or available_b, 'Complete-pair overlap failed')
                cases += 1
    miss = dict(a_read=0,b_read=2,new_a_valid_from=1,old_b_valid_until=1)
    require(not (miss['new_a_valid_from'] <= miss['a_read']) and
            not (miss['b_read'] <= miss['old_b_valid_until']), 'Sequential-read miss disappeared')
    return dict(pair_windows=cases,bank_reuses=6,instantaneous_coverage_counterexample=miss)


def logical_vote_cases():
    cases = 0
    for lower, upper in ((0,0),(0,1),(3,7),(970,990)):
        for a,b,pivot in product((None,lower,upper),repeat=3):
            if pivot is None:
                continue
            ra,rb = record(a),record(b)
            vote = logical_compare(ra,rb,'le',pivot)
            if vote:
                require(lower <= pivot, 'Successful logical vote escaped lower envelope')
            if (a is not None or b is not None) and pivot >= upper:
                require(vote, 'Available nominal vote failed at upper envelope')
            cases += 1
    rotated = 0
    for failed in combinations(range(13),6):
        failed = set(failed)
        inputs = [(record(0 if i in failed else 985),record(0 if i in failed else None)) for i in range(13)]
        value, state = inference(inputs)
        require(value == 985 and state['work'] <= 1557 and state['reads'] <= 286,
                'Logical-origin rotating case violates inference/work bound')
        rotated += 1
    low = [(record(970),record(None))]*6+[(record(990),record(None))]*6
    permitted,_ = inference([(record(970),record(970))]+low,threshold=970)
    deferred,_ = inference([(record(990),record(990))]+low,threshold=970)
    require(permitted and not deferred,'Primary observation is not action-relevant')
    primary_b = [(record(None),record(985))]+[(record(985),record(None)) for _ in range(12)]
    primary_value,_ = inference(primary_b)
    require(primary_value == 985,'Retiring physical primaryA lost the logical origin despite readyB')
    return dict(logical_implication_cases=cases,all_six_origin_subsets=rotated,
                primary_forgery_changes_permission=True,primary_A_retired_B_supplies=True,
                primary_two_records_remain_one_origin=True,private_algorithm_reads_no_fault_map=True)


def old_tail_and_reuse_cases():
    cases = 0
    for life, delay in product((3,7,8,64),(0,1,2)):
        good = record(1200,lifetime=life)
        old = record(400,lifetime=life)
        old.raw_corrupt(400,old.cap)
        cap = old.cap
        require(logical_compare(good,old,'le',970), 'Bad sibling was accidentally ignored')
        # Cut blocks new source sends; its last packet may arrive at D and set E.
        lane = Lane()
        lane.offer(Packet(0,400,65535,F(-100000),0),F(0),F(delay))
        lane.cut = True
        for t in range(delay+cap+2):
            if t:
                old.elapse(F(1))
            lane.poll(F(t),{0:old})
        require(not old.read_compare('le',970), 'Old packet/record survives finite tail')
        # Reuse the same A/B address repeatedly; no incrementing epoch/tag exists.
        for cycle in range(8):
            old.pause()
            old.raw_corrupt(400,cap)
            require(not old.read_compare('le',970), 'Disconnected output leaked stale word')
            old.resume_initialized()
            require(not old.read_compare('le',970), 'Actual entry writes failed to invalidate')
            old.receive(Packet(0,1200,cycle%2,F(cycle),0))
            require(old.read_compare('eq',1200),'Fresh reuse did not establish useful data')
            cases += 1
    initial = record(400,lifetime=64)
    initial.raw_corrupt(400,initial.cap)
    selected = record(1200,lifetime=64)
    require(logical_compare(selected,initial,'le',970),'Initial-I obstruction missing')
    initial.elapse(F(initial.cap))
    selected.receive(Packet(0,1200,0,F(127),0))
    require(not logical_compare(selected,initial,'le',970),'Initial unknown receipt failed quarantine')
    return dict(actual_bank_reuse_cases=cases,initial_unknown_record_needs_quarantine=True,
                input_initialization_not_charged_as_new_fault=True,tail_uses_counter_cap_not_nominal_E=True)


def masked_first_sweep_cases():
    cases = 0
    for keys, delay in product((1,3,17,64),(0,1,2)):
        lifetime = 2*(keys+delay+1)
        records = {key:Receipt(lifetime) for key in range(keys)}
        lane = Lane(128)
        for r in records.values():
            r.raw_corrupt(0,r.cap)
            r.mask()  # The observation gate, not power to the receipt clock.
        for t in range(keys+delay+1):
            for r in records.values(): r.elapse(F(1))
            if t < keys:
                lane.offer(Packet(t,1000+t,0,F(t),t),F(t),F(delay))
            lane.poll(F(t),records)
            require(all(not r.read_compare('le',2000) for r in records.values()),
                    'Preparatory publication leaked through disconnected observation gate')
        for key,r in records.items():
            r.output_connected = True
            require(r.read_compare('eq',1000+key),'First sweep failed to overwrite every actual key')
            require(r.nominal_age(F(keys+delay)) <= lifetime+5,
                    'Masked receipt timer silently stopped aging')
        cases += 1
    return dict(full_table_sweeps=cases,initial_arbitrary_words_overwritten=True,
                masked_clocks_continue=True,raw_caches_not_in_receiver_W=True)


def passive_scan_cases():
    clients, cells, bays, origins, q = 80,32,5,13,6
    intended = [(a*17+3)%101 for a in range(cells)]
    physical = [intended[:] for _ in range(bays)]
    physical[0][19] = (physical[0][19]+1)%101
    physical[3][4] = (physical[3][4]+2)%101
    eligible = [True,True,False,True,True]
    choices = []
    comparisons = head_reads = 0
    for client in range(clients):
        choice = None
        for bay in range(bays):
            passing = True
            for address in range(cells):
                yes = 0
                for origin in range(origins):
                    # Actual passive head, independent of the target program.
                    actual = physical[bay][address] if eligible[bay] else None
                    head_reads += 1
                    if origin < q:
                        a = record(intended[address])  # Arbitrary false source.
                        b = record(intended[address])
                    else:
                        # Honest earlier/later errors may vary, but every client
                        # has continuously published j*=1 after its age wait.
                        unavailable = bay != 1 and (client+origin+address)%11 == 0
                        a = record(None if unavailable else actual)
                        b = record(None)
                    yes += logical_compare(a,b,'eq',intended[address])
                    comparisons += 2
                if yes < q+1:
                    passing = False
                    break
            if passing:
                choice = bay
                break
        choices.append(choice)
    require(choices == [1]*clients,'Concurrent truthful errors split the least matching bay')
    # Freeze changes a cell after old sample; sound raw read was not a frozen read.
    frozen_actual, cached, intended_cell = 9,3,3
    require(cached == intended_cell and frozen_actual != intended_cell,'Pre-freeze countercase missing')
    freeze_cases = 0
    for freeze, age, read in product(range(5),range(1,9),range(25)):
        for sampled in range(read+1):
            if read >= freeze+age and read-sampled <= age:
                require(sampled >= freeze,'Age-wait arithmetic admitted pre-freeze sample')
                freeze_cases += 1
    return dict(participating_clients=clients,physical_bays=bays,cells_per_bay=cells,
                passive_head_reads=head_reads,raw_comparisons=comparisons,all_choices=sorted(set(choices)),
                independently_phased_truthful_errors=True,post_freeze_age_instances=freeze_cases,
                pre_freeze_cache_countercase=dict(old_good_sample=cached,frozen_cell=frozen_actual))


def countercases():
    # All-input replacement is a raw I attack; no derived private state changes.
    honest = [(record(1200),record(None)) for _ in range(13)]
    forged = [(record(400),record(None)) for _ in range(13)]
    refused,htrace = inference(honest,threshold=970)
    authorized,ftrace = inference(forged,threshold=970)
    require(not refused and authorized,'Intact whole-input-write obstruction missing')
    baseline = [(record(400),record(None)) for _ in range(13)]
    _,btrace = inference(baseline,threshold=970)
    require(ftrace == btrace,'Forged inputs changed private execution rather than observations')
    # A target-owned server or a shared remapper supplies those same false raw words.
    server_footprint = set(range(13))
    require(len(server_footprint) == 13,'Common server was counted as one independent slot')
    dup = [(record(400),record(400)) for _ in range(6)]+[(record(1200),record(None)) for _ in range(7)]
    logical = sum(logical_compare(a,b,'le',970) for a,b in dup)
    naive = sum(a.read_compare('le',970)+b.read_compare('le',970) for a,b in dup)
    require(logical == 6 and naive == 12,'Bank duplication obstruction missing')
    paused = record(400,lifetime=64)
    paused.pause()
    paused.elapse(F(10000))
    paused.output_connected = True  # Deliberately missing actual resume writes.
    require(paused.read_compare('le',970),'Frozen-clock bad resume countercase missing')
    oldcache = Cache(F(2))
    oldcache.completed(Packet(0,400,0,F(-100000),0))
    oldcache.remaining = F(2)  # Models illicit repackaging of the same old sample.
    stale = oldcache.emit()
    require(stale.sampled < -99999,'Cache-repackaging failure missing')
    missing = [(record(985),record(None)) for _ in range(6)]+[(record(None),record(None)) for _ in range(7)]
    imprecise,_ = inference(missing)
    require(imprecise == 2000,'Unavailable-as-high did not expose lost precision')
    # Every rejected offered item is real work; queue capacity is not arrival bound.
    raw = Lane(1)
    packet = Packet(0,400,0,F(0),0)
    for _ in range(1000): raw.offer(packet,F(0),F(1))
    require(raw.offers == raw.examinations == 1000 and raw.rejections == 999,'Raw rejection work hidden')
    # A shared queue permits another origin's raw traffic to exclude the honest one.
    shared = Lane(2)
    shared.offer(packet,F(0),F(2)); shared.offer(packet,F(0),F(2))
    admitted = shared.offer(Packet(1,1200,0,F(0),1),F(0),F(2))
    require(not admitted,'Shared FIFO starvation obstruction missing')
    # A code writer can claim any raw head's key; this is not physical binding.
    wrong = Packet(0,400,65535,F(0),1)
    # Single request transmission over a reordered packet lane is not a held level.
    queued_request = [('new',0),('old',1)]
    eventual_word = sorted(queued_request,key=lambda event:event[1])[-1][0]
    require(eventual_word == 'old','One-shot reordered request obstruction missing')
    require(wrong.key != wrong.physical_key,'Wrong-key obstruction missing')
    return dict(whole_input_overwrite=dict(execution_intact=True,affected_slots=13,authorization=authorized,
        same_private_trace_as_low_world=True),shared_target_read_server=dict(affected_slots=13),
        shared_input_remapper=dict(affected_slots=13),duplicate_bank_amplification=dict(logical=logical,naive=naive),
        frozen_clock_after_pause=dict(elapsed_while_off=10000,stale_word_reaccepted=True),
        repackaged_old_cache=dict(sample_age_at_repackaging=100000),
        missing_nominal_data=dict(true_envelope=[985,985],returned=imprecise,precision_lost=True),
        raw_rejection_cost=dict(offered=raw.offers,rejected=raw.rejections,examinations=raw.examinations),
        shared_queue=dict(honest_admitted=admitted),one_shot_request_reordering=dict(eventual=eventual_word),wrong_key=dict(claimed=wrong.key,physical=wrong.physical_key))


def demand_parameters():
    source_slots, per_frame, reply_lifetime = 3200,4,819
    period = ceil(F(source_slots,per_frame))+1
    response = 2+period+1+2+2
    age = 1+2+2+reply_lifetime
    corrupted_cap = (1 << reply_lifetime.bit_length())-1
    local_read_wait = ceil(F(101,100)*(response+1))
    local_freeze_wait = ceil(F(101,100)*(age+1))
    per_cell = local_read_wait+10+1
    raw = 20480+6400
    work = 16*342+4*26+3114+584+256+4*raw
    elapsed = F(20,64)+F(work,262144)
    minimum = F(4*raw,1)/F(262144*101,100)
    require(elapsed < 1 and F(20)/minimum < 64,'Demand frame/egress capacity does not close')
    require(F(reply_lifetime)/F(101,100) > response+1,'First current reply may expire before read')
    require(F(local_freeze_wait)/F(101,100) > age,'Demand freeze wait does not clear old samples')
    require(F(local_read_wait)/F(101,100) >= response+1,'Demand response wait too short')
    require(per_cell == 829 and corrupted_cap == 1023,'Demand geometry interface changed')
    return dict(selected_code_supplier='fixed client-target on-demand passive read',
        source_slots=source_slots,source_visits_per_frame=per_frame,service_period=period,
        response_deadline=response,nominal_receipt_lifetime=reply_lifetime,actual_read_age=age,
        arbitrary_counter_cap=corrupted_cap,local_read_wait=local_read_wait,
        local_freeze_wait=local_freeze_wait,cell_attempt_bound=per_cell,
        target_scan_8192=per_cell*(80*8192+2),code_records_per_receiver=40*26,
        fast_and_code_records_per_receiver_bank=160*643+40*26,
        fast_and_code_records_per_receiver_host=2*(160*643+40*26),
        receiver_banks_per_target=80,client_banks_per_source=80,
        instruction_symbol_bits=192,reply_bits=256,code_cell_64bit_limbs=3,reply_64bit_limbs=4,
        maximum_encoded_8192_reply_bits=(160*8192*(1<<192)-1).bit_length(),
        native_word_rate_is_a_new_capacity_obligation=True,
        raw_admission_allowance=raw,frame_word_work=work,frame_elapsed_upper=elapsed,
        per_branch_record_rate_upper=F(20)/minimum,
        full_source_image_size_proved=False,full_energy_supply_proved=False)


class HeldRequest:
    """Physical held-word lead. The program sees a delayed raw word, not time."""
    def __init__(self, changes, settling=2):
        self.changes = sorted(changes)
        self.settling = settling

    def raw_word_at(self, now):
        word = -1
        for changed,value in self.changes:
            if changed+self.settling <= now:
                word = value
            else:
                break
        return word


def demand_service_cases():
    clients,targets,source_count,cells_per_bay = 80,40,13,16
    slots, key_count, symbol_count = clients*targets,2*80*cells_per_bay,1 << 192
    invalid = (1 << 256)-1
    # Actual passive cells: each body is a finite mutable array. No target read
    # server or expected-image opcode exists in the source's acquisition step.
    intended = [(17*a+3)%symbol_count for a in range(cells_per_bay)]
    physical = [[intended[k%cells_per_bay] for k in range(key_count)] for _ in range(targets)]
    requests = []
    deadlines = []
    for slot in range(slots):
        client,target = divmod(slot,targets)
        changes = []
        for turn in range(3):
            time = 900*turn+(client%7)
            key = cells_per_bay+(client+turn)%cells_per_bay
            changes.append((time,key))
            deadlines.append((slot,time+829,key))
        # Every source services every slot, including a client that keeps sending
        # malformed requests. These slots consume work but cannot add visits.
        if client == 79:
            changes = [(t,-1 if t%2 else key_count+7) for t in range(0,2710,3)]
        requests.append(HeldRequest(changes))
    total_visits = total_admissions = good_checks = malformed = 0
    max_reply_delay = 0
    for origin in range(source_count):
        events = [[] for _ in range(slots)]
        cursor = (origin*137)%slots
        for frame in range(0,2710):
            for _ in range(4):
                slot = cursor
                cursor = (cursor+1)%slots
                key = requests[slot].raw_word_at(frame)
                # The selected head/key is captured at start. New input changes
                # cannot retag this conversion at publication.
                captured_key = key
                client,target = divmod(slot,targets)
                if 0 <= captured_key < key_count:
                    value = physical[target][captured_key]
                    word = captured_key*symbol_count+value
                    physical_key = target*key_count+captured_key
                else:
                    word = invalid
                    physical_key = -1
                    malformed += 1
                # Two quanta publication delay and two raw reply propagation.
                packet = Packet(slot,word,65535,F(frame),physical_key)
                events[slot].append((frame+4,packet))
                total_visits += 1
                total_admissions += 1
        for slot,deadline,key in deadlines:
            client,target = divmod(slot,targets)
            if client == 79:
                continue
            r = Receipt(819,maximum=invalid-1)
            # Incoming I may already contain exactly the misleading desired word.
            r.raw_corrupt(key*symbol_count+0,r.cap)
            last = 0
            for received,packet in events[slot]:
                if received > deadline:
                    break
                r.elapse(F(received-last),F(101,100) if client%2 else F(1))
                r.receive(packet)
                last = received
            r.elapse(F(deadline-last),F(101,100) if client%2 else F(1))
            expected = key*symbol_count+intended[key%cells_per_bay]
            require(r.read_compare('eq',expected),'A nominal honest client missed its current key by deadline')
            require(r.packet.physical_key == target*key_count+key,'Response key was not the actual passive head')
            require(r.nominal_age(F(deadline)) <= 824,'Demand response age exceeds proved bound')
            good_checks += 1
            start = deadline-829
            after = [received for received,packet in events[slot]
                     if start+2 <= packet.sampled and packet.value//symbol_count == key and received <= deadline]
            require(after,'No actually new stabilized-key acquisition before response deadline')
            max_reply_delay = max(max_reply_delay,min(after)-start)
    require(max_reply_delay <= 808,'Fixed-cycle response proof failed')
    require(good_checks == source_count*79*40*3,'All-client check coverage changed')
    # A request may change during conversion. Re-reading its key on emission
    # would misbind the old value; this implementation returns the captured key.
    race = HeldRequest([(0,7),(1,8)],settling=0)
    selected = race.raw_word_at(0)
    captured_value = physical[0][selected]
    emitted = selected*symbol_count+captured_value
    new_wanted = race.raw_word_at(2)
    require(new_wanted == 8 and emitted//symbol_count == 7,'Request race was silently retagged')
    # Reusing the same finite key does not reset a sample's actual age.
    same_key_checks = 0
    for old_sample,freeze,consumed in product(range(8),range(8),range(8,20)):
        if consumed-freeze >= 5 and consumed-old_sample <= 5:
            require(old_sample >= freeze,'Full-age same-key reuse admitted a pre-freeze sample')
            same_key_checks += 1
    # A reversed gap encoding preserves the safe unavailable sentinel.
    gap = Receipt(64,maximum=1000)
    require(not gap.read_compare('le',180),'Unavailable gap passed the reversed test')
    gap.receive(Packet(0,100,0,F(0),0))  # Actual z=.9, encoded1-z=.1.
    require(gap.read_compare('le',180),'Reversed lower-bound guard rejected robust gap')
    return dict(source_banks_checked=source_count,fixed_slots_per_bank=slots,
        actual_passive_visits=total_visits,offered_reply_records=total_admissions,
        malformed_visits_charged=malformed,concurrent_honest_client_checks=good_checks,
        client_hosts_per_target=40,client_banks_per_target=80,targets=40,held_key_changes_per_honest_client=3,
        maximum_new_response_delay=max_reply_delay,request_change_during_conversion_keeps_captured_key=True,
        same_key_freeze_instances=same_key_checks,reverse_gap_sentinel_check=True,
        initial_reply_words_arbitrary=True,slot_count_independent_of_image_length=True)


def producer_adapter_cases():
    preservation_cases = prefix_checks = 0
    for intended, initial, trace in product(product((0,1),repeat=3),
                                          product((0,1),repeat=3),
                                          product(range(7),repeat=3)):
        body = list(initial)
        cursor = 0
        matched_cells = set()
        for event in trace:
            before = body[:]
            if event < 3:
                body[event] = intended[event]  # Actual expected-value write.
            elif event < 6:
                pass  # Attempt to address event-3 physically failed.
            else:
                pass  # No write this transition.
            for address in range(3):
                if before[address] == intended[address]:
                    require(body[address] == intended[address], 'Expected-write law lost an established cell')
            if cursor < 3 and body[cursor] == intended[cursor]:
                matched_cells.add(cursor)
                cursor += 1
            require(all(body[j] == intended[j] for j in range(cursor)), 'Copy prefix failed under expected writes')
            prefix_checks += 1
        preservation_cases += 1
    params = demand_parameters()
    age, life = params['actual_read_age'],params['nominal_receipt_lifetime']
    entry, desired, wrong = F(1),1,0
    first_read = entry+params['response_deadline']
    old = record(None,lifetime=life)
    # This is a genuine pre-entry sample, not arbitrary initial I or a bad source.
    old.receive(Packet(0,desired,65535,F(-1),0))
    old.elapse(first_read)
    fresh_wrong = record(None,lifetime=life)
    fresh_wrong.receive(Packet(0,wrong,0,first_read,0))
    require(first_read-F(-1) <= age and logical_compare(old,fresh_wrong,'eq',desired),
            'Request deadline did not retain the real stale-sibling obstruction')
    false_advance_without_entry_wait = logical_compare(old,fresh_wrong,'eq',desired)
    gate_read = F(ceil(entry+F(params['local_freeze_wait'])/F(101,100)))
    old.elapse(gate_read-first_read)
    fresh_wrong.receive(Packet(0,wrong,0,gate_read,0))
    require(not logical_compare(old,fresh_wrong,'eq',desired), 'Entry age wait failed to remove pre-entry match')
    # Equality may be established before the latest attempt, which can fail.
    held = record(None,lifetime=life)
    held.receive(Packet(0,desired,0,F(100),0))
    held.elapse(gate_read-F(100))
    actual = wrong
    actual = desired  # Earlier actual expected-value write, before the sample.
    latest_attempt_succeeded = False
    if latest_attempt_succeeded:
        actual = desired
    require(held.read_compare('eq',desired) and actual == desired and not latest_attempt_succeeded,
            'Current equality was incorrectly identified with latest-write acknowledgment')
    # Seven honest fresh wrong replies cannot be beaten by six false matches.
    failed_inputs = [(record(desired,lifetime=life),record(desired,lifetime=life)) for _ in range(6)]
    failed_inputs += [(record(wrong,lifetime=life),record(wrong,lifetime=life)) for _ in range(7)]
    failed_actual,failed_cursor,failed_offers = wrong,0,0
    for _ in range(8):
        failed_offers += 1
        physically_connected = False
        if physically_connected:
            failed_actual = desired
        votes = sum(logical_compare(a,b,'eq',desired) for a,b in failed_inputs)
        if votes >= 7:
            failed_cursor += 1
    require(votes == 6 and failed_cursor == 0 and failed_actual == wrong,
            'Failed writes falsely advanced a genuinely wrong cell')
    # Old wrong tail remains possible when the alleged entry cue precedes drain.
    claimed_e, wrong_packet_issued, wrong_packet_applied = F(100),F(98),F(104)
    sampled,received,read = F(103),F(107),F(9259,10)
    late = record(None,lifetime=life)
    late.receive(Packet(0,desired,0,sampled,0))
    late.elapse(read-received)
    require(read > claimed_e+F(params['local_freeze_wait'])/F(101,100), 'Late-tail gate fixture too early')
    require(read-sampled <= age and late.read_compare('eq',desired), 'Late-tail real old witness expired')
    require(wrong_packet_applied-wrong_packet_issued == 6 and sampled < wrong_packet_applied < read,
            'Late wrong packet fixture violates its admitted six-quantum tail')
    # The same past observation cannot survive a later wrong write, alias or swap.
    obstruction_values = {}
    for mechanism in ('late_wrong_writer','logical_address_alias','direct_corruption','body_substitution'):
        body = {'identity':7,'cells':[1,0]}
        actual_at_sample = body['cells'][0]
        observation = record(None,lifetime=life)
        observation.receive(Packet(0,actual_at_sample,0,F(850),0))
        if mechanism == 'late_wrong_writer':
            # A previously compromised writer retains an uncut ordinary lead.
            retained_write = {'address':0,'value':0}
            body['cells'][retained_write['address']] = retained_write['value']
            event = 'retained wrong writer applies an ordinary value'
        elif mechanism == 'logical_address_alias':
            intended = [1,0]
            logical_address = 1
            physical_address = {0:0,1:0}[logical_address]
            body['cells'][physical_address] = intended[logical_address]
            event = 'expected write at logical1 aliases physical0'
        elif mechanism == 'direct_corruption':
            body['cells'][0] = 0  # An explicit exceptional digital overwrite.
            event = 'one fresh direct target-cell overwrite'
        else:
            body = {'identity':8,'cells':[0,0]}
            event = 'bay retains its label but powers substituted body8'
        observation.elapse(F(50))
        actual_now = body['cells'][0]
        require(observation.read_compare('eq',1) and actual_now != 1, 'Missing preservation obstruction')
        obstruction_values[mechanism] = dict(sampled_value=actual_at_sample,current_value=actual_now,
            sampled_body=7,current_body=body['identity'],actual_event=event,
            observation_age=50,ordinary_expected_write_law_holds=False,
            fresh_acquisitions=1 if mechanism == 'direct_corruption' else 0)
    # Whole packed equality rejects a reply for an earlier different cursor key.
    alphabet = 1 << 192
    previous_key,current_key = 7,8
    previous = record(None,lifetime=life)
    previous.maximum = (1 << 256)-2
    previous.receive(Packet(0,previous_key*alphabet+3,0,F(0),previous_key))
    require(not previous.read_compare('eq',current_key*alphabet+3), 'Changed key reused another address match')
    # Parameterized copy bound; one gate per preserved entry, not one per write.
    copy_bounds = []
    for write_delay in (0,2,3,6,17):
        t_mut = max(2,write_delay)+params['service_period']+1+2+2
        local_wait = ceil(F(101,100)*(t_mut+1))
        fused = local_wait+10+1
        unfused = fused+10
        gate_bound = params['local_freeze_wait']+10+1
        require(F(local_wait)/F(101,100) >= t_mut+1, 'Mutable response wait too short')
        copy_bounds.append(dict(write_delay=write_delay,response=t_mut,local_response_wait=local_wait,
            issued_to_read=fused,unfused_cell=unfused,entry_gate=gate_bound,
            unfused_copy_8192=gate_bound+8192*unfused))
    require(copy_bounds[2]['unfused_cell'] == 840 and copy_bounds[3]['unfused_cell'] == 843,
            'Current mutable copy timing changed')
    return dict(expected_write_traces=preservation_cases,prefix_checks=prefix_checks,
        failed_writes_leave_wrong_cursor_blocked=True,failed_write_offers_charged=failed_offers,
        failed_latest_write_can_still_have_current_equality=True,
        no_entry_wait=dict(entry=entry,response_read=first_read,actual_wrong_cell=wrong,
            old_genuine_sample=-1,old_still_valid=True,new_bank_reports_current_wrong=True,
            false_cursor_advance=false_advance_without_entry_wait,receiving_execution_intact=True),
        entry_wait=dict(first_allowed_integer_read=gate_read,pre_entry_match_rejected=True),
        late_pre_entry_tail=dict(claimed_entry=claimed_e,actual_drain=wrong_packet_applied,
            issued=wrong_packet_issued,current_expected_write_applied=101,sampled=sampled,received=received,read=read,
            prescribed_wait_elapsed=True,still_falsely_matches=True,fresh_acquisitions=0),
        other_preservation_obstructions=obstruction_values,changing_key_rejected=True,copy_bounds=copy_bounds)


def requester_bank_and_word_cases():
    # Healthy A/B clients write distinct keys; a host-merged request slot cannot
    # supply both held-key obligations. Neither consumer is execution-faulty.
    a_key,b_key = 5,9
    shared_trace = []
    for cycle in range(6):
        shared_slot = a_key
        shared_slot = b_key
        sampled_key = shared_slot
        shared_trace.append(dict(cycle=cycle,a_matches=sampled_key == a_key,b_matches=sampled_key == b_key))
    require(all(not row['a_matches'] and row['b_matches'] for row in shared_trace),
            'Host-only requester alias counterexample vanished')
    separate = {('host',0):a_key,('host',1):b_key}
    require(separate[('host',0)] == a_key and separate[('host',1)] == b_key,
            'Bank-private request slots do not preserve simultaneous intentions')
    # Serial limb reads from changing complete replies can forge a match.
    limb = 1 << 64
    wanted = 4*limb**3+3*limb**2+2*limb+1
    old = 9*limb**3+9*limb**2+2*limb+1
    new = 4*limb**3+3*limb**2+8*limb+8
    torn = old%(limb**2)+(new//(limb**2))*limb**2
    require(old != wanted and new != wanted and torn == wanted, 'Torn nominal-word obstruction missing')
    # An origin-separated staging buffer does not publish until the complete frame.
    current = old
    stage = [0]*4
    intermediate_matches = []
    for index in range(4):
        stage[index] = (new//(limb**index))%limb
        if index == 3:
            current = sum(word*limb**i for i,word in enumerate(stage))
        intermediate_matches.append(current == wanted)
    require(not any(intermediate_matches),'Partial raw assembly leaked as a complete matching record')
    maximum_symbol = (1 << 192)-1
    maximum_key = 160*8192-1
    encoded = maximum_key*(1 << 192)+maximum_symbol
    require(encoded < (1 << 256)-1 and encoded.bit_length() == 213,'Concrete word ABI does not fit')
    return dict(shared_host_request_slot=dict(trace=shared_trace,all_executions_intact=True),
        corrected_requesters_per_target=80,source_client_target_slots=3200,
        same_origin_bank_votes_still_one=True,
        torn_reply=dict(old_equals_wanted=False,new_equals_wanted=False,torn_equals_wanted=True),
        complete_record_publication=dict(staging_limbs=4,current_limbs=4,partial_matches=intermediate_matches),
        instruction_symbol_bits=192,reply_word_bits=256,maximum_encoded_8192_bits=encoded.bit_length(),
        old_capacity_point_not_inherited=True)


class FunctionalPublisher:
    """One-head microvisits; current/query raw operands I0..5, max data I6.

    W contains only cursor, failure and comparison flags. The ghost sample log
    is checker-only and is never used to compute a publication or permission.
    """
    def __init__(self, degree, pose_words, connectors_a, connectors_b, batch=16, scale=1000):
        require(min(degree,connectors_a,connectors_b,batch,scale) > 0,'Empty functional catalogue/design')
        self.degree,self.pose_words,self.counts,self.batch,self.scale = degree,pose_words,(connectors_a,connectors_b),batch,scale
        self.raw_per_target = pose_words+2*(connectors_a+connectors_b)
        self.raw_steps = degree*self.raw_per_target
        self.public_per_target = pose_words+4
        self.I = [(1<<256)-1]*7
        self.W = dict(cursor=0,failed=False,compare=False)
        self.publications = []
        self.samples = []
        self.current_samples = []
        self.operations = {}

    def op(self,name,count=1):
        self.operations[name] = self.operations.get(name,0)+count

    def decode(self):
        target,local = divmod(self.W['cursor'],self.raw_per_target)
        self.op('decode')
        if local < self.pose_words:
            return target,None,local,None,None
        local -= self.pose_words
        for group in range(4):
            count = self.counts[group%2]
            if local < count:
                return target,group,local,count,3+target*self.public_per_target+self.pose_words+group
            local -= count
        raise RuntimeError('Raw cursor escaped its finite catalogue')

    def step(self,time,reader,interleave_query=True,alias_accumulator=False):
        target,group,connector,count,pubkey = self.decode()
        if group is None:
            raw = reader(target,0,connector,'pose',time)
            self.op('raw_conversion')
            self.op('raw_range_check')
            if raw is not None:
                self.op('offer',2*self.degree)
            self.W['cursor'] = (self.W['cursor']+1)%self.raw_steps
            self.op('cursor_advance')
            return
        side,kind = group%2,group//2
        if connector == 0:
            self.I[6] = 0
            self.W['failed'] = False
            self.current_samples = []
            self.op('aggregate_initialization',2)
        raw = reader(target,side,connector,'load' if kind == 0 else 'isolation',time)
        self.op('raw_conversion')
        bias,error_words = 32,10
        self.I[1] = (1<<256)-1 if raw is None else bias+raw
        self.op('raw_range_check')
        cap = 3000 if kind == 0 else self.scale
        valid = raw is not None and bias-error_words <= self.I[1] <= bias+cap+error_words
        if not valid:
            self.W['failed'] = True
            self.op('failed_flag_store')
        else:
            # Decode valid offset-binary data, then project onto the physical
            # quantity range. Unavailable status was rejected before clipping.
            if self.I[1] < bias:
                self.I[1] = 0
            else:
                self.I[1] -= bias
                if self.I[1] > cap:
                    self.I[1] = cap
            self.op('decode_and_clip',3)
            if kind == 1:
                self.I[1] = self.scale-self.I[1]
                self.op('isolation_reverse')
            # An ordinary comparison followed by a conditional raw I copy.
            self.W['compare'] = self.I[6] < self.I[1]
            self.op('raw_compare')
            if self.W['compare']:
                self.I[6] = self.I[1]
                self.op('raw_copy')
        self.current_samples.append((time,raw))  # Ghost only.
        self.samples.append((target,side,connector,kind,time,raw))
        if connector == count-1:
            value = None if self.W['failed'] else self.I[6]
            self.publications.append(dict(target=target,side=side,kind=kind,key=pubkey,value=value,
                samples=self.current_samples[:],published=time))
            self.op('offer',2*self.degree)
        self.I[5] = (1<<256)-1
        self.op('invalidate_current')
        if interleave_query:
            for location in range(6):
                self.I[location] = 0  # An unrelated code-query conversion/copy.
            self.op('interleaved_query_raw_writes',6)
            if alias_accumulator:
                self.I[6] = 0  # Countermodel: actual scratch locations alias.
        self.W['cursor'] = (self.W['cursor']+1)%self.raw_steps
        self.op('cursor_advance')


def upper_permission(value,margin,limit):
    # value=None is the unavailable record. A negative unsigned threshold is
    # never formed: a margin exceeding the limit yields ordinary zero action.
    return value is not None and 0 <= margin <= limit and value <= limit-margin


def functional_inventory_cases():
    examples = []
    for p in (1,8,11,39,40,41,80,3360):
        degree,pose,batch = 40,678,16
        raw = degree*(pose+4*p)
        public = 3+degree*(pose+4)
        period = ceil(F(raw,batch))+1
        fold = 1+ceil(F(p-1,batch))
        lifetime = ceil(F(101,100)*(period+2+1))
        age = fold+2+2+lifetime
        horizon = age+2+25
        load_available = F(1,5)+F(2,100)+F(horizon,10000) <= 1
        isolation_available = F(2,100)+F(horizon,12000) <= F(1,5)
        examples.append(dict(connectors_per_side=p,raw_maintenance_steps=raw,
            public_keys=public,per_frame_plant_conversions=3,maintenance_batch=batch,
            maintenance_publication_period=period,fold_span=fold,receipt_lifetime=lifetime,
            functional_read_age=age,example_complete_future_horizon=horizon,
            load_positive_margin=load_available,isolation_positive_margin=isolation_available,
            point_is_conditional_on_actual_F1_and_physical_rates=True))
    require(next(x for x in examples if x['connectors_per_side']==40)['isolation_positive_margin'] and not next(x for x in examples if x['connectors_per_side']==41)['isolation_positive_margin'],
            'Functional inventory/latency sensitivity boundary changed')
    require(3+16+4 == 23 and 80*(3+16)+4 == 1524,'Publication work count wrong')
    return dict(examples=examples,public_functional_keys_per_target=4,
        raw_functional_heads_per_target='2*(P_A+P_B)',maximum_conversions_per_frame=23,
        maximum_actual_record_offers_per_frame=1524,per_branch_offers_per_frame=23,
        needed_frame_minimum_for_64_rate=F(23,64),connector_catalogue_is_source_data=True,
        example_connector_names=['SUPPLY_IN','SUPPLY_RETURN','MAINTENANCE_FEED','MAINTENANCE_RETURN','WORLD1','WORLD2','DATA_TX','DATA_RX','RUNTIME_WRITE','ACTIVE_SENSE','SERVICE'])


def functional_fold_cases():
    cases = groups = missing_cases = full_scale_visits = 0
    for degree,pose,pa,pb,batch in product((1,2),(0,3),(1,3),(2,7),(1,3,16)):
        machine = FunctionalPublisher(degree,pose,pa,pb,batch)
        def read(target,side,connector,kind,time):
            if kind == 'pose': return 100
            return 200+17*connector+side if kind == 'load' else 1000-11*connector-side
        for step in range(machine.raw_steps):
            frame,position = divmod(step,batch)
            machine.step(F(frame)+F(position+1,batch+1),read)
        require(len(machine.publications) == 4*degree,'Missing completed functional group')
        for item in machine.publications:
            values = [raw if item['kind'] == 0 else 1000-raw for _,raw in item['samples']]
            require(item['value'] == max(values),'Ordinary fold differs from independent maximum specification')
            count = pa if item['side'] == 0 else pb
            span = 1+ceil(F(count-1,batch))
            require(item['published']-item['samples'][0][0] <= span,'Oldest-member span violated')
            groups += 1
        cases += 1
    # Every missing head position, including the first and last, stays fatal to
    # that group even when later readings are small and queries reuse I0..5.
    for missing_at in range(17):
        machine = FunctionalPublisher(1,0,17,17,16)
        def read(target,side,connector,kind,time):
            if side == 0 and kind == 'load' and connector == missing_at: return None
            return 200 if kind == 'load' else 1000
        for step in range(machine.raw_steps): machine.step(F(step,16),read)
        load_a = next(p for p in machine.publications if p['key'] == 3)
        require(load_a['value'] is None and not upper_permission(load_a['value'],20,1000),
                'Missing required head was treated as harmless')
        require(machine.operations['raw_conversion'] == 68,'Missing head caused unbounded retry or skipped work')
        missing_cases += 1
    # One full current-size pose inventory, with a nontrivial asymmetric physical
    # connector catalogue; compile-time counts are tested separately above.
    full = FunctionalPublisher(40,678,11,11,16)
    def full_read(target,side,connector,kind,time):
        if kind == 'pose': return (target+connector)%1000 if connector < 336 else connector%2
        return 200+connector%31 if kind == 'load' else 1000-connector%17
    for step in range(full.raw_steps): full.step(F(step,16),full_read)
    require(len(full.publications) == 160,'Full layout did not emit every side/kind aggregate')
    full_scale_visits = full.operations['raw_conversion']
    return dict(small_decoding_cases=cases,groups_checked=groups,each_missing_head=missing_cases,
        full_scale_raw_visits=full_scale_visits,full_scale_groups=len(full.publications),
        full_scale_operation_vector=full.operations,separate_query_scratch_preserves_partial_max=True)


def functional_future_cases():
    checks = 0
    for count,age,horizon in product((1,2,3,7),(0,1,4,9),(0,1,5)):
        sample_times = [-F(age*i,max(1,count-1)) for i in range(count)]
        for noise_sign in (-1,0,1):
            rates = [F(1+i%3,100) for i in range(count)]
            truths_at_zero = [F(1,5)+F(i%4,10) for i in range(count)]
            samples = [truths_at_zero[i]+rates[i]*sample_times[i] for i in range(count)]
            if min(samples) < 0: continue
            # Rounding down is included in epsilon=11/1000, not erased.
            words = [int((x+noise_sign*F(1,100))*1000) for x in samples]
            words = [max(0,y) for y in words]
            output = max(words)
            epsilon = F(11,1000)
            beta = epsilon+max(rates)*(age+horizon)
            margin = ceil(1000*beta)
            future = [truths_at_zero[i]+rates[i]*horizon for i in range(count)]
            require(all(x <= F(output+margin,1000) for x in future), 'Staggered future envelope fails')
            if upper_permission(output,margin,1000):
                require(all(x <= 1 for x in future), 'Passing aggregate violates a connector load limit')
            checks += 1
    # Lower isolation is handled by the same upper theorem on1-z.
    deficit_words = [0,30,50]
    beta = F(1,100)+F(2,100)
    require(upper_permission(max(deficit_words),ceil(1000*beta),200), 'Robust insulation fixture unavailable')
    require(1-F(max(deficit_words),1000)-beta >= F(4,5), 'Reversed functional-isolation guard wrong')
    return dict(heterogeneous_staggered_future_instances=checks,quantization_in_error=True,
        functional_isolation_uses_deficit=True)


def functional_countercases():
    # Every pose is correct; the independently measured functionality differs.
    cases = {}
    for failure in ('failed_attenuation','failed_insulation'):
        machine = FunctionalPublisher(1,0,2,2,16)
        loads = [1200,200] if failure == 'failed_attenuation' else [200,200]
        isolation = [600,1000] if failure == 'failed_insulation' else [1000,1000]
        def read(target,side,connector,kind,time):
            return loads[connector] if kind == 'load' else isolation[connector]
        for step in range(machine.raw_steps): machine.step(F(step,16),read)
        load = next(p['value'] for p in machine.publications if p['key'] == 3)
        deficit = next(p['value'] for p in machine.publications if p['key'] == 5)
        functional = upper_permission(load,20,1000) and upper_permission(deficit,20,200)
        position_only = 0+50 <= 400 and 0+50 <= 200  # b=z_pose=1.
        require(position_only and not functional,'Correct motion hid failed actual functionality')
        cases[failure] = dict(correct_shunt_and_sleeve_pose=True,position_guard=position_only,
            actual_loads=loads,actual_isolation=isolation,computed_load=load,computed_deficit=deficit,
            functional_guard=functional)
    named_failures = 0
    for failed_connector in range(11):
        for failed_kind in ('load','isolation'):
            machine = FunctionalPublisher(1,0,11,11,16)
            def named_read(target,side,connector,kind,time):
                if side == 0 and connector == failed_connector and kind == failed_kind:
                    return 1200 if kind == 'load' else 600
                return 200 if kind == 'load' else 1000
            for step in range(machine.raw_steps): machine.step(F(step,16),named_read)
            a_load = next(p['value'] for p in machine.publications if p['key'] == 3)
            a_deficit = next(p['value'] for p in machine.publications if p['key'] == 5)
            b_load = next(p['value'] for p in machine.publications if p['key'] == 4)
            b_deficit = next(p['value'] for p in machine.publications if p['key'] == 6)
            require(not (upper_permission(a_load,20,1000) and upper_permission(a_deficit,20,200)),
                    'A named actual cut connector was omitted from functional protection')
            require(upper_permission(b_load,20,1000) and upper_permission(b_deficit,20,200),
                    'Failure on sideA was silently relabeled as sideB evidence')
            named_failures += 1
    # Two connectors swap the high role with an overlap. True max stays1200 at
    # every point, but p0 is read low at0 and p1 low at2.
    samples = [200,200]
    true_states = [[200,1200],[1200,1200],[1200,200]]
    require(all(max(x) == 1200 for x in true_states),'Scalar-max-rate fixture not constant')
    folded = max(samples)
    naive = upper_permission(folded,0,1000)
    correct = upper_permission(folded,2000,1000)  # per-connector rate1 over2q.
    require(naive and not correct,'Last-sample/scalar-max-rate flaw missing')
    # Missing catalogue member: every acquired value is truthful, but not every
    # physically cut connector is covered.
    actual = [200,1200]
    incomplete = [0]
    require(upper_permission(max(actual[p] for p in incomplete),0,1000) and max(actual)>1000,
            'Catalogue coverage counterexample missing')
    # Query-scratch alias destroys a partial max without a new observation.
    good = FunctionalPublisher(1,0,2,2,16)
    bad = FunctionalPublisher(1,0,2,2,16)
    def read(target,side,connector,kind,time):
        return (1200 if connector == 0 else 200) if kind == 'load' else 1000
    for step in range(good.raw_steps):
        good.step(F(step),read)
        bad.step(F(step),read,alias_accumulator=True)
    good_word = good.publications[0]['value']; bad_word = bad.publications[0]['value']
    require(good_word == 1200 and bad_word == 200,'I accumulator/query alias did not change the answer')
    # A nominal streaming head cannot update between compare and copy unless
    # its raw word has first been captured. Otherwise even the old max can fall.
    previous_max,compared_raw,copied_raw = 800,1200,100
    copied_without_hold = copied_raw if previous_max < compared_raw else previous_max
    require(copied_without_hold < previous_max,'Unlatched compare/copy counterexample missing')
    # A raw I accumulator overwrite remains input-only; six false source records
    # cannot meet the seven-vote threshold, and thirteen aliases can.
    normal_word = 1200
    words = [0]*6+[normal_word]*7
    require(sum(upper_permission(y,0,1000) for y in words) == 6,'Bad-source budget was bypassed')
    all_alias = [0]*13
    require(sum(upper_permission(y,0,1000) for y in all_alias) == 13,'Shared target report obstruction missing')
    # Whole-primary forgery remains action-relevant with twelve fixed auxiliaries.
    auxiliary = [970]*6+[990]*6
    require(sum(y<=970 for y in [970]+auxiliary)==7 and sum(y<=970 for y in [990]+auxiliary)==6,
            'Functional aggregate made primary information decorative')
    # Unsigned margin subtraction is not a safe saturating rule.
    limit,margin = 200,201
    wrapped = (limit-margin)%(1<<256)
    require(100 <= wrapped and not upper_permission(100,margin,limit),'Margin-underflow obstruction missing')
    # Each frame has duration1; positions inside frames can still differ.
    frame_bound,old_sample,new_sample = F(1),F(1,10),F(19,10)
    require(new_sample-old_sample > frame_bound and new_sample-old_sample <= 2*frame_bound,
            'Partial-frame service distinction missing')
    return dict(failed_components=cases,every_declared_connector_and_failure_kind=named_failures,
        staggered_no_snapshot=dict(sampled_words=samples,actual_snapshot_maxima=[1200,1200,1200],
            source_result=folded,naive_last_sample_or_scalar_rate_guard=naive,per_connector_age_guard=correct),
        omitted_connector=dict(actual=actual,catalogue=incomplete,false_permission=True),
        raw_scratch_alias=dict(correct=good_word,aliased=bad_word,receiving_execution_intact=True),
        unlatched_compare_copy=dict(previous=previous_max,compared=compared_raw,copied=copied_raw,result=copied_without_hold),
        raw_accumulator_input_fault=dict(false_origins=6,passing_votes=6,execution_intact=True),
        shared_target_report=dict(apparent_origins=13,actual_common_dependency=1,affected_slots=13),
        primary_forgery_changes_guard=True,unsigned_margin_wrap_rejected=True,
        partial_frame_counterexample=dict(frame_bound=frame_bound,old_sample=old_sample,new_sample=new_sample,
            actual_gap=new_sample-old_sample))


def functional_clipping_cases():
    cases = 0
    for true,noise in product((0,1,200,600,990,999,1000),range(-10,11)):
        raw = true+noise
        machine = FunctionalPublisher(1,0,1,1)
        def read(target,side,connector,kind,time): return 200 if kind == 'load' else raw
        for step in range(machine.raw_steps): machine.step(F(step),read)
        deficit = next(x['value'] for x in machine.publications if x['key'] == 5)
        require(deficit is not None,'A valid nominal endpoint error was rejected')
        clipped = 1000-deficit
        require(abs(clipped-true) <= abs(noise),'Ordinary clipping enlarged raw error')
        if true == 1000:
            require(upper_permission(deficit,20,200),'Full isolation lost availability at an allowed noise sign')
        if true == 600:
            require(not upper_permission(deficit,20,200),'Clipping concealed failed insulation')
        cases += 1
    safest_cases = 0
    for load_error,isolation_error in product(range(-10,11),repeat=2):
        machine = FunctionalPublisher(1,0,11,11)
        def safest_read(target,side,connector,kind,time):
            return load_error if kind == 'load' else 1000+isolation_error
        for step in range(machine.raw_steps): machine.step(F(step),safest_read)
        load = next(x['value'] for x in machine.publications if x['key'] == 3)
        deficit = next(x['value'] for x in machine.publications if x['key'] == 5)
        require(upper_permission(load,20,1000) and upper_permission(deficit,20,200),
                'Allowed signed noise made every healthy safest-state source abstain')
        safest_cases += 1
    for invalid in (None,-11,1011):
        machine = FunctionalPublisher(1,0,1,1)
        def read(target,side,connector,kind,time): return 200 if kind == 'load' else invalid
        for step in range(machine.raw_steps): machine.step(F(step),read)
        deficit = next(x['value'] for x in machine.publications if x['key'] == 5)
        require(deficit is None and not upper_permission(deficit,20,200),
                'Invalid status/data was clipped into permission')
    return dict(valid_noise_endpoint_cases=cases,safest_load0_isolation1_error_pairs=safest_cases,
        invalid_band_cases=3,bias=32,
        numeric_error_words=10,valid_isolation_encoded_band=[22,1042],
        unavailable_is_separate=True,failed_insulation_still_rejected=True)


class LimbAssembler:
    """Fixed bounded pre-parser circuit. No completion is needed to incur work."""
    def __init__(self):
        self.stage = [0]*4
        self.expected = 0
        self.partial_left = F(0)
        self.record = Receipt(64,maximum=(1<<256)-2)
        self.offers = self.commits = self.resets = self.drops = self.work = 0
        self.now = F(0)

    def elapse(self,now):
        delta = now-self.now
        require(delta >= 0,'Raw circuit time moved backward')
        self.record.elapse(delta)
        if self.expected:
            self.partial_left = max(F(0),self.partial_left-delta)
            self.work += 1
            if self.partial_left == 0:
                self.expected = 0
                self.resets += 1
                self.work += 1
        self.now = now

    def offer(self,kind,ordinal,payload):
        self.offers += 1
        self.work += 3  # admission, bounded tag/ordinal decode, payload range.
        valid_word = 0 <= payload < 1<<64
        if kind == 'start' and ordinal == 0 and valid_word:
            if self.expected: self.resets += 1
            self.stage[0] = payload
            self.expected = 1
            self.partial_left = F(2)
            self.work += 3
            return None
        if kind in ('data','end') and valid_word and ordinal == self.expected and self.expected > 0:
            if (ordinal == 3) != (kind == 'end'):
                self.expected = 0;self.drops += 1;self.resets += 1;self.work += 2
                return None
            self.stage[ordinal] = payload
            self.work += 2
            if ordinal == 3:
                word = sum(value << (64*i) for i,value in enumerate(self.stage))
                # Complete coherent publication, not a partial-buffer commit.
                self.record.receive(Packet(0,word,0,self.now,0))
                self.commits += 1
                self.expected = 0
                self.work += 3
                return word
            self.expected += 1
            return None
        self.expected = 0
        self.drops += 1
        self.resets += 1
        self.work += 2
        return None


def raw_ingress_cases():
    malformed = LimbAssembler()
    malformed.record.receive(Packet(0,400,0,F(0),0))
    for index in range(10000):
        malformed.elapse(F(index,128))
        malformed.offer('start',0,index)
    require(malformed.commits == 0 and malformed.offers == 10000 and malformed.resets >= 9999,
            'Partial starts escaped raw admission/reset accounting')
    require(not malformed.record.read_compare('le',1000),'Partial traffic refreshed an old observation')
    require(malformed.work >= 10000,'Malformed input examination was free')
    # Exhaust every four-symbol pattern over valid and malformed control events.
    symbols = [('start',0,1),('data',1,2),('data',2,3),('end',3,4),('reset',0,0),('data',3,5)]
    patterns = commits = 0
    for trace in product(symbols,repeat=4):
        machine = LimbAssembler()
        actual = []
        for index,symbol in enumerate(trace):
            machine.elapse(F(index,1024))
            result = machine.offer(*symbol)
            if result is not None: actual.append(result)
        expected = [1+(2<<64)+(3<<128)+(4<<192)] if tuple(trace) == tuple(symbols[:4]) else []
        require(actual == expected,'Malformed or partial frame committed a word')
        require(machine.work <= 12*4+2*4,'Pre-parser body exceeded constant per-symbol work')
        patterns += 1; commits += len(actual)
    # An independent bounded sampler does not examine every driver toggle.
    sender_attempts = 10000
    accepted_toggles = rejected = 0
    next_allowed = F(0)
    transitions = []
    for index in range(sender_attempts):
        time = F(index,5000)
        if time >= next_allowed:
            transitions.append((time,index))
            accepted_toggles += 1
            next_allowed = time+F(1,64)
        else:
            rejected += 1
    receiver_samples = 0
    observed = []
    for time in (F(0),F(1),F(2)):
        level = next((value for at,value in reversed(transitions) if at <= time),0)
        observed.append(level)
        receiver_samples += 1
    require(sender_attempts > accepted_toggles > receiver_samples and rejected > 0,
            'Sender attempts were confused with receiver sampling')
    require(accepted_toggles <= 1+64*2,'Physical driver accepted unbounded toggles')
    # Once a nominal write actually holds at3, a1q propagation plus arbitrary
    # bounded-rate sampling phase reaches it by5 without a successful RPC flag.
    stable_checks = 0
    transitions.append((F(3),777))
    for phase in (F(0),F(1,4),F(99,100)):
        samples = []
        for tick in range(7):
            now = phase+tick
            level = next((value for at,value in reversed(transitions) if at+1 <= now),0)
            samples.append((now,level))
        require(any(4 <= now <= 5 and value == 777 for now,value in samples),
                'Held request stabilization exceeds propagation plus sampling bound')
        stable_checks += 1
    # Physical circuit point: every raw symbol, not just complete packets.
    symbol_bound = 160*(4+1040)
    raw_delay = F(129,256)+F(1,4)+F(513,2048)
    require(raw_delay == F(2057,2048) and raw_delay < 2,'Raw queue/assembly delay does not close')
    return dict(partial_offers=malformed.offers,partial_commits=malformed.commits,
        partial_resets=malformed.resets,partial_work=malformed.work,old_receipt_expired=True,
        exhaustive_four_symbol_patterns=patterns,committing_patterns=commits,
        raw_symbol_width_max_bits=96,symbol_burst=4,symbol_rate=1040,
        symbols_per_receiver_bank_unit_interval=symbol_bound,raw_delay=raw_delay,
        separate_sender_attempts=sender_attempts,accepted_driver_toggles=accepted_toggles,
        rejected_sender_attempts=rejected,receiver_samples=receiver_samples,
        held_request_phase_checks=stable_checks,
        line_and_timer_power_is_separate=True,helper_output_offers_not_in_publisher_total=True)


def acquisition_storage_cases():
    record_cases = []
    for lifetime in (6,819,1828,(1<<64)-1):
        width = lifetime.bit_length()
        cap = (1<<width)-1
        fields = dict(data_buffers=512,raw_operand_latch=256,receipt_counters=2*width,
                      local_key_descriptor=64,selector_validity_commit_status=16)
        bits = sum(fields.values())
        require(width <= 64 and bits <= 1024 and lifetime <= cap,'Record allocation/width mismatch')
        record_cases.append(dict(nominal_lifetime=lifetime,effective_counter_bits=width,
            arbitrary_counter_cap=cap,fields=fields,field_total_bits=bits,allocation_bits=1024))
    branch = dict(tx_fifo=128*384,rx_symbol_fifo=512*128,serializer=384,partial_assembly=512,control=128)
    require(sum(branch.values()) == 115712,'Branch storage bill changed')
    public_keys = 3+40*(678+4)
    consumed = 26*(public_keys+40)
    dense = 160*public_keys+26*40
    require(public_keys == 27283 and consumed == 710398 and dense == 4366320,'Record inventory wrong')
    return dict(record_layout_cases=record_cases,parent_record_bits_2048_is_conservative=True,
        branch_fields=branch,branch_bits=sum(branch.values()),raw_wire_bits_per_symbol=96,
        raw_wire_bits_per_four_limb_frame=384,held_request_receiver_bits=1024,
        held_request_sender_bits=512,source_raw_scratch_bits=4096,
        consumed_records_per_receiver_bank=consumed,dense_records_per_receiver_bank=dense,
        shared_arrays_need_actual_mapping=True,command_word_bits_per_bank_target=64,
        world_word_pair_bits=128,physical_timer_and_line_power_is_additional=True)


def digest(path):
    return hashlib.sha256(path.read_bytes().replace(b'\r\n',b'\n')).hexdigest()


def check_lean(lean):
    checker_path = HERE.parent/'integration/verify.py'
    spec = importlib.util.spec_from_file_location('acquisition_strict_checker',checker_path)
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    version = subprocess.run([str(lean),'--version'],capture_output=True,text=True,encoding='utf-8')
    require(version.returncode == 0 and 'version 4.33.0,' in version.stdout,'Lean4.33.0 required')
    return dict(version=version.stdout.strip(),declarations=checker.proof_check(HERE/'Acquisition.lean',str(lean)),
                checker_sha256_lf=digest(checker_path))


def main():
    require(not sys.flags.optimize and sys.version_info[:2] == (3,12),'Unoptimized Python3.12 required')
    sys.dont_write_bytecode = True
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write',action='store_true')
    mode.add_argument('--check',action='store_true')
    parser.add_argument('--lean',type=Path,default=LEAN)
    args = parser.parse_args()
    names = ('ACQUISITION.md','Acquisition.lean','acquisition_model.py')
    before = {name:digest(HERE/name) for name in names}
    path = HERE/'acquisition_results.json'
    expected = json.loads(path.read_text(encoding='utf-8')) if args.check else None
    if expected:
        require(expected['sources_sha256_lf'] == before,'Acquisition sources changed; inspect before refresh')
    actual = dict(schema='local-acquisition-v1',component_checks_passed=True,
        scope='Periodic physical-origin acquisition component; no source admission or global renewal theorem',
        sources_sha256_lf=before,python_major_minor=list(sys.version_info[:2]),parameters=parameter_checks(),demand_parameters=demand_parameters(),demand_service=demand_service_cases(),
        producer_adapter=producer_adapter_cases(),requester_banks_and_words=requester_bank_and_word_cases(),
        functional_inventory=functional_inventory_cases(),functional_folds=functional_fold_cases(),
        functional_future=functional_future_cases(),functional_countercases=functional_countercases(),
        functional_clipping=functional_clipping_cases(),raw_ingress=raw_ingress_cases(),
        storage=acquisition_storage_cases(),
        age=cache_and_age_cases(),publication=cyclic_publication_cases(),overlap=overlap_cases(),
        logical_votes=logical_vote_cases(),old_tail_and_reuse=old_tail_and_reuse_cases(),
        masked_entry=masked_first_sweep_cases(),passive_scan=passive_scan_cases(),countercases=countercases(),lean=check_lean(args.lean))
    actual = serial(actual)
    require(before == {name:digest(HERE/name) for name in names},'Sources changed during verification')
    if args.write:
        path.write_text(json.dumps(actual,indent=2,sort_keys=True)+'\n',encoding='utf-8',newline='\n')
    else:
        require(actual == expected,'Acquisition evidence differs')
    print('PASS acquisition component: '+str(len(actual['lean']['declarations']))+' Lean declarations; '+
          str(actual['publication']['live_key_reads'])+' live keyed reads; '+
          str(actual['overlap']['pair_windows'])+' overlap windows; source admission remains open')


if __name__ == '__main__':
    main()

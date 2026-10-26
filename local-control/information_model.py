"""Finite information kernels and source-bound first-pass evidence.

The checker owns only information_results.json. Runtime state is finite;
physical time/provenance are checker ghosts, never freshness inputs.
"""
from collections import deque
from dataclasses import dataclass, replace
from fractions import Fraction as F
from itertools import combinations, product
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import os
import subprocess
import sys

HERE = Path(__file__).resolve().parent
LEAN = Path(os.environ['USERPROFILE']) / '.elan/toolchains/leanprover--lean4---v4.33.0/bin/lean.exe'
KEYS = ((0, 0), (0, 1), (1, 0), (1, 1))


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


@dataclass(frozen=True)
class Sample:
    key: tuple
    value: int
    sampled: int  # Ghost only: no algorithm reads this field.


@dataclass(frozen=True)
class Record:
    kind: str
    key: tuple = (0, 0)
    token: int = 0
    value: int = 0
    witness: object = None  # Ghost provenance, not on the wire.

    def wire(self):
        return self.kind, self.key, self.token, self.value

    def syntax(self):
        return (self.kind in ('CLEAR', 'QUERY', 'DATA') and self.key in KEYS
                and self.token in (0, 1) and 0 <= self.value <= 2000)


@dataclass
class Cache:
    sample: Sample
    remaining: int


@dataclass
class Pending:
    sample: Sample
    remaining: int
    discard: bool = False


class Source:
    """One physical conversion at a time, hard nonrefreshing finite cache.

    'now' is used solely to annotate the actual acquisition for the checker.
    The two legacy switches intentionally violate the declared kernel.
    """
    def __init__(self, lifetime=16, conversion=2, indefinite=False, refresh=False):
        require(lifetime > 0 and conversion > 0, 'Positive finite source durations required')
        self.lifetime, self.conversion = lifetime, conversion
        self.cache, self.pending = None, None
        self.indefinite, self.refresh = indefinite, refresh
        self.samples = self.emissions = self.clear_writes = 0  # Checker work counters.

    def pause(self, invalidate=True):
        if invalidate:
            self.cache = None
            if self.pending:
                self.pending.discard = True
            self.clear_writes += 1

    def tick(self, now, request, physical):
        if self.cache and not self.indefinite:
            self.cache.remaining = max(0, self.cache.remaining-1)
            if self.cache.remaining == 0:
                self.cache = None
        if self.pending:
            self.pending.remaining -= 1
            if self.pending.remaining == 0:
                if not self.pending.discard:
                    self.cache = Cache(self.pending.sample, self.lifetime)
                self.pending = None
        if request is None or not request.syntax():
            return None
        if request.kind == 'CLEAR':
            self.cache = None
            if self.pending:
                self.pending.discard = True
            self.clear_writes += 1
            return None
        if request.kind != 'QUERY':
            return None
        if self.cache and self.cache.sample.key == request.key:
            if self.refresh:
                self.cache.remaining = self.lifetime  # Deliberately bad variant.
            self.emissions += 1
            sample = self.cache.sample
            return Record('DATA', sample.key, request.token, sample.value, sample)
        if self.pending is None:
            require(request.key in physical and 0 <= physical[request.key] <= 2000,
                    'Primitive physical observation outside the declared bounded domain')
            self.pending = Pending(Sample(request.key, physical[request.key], now), self.conversion)
            self.samples += 1
        return None


@dataclass
class Vote:
    record: Record
    remaining: int


class Votes:
    """One cell per actual ingress. Claimed path/source IDs are not inputs."""
    def __init__(self, paths, threshold, lifetime, kinds, expected_key=None):
        require(0 < threshold <= paths and lifetime > 0, 'Invalid finite vote parameters')
        self.paths, self.threshold, self.lifetime = paths, threshold, lifetime
        self.kinds, self.expected_key = kinds, expected_key
        self.cells = [None] * paths
        self.parsed = self.rejected = 0  # Checker work counters.
        self.examined = self.slot_visits = self.group_visits = 0
        self.work_units = self.max_tick_work = self.max_batch = 0

    def clear(self):
        self.cells = [None] * self.paths

    def tick(self, arrivals):
        examined = 0
        for i, cell in enumerate(self.cells):
            self.slot_visits += 1
            if cell:
                cell.remaining = max(0, cell.remaining-1)
                if not cell.remaining:
                    self.cells[i] = None
        seen = set()
        for actual_port, record in arrivals:
            # Every offered record is examined and charged, including duplicates.
            # Only one record per lane receives payload parsing/slot replacement.
            examined += 1
            if actual_port in seen or not 0 <= actual_port < self.paths:
                self.rejected += 1
                continue
            seen.add(actual_port)
            self.parsed += 1
            if (not record.syntax() or record.kind not in self.kinds
                    or self.expected_key is not None and record.key != self.expected_key):
                self.rejected += 1
                continue
            self.cells[actual_port] = Vote(record, self.lifetime)
        groups = {}
        for i, cell in enumerate(self.cells):
            self.slot_visits += 1
            if cell:
                groups.setdefault(cell.record.wire(), []).append((i, cell.record))
        group_visits, result = 0, None
        for support in groups.values():
            group_visits += 1
            if len(support) >= self.threshold:
                result = support
                break
        self.examined += examined
        self.group_visits += group_visits
        # Bounded-word loop/record work units, not Python instruction counts.
        work = 2*self.paths + examined + group_visits
        self.work_units += work
        self.max_tick_work = max(self.max_tick_work,work)
        self.max_batch = max(self.max_batch,examined)
        return result

    def work_record(self):
        return {'arrivals_examined':self.examined,'payload_parse_attempts':self.parsed,
                'rejections':self.rejected,'slot_visits':self.slot_visits,
                'group_visits':self.group_visits,'charged_work_units':self.work_units,
                'maximum_arrival_batch':self.max_batch,'maximum_tick_work_units':self.max_tick_work}


class Receiver:
    def __init__(self, paths=5, b=2, lifetime=12, use_lifetime=3, key=(0, 0)):
        self.votes = Votes(paths, b+1, lifetime, ('DATA',), key)
        self.use_lifetime = use_lifetime
        self.result = None

    def pause(self, invalidate=True):
        if invalidate:
            self.votes.clear()
            self.result = None

    def tick(self, arrivals):
        if self.result:
            value, remaining, witnesses = self.result
            self.result = (value, remaining-1, witnesses) if remaining > 1 else None
        support = self.votes.tick(arrivals)
        if support:
            self.result = (support[0][1].value, self.use_lifetime, support)
        return self.result


@dataclass
class InFlight:
    record: Record
    claimed_path: int
    remaining: int
    emitted: int  # Ghost only.


class Paths:
    """Independent finite physical lanes with h forward-once FIFO stages.

    Each stage's actual predecessor is fixed by its queue. A forged route
    label cannot acquire another lane's terminal slot. Shared mux failure
    is a separate explicit countercase, not excluded by the label parser.
    """
    def __init__(self, count=5, hops=2, capacity=3, delay=1):
        require(min(count,hops,capacity,delay) > 0, 'Positive finite path parameters required')
        self.count, self.hops, self.capacity, self.delay = count, hops, capacity, delay
        self.queues = [[deque() for _ in range(hops)] for _ in range(count)]
        self.forwarded = self.dropped = self.wrong_predecessor = 0  # Checker work counters.
        self.injection_attempts = self.hop_polls = self.frame_visits = 0
        self.max_tick_work = self.max_delivered_batch = 0

    def inject(self, actual_lane, record, now, claimed_path=None):
        # Admission/drop handling is work even if the queue is already full.
        self.injection_attempts += 1
        if claimed_path is None:
            claimed_path = actual_lane
        queue = self.queues[actual_lane][0]
        if len(queue) == self.capacity:
            self.dropped += 1
            return
        queue.append(InFlight(record, claimed_path, self.delay, now))

    def tick(self, now):
        arrivals, frame_visits = [], 0
        for lane in range(self.count):
            # Reverse order prevents a record traversing two hops in one tick.
            for hop in reversed(range(self.hops)):
                self.hop_polls += 1
                queue = self.queues[lane][hop]
                if not queue:
                    continue
                frame_visits += 1
                frame = queue[0]
                frame.remaining -= 1
                if frame.remaining > 0:
                    continue
                queue.popleft()
                if frame.claimed_path != lane:
                    self.wrong_predecessor += 1
                    continue
                self.forwarded += 1
                if hop == self.hops-1:
                    arrivals.append((lane, frame.record, now-frame.emitted))
                elif len(self.queues[lane][hop+1]) < self.capacity:
                    self.queues[lane][hop+1].append(replace(frame, remaining=self.delay))
                else:
                    self.dropped += 1
        self.frame_visits += frame_visits
        self.max_tick_work = max(self.max_tick_work,self.count*self.hops+frame_visits)
        self.max_delivered_batch = max(self.max_delivered_batch,len(arrivals))
        require(len(arrivals) <= self.count,'Forward-once lanes exceeded their output batch bound')
        return arrivals

    def work_record(self):
        return {'injection_attempts':self.injection_attempts,'dropped_records':self.dropped,
                'hop_polls':self.hop_polls,'frame_visits':self.frame_visits,
                'charged_work_units':self.injection_attempts+self.hop_polls+self.frame_visits,
                'maximum_tick_work_units_excluding_admissions':self.max_tick_work,
                'maximum_delivered_batch':self.max_delivered_batch}


def median(values):
    require(len(values) % 2 == 1, 'Odd observation cardinality required')
    return sorted(values)[len(values)//2]


def permitted(load, gap, beta_load, beta_gap):
    return load+beta_load <= 1000 and gap-beta_gap >= 800


def matchings(items):
    if not items:
        yield ()
    else:
        first = items[0]
        for other in items[1:]:
            rest = tuple(x for x in items if x not in (first, other))
            for tail in matchings(rest):
                yield (frozenset((first, other)),) + tail


def observation_checks():
    layouts = list(matchings(tuple(range(1, 9))))
    supports = set()
    for layout in layouts:
        domains = (frozenset((0,)),) + layout
        for n in range(3):
            for chosen in combinations(domains, n):
                supports.add(frozenset().union(*chosen))
    require(len(layouts) == 105 and max(map(len, supports)) == 4, 'Unknown-layout support projection failed')
    require(max(len(s) for s in supports if 0 in s) == 3, 'Primary-plus-relay footprint miscount')
    count = 0
    for bad in sorted(supports, key=lambda x: (len(x), sorted(x))):
        for extremes in product((0, 2000), repeat=len(bad)):
            rows = [490 if i % 2 else 510 for i in range(9)]
            for i, value in zip(sorted(bad), extremes):
                rows[i] = value
            require(490 <= median(rows) <= 510, 'Median escaped genuine interval')
            count += 1
    aux = [800]*4+[1200]*4
    def plausible(rows, x, indices):
        mismatch = frozenset(i for i in indices if rows[i] != x)
        return any(mismatch <= support for support in supports)
    rows = [800]+aux
    require(plausible(rows, 800, range(9)) and not plausible(rows, 1200, range(9)), 'Primary did not disambiguate')
    require(plausible(rows, 800, range(1,9)) and plausible(rows, 1200, range(1,9)), 'Missing-primary comparison invalid')
    near = [970]*4+[990]*4
    before = permitted(median([970]+near), 900, 30, 20)
    forged = permitted(median([990]+near), 900, 30, 20)
    require(before and not forged, 'Consumed primary did not change decision')
    require(permitted(600,900,30,20) and not permitted(1200,900,30,20), 'Nonempty permission region missing')
    # Two separate low-load certificates can omit a simultaneous transfer.
    require(permitted(970,900,30,20) and 970+60 > 1000, 'Missing-jump countercase failed')
    # Each layout carries its own admissible effective sets. Do not merge
    # mutually exclusive layouts into one imagined simultaneous footprint.
    alternative_layouts = ({'d':frozenset((0,1))},{'d':frozenset((2,3))})
    admissible = ((frozenset(),frozenset(('d',))),)*2
    alternatives = [frozenset().union(*(gamma[d] for d in effective))
                    for gamma,window_sets in zip(alternative_layouts,admissible)
                    for effective in window_sets]
    correct_max = max(map(len,alternatives))
    incompatible_union = len(frozenset().union(*alternatives))
    require(correct_max == 2 and incompatible_union == 4,'Layout-indexed maximum was conflated with union')
    return {'unknown_layouts':len(layouts),'distinct_window_supports':len(supports),
            'endpoint_attack_cases':count,'max_affected_slots':4,'max_with_primary':3,
            'without_primary_alternatives':[800,1200],'with_primary_alternatives':[800],
            'layout_indexed_maximum':correct_max,'incompatible_layout_union':incompatible_union,
            'primary_same_auxiliary_decisions':[before,forged],
            'missing_jump_counterexample':{'load_before':970,'unaccounted_transfer':60,'load_after':1030}}


def exhaustive_cache_checks():
    alphabet = (None, Record('CLEAR'), Record('QUERY',(0,0)), Record('QUERY',(1,0)))
    max_age, emissions, traces = 0, 0, 0
    for choices in product(range(4), repeat=8):
        source = Source(lifetime=3, conversion=2)
        for t, choice in enumerate(choices):
            physical = {key: (100*t+key[0]*10+key[1]) for key in KEYS}
            out = source.tick(t, alphabet[choice], physical)
            if out:
                sample = out.witness
                age = t-sample.sampled
                require(sample.key == out.key and sample.value == out.value, 'Cache key/value detached from acquisition')
                require(age <= 5, 'Arbitrary requester extended source cache age')
                emissions += 1
                max_age = max(max_age, age)
        traces += 1
    require(traces == 65536 and emissions > 0, 'Exhaustive cache domain changed')
    return {'traces':traces,'length':8,'input_symbols':4,'emissions':emissions,'maximum_sample_age':max_age,
            'age_bound':5,'scope':'All stated finite input sequences; not physical or infinite-run verification'}


def transport_trace(indefinite=False, requester_egress_bad=False):
    source = Source(indefinite=indefinite)
    outward, inward = Paths(), Paths()
    control = Votes(5,3,12,('CLEAR','QUERY'))
    receiver = Receiver()
    records, max_age, max_residence = [], 0, 0
    deadline = 120
    # The same public tag is reused. At deadline the old sample is stale.
    for t in range(160):
        load = min(600+7*t,1200)
        physical = {(0,0):load,(0,1):900,(1,0):1200,(1,1):900}
        if t == deadline:
            receiver.pause()  # Actual local writes, independent of outgoing CLEAR.
        if t in (0,deadline):
            request = Record('QUERY',(0,0),0)
            for lane in range(5):
                outward.inject(lane,request,t)
        if t == 80 and not requester_egress_bad:
            for lane in range(5):
                outward.inject(lane,Record('CLEAR'),t)
        incoming_requests = outward.tick(t)
        chosen = control.tick([(p,r) for p,r,_ in incoming_requests])
        response = source.tick(t, chosen[0][1] if chosen else None, physical)
        if response:
            for lane in range(5):
                # Two bad incoming paths forge a low value, including fresh labels.
                record = Record('DATA',(0,0),0,0) if lane < 2 else response
                inward.inject(lane,record,t)
        arrivals = inward.tick(t)
        for _,_,residence in arrivals:
            max_residence = max(max_residence,residence)
        result = receiver.tick([(p,r) for p,r,_ in arrivals])
        if t >= deadline and result:
            value,_,support = result
            genuine = [r.witness for p,r in support if p >= 2 and r.witness is not None]
            require(genuine, 'Quorum had no genuine incoming path')
            age = min(t-s.sampled for s in genuine)
            max_age = max(max_age,age)
            if not indefinite:
                require(age <= 43, 'Bounded-actual-age theorem failed in operative paths')
            if not records or records[-1]['value'] != value:
                records.append({'time':t,'value':value,'sample_age':age,'actual_load':load,
                                'detach_guard':permitted(value,900,308,0)})
    require(records, 'Nominal/egress-replay trace delivered no useful response')
    require(max_residence <= 10, 'Nominal pipeline residence exceeded declared bound')
    require(outward.max_tick_work <= 20 and inward.max_tick_work <= 20, 'Lane polling/forward work cap exceeded')
    require(control.max_batch <= 5 and receiver.votes.max_batch <= 5,'Coupled path batch bound missing')
    require(control.max_tick_work <= 20 and receiver.votes.max_tick_work <= 20,'Bounded-batch vote work exceeded')
    return {'requester_egress_bad':requester_egress_bad,'source_indefinite_cache':indefinite,
            'decisions':records,'maximum_accepted_sample_age':max_age,
            'maximum_path_residence':max_residence,'source_samples':source.samples,
            'source_emissions':source.emissions,'outward_work':outward.work_record(),
            'inward_work':inward.work_record(),'control_vote_work':control.work_record(),
            'reply_vote_work':receiver.votes.work_record()}


def pause_and_refresh_countercases():
    query = Record('QUERY',(0,0))
    low = {key:600 for key in KEYS}
    high = {key:1200 for key in KEYS}
    bad, good = Source(), Source()
    for t in range(4):
        bad.tick(t,query,low)
        good.tick(t,query,low)
    bad.pause(invalidate=False)
    good.pause(invalidate=True)
    old = bad.tick(104,query,high)
    fresh = good.tick(104,query,high)
    require(old and old.value == 600 and old.witness.sampled == 0, 'Frozen-source witness not reproduced')
    require(fresh is None, 'Invalidated source used old sample')
    for t in (105,106):
        fresh = good.tick(t,query,high)
    require(fresh and fresh.value == 1200, 'Post-pause source failed useful fresh return')
    refreshed = Source(lifetime=3, refresh=True)
    last = None
    for t in range(20):
        last = refreshed.tick(t,query,low)
    require(last and 19-last.witness.sampled > 5, 'Duplicate-refresh witness not reproduced')
    packet = Record('DATA',(0,0),0,600,Sample((0,0),600,0))
    rb, rg = Receiver(), Receiver()
    for receiver in (rb,rg):
        receiver.tick([(i,packet) for i in range(3)])
    rb.pause(invalidate=False)
    rg.pause(invalidate=True)
    stale_result, no_result = rb.tick([]), rg.tick([])
    require(stale_result and no_result is None, 'Receiver pause distinction lost')
    return {'frozen_source_sample_age':104,'invalidated_source_return_value':fresh.value,
            'duplicate_refresh_sample_age':19-last.witness.sampled,
            'frozen_receiver_retains_old_quorum':True,'frozen_receiver_sample_age_at_resume':104,
            'invalidated_receiver_returns_unknown':True}


def unequal_clock_trace():
    """Different initial offsets and variable positive invocation gaps.

    Timers count local invocations. The proof bound uses the actual upper
    gap, not an inherited alignment or a trustworthy payload timestamp.
    """
    source = Source(lifetime=3,conversion=2)
    receiver = Receiver(paths=3,b=1,lifetime=4,use_lifetime=2)
    future, buffers = [], [deque() for _ in range(3)]
    source_next, receiver_next = 0, 1
    source_calls = receiver_calls = 0
    emitted = accepted = max_age = max_residence = max_queued = 0
    capacity = 4
    # Conversion <=6, source cache <=9, path+input FIFO <=19,
    # vote <=12, decoded use <=6 actual time units.
    bound = 6+9+19+12+6
    for now in range(120):
        if now == source_next:
            physical = {key:min(600+now,2000) for key in KEYS}
            out = source.tick(now,Record('QUERY'),physical)
            if out:
                emitted += 1
                for lane,delay in enumerate((0,1,4)):
                    packet = Record('DATA',value=0) if lane == 0 else out
                    future.append((now+delay,lane,packet,now))
            source_next += (1,3,2)[source_calls % 3]
            source_calls += 1
        due = [event for event in future if event[0] == now]
        future = [event for event in future if event[0] != now]
        for _,lane,packet,sent in due:
            require(len(buffers[lane]) < capacity, 'Unequal-clock trace exceeded actual input capacity')
            buffers[lane].append((packet,sent))
        max_queued = max(max_queued,sum(map(len,buffers))+len(future))
        if now == receiver_next:
            arrivals = []
            for lane,queue in enumerate(buffers):
                if queue:
                    packet,sent = queue.popleft()
                    max_residence = max(max_residence,now-sent)
                    arrivals.append((lane,packet))
            result = receiver.tick(arrivals)
            if result:
                witnesses = [packet.witness for lane,packet in result[2]
                             if lane != 0 and packet.witness is not None]
                require(witnesses, 'Jittered quorum lacks good incoming witness')
                age = min(now-sample.sampled for sample in witnesses)
                require(age <= bound, 'Local countdowns exceeded the actual-time envelope')
                max_age = max(max_age,age)
                accepted += 1
            receiver_next += (2,3,1)[receiver_calls % 3]
            receiver_calls += 1
    require(accepted > 0 and max_residence <= 19, 'Unequal-clock positive trace failed')
    require(receiver.votes.max_batch <= 3 and receiver.votes.max_tick_work <= 12,
            'Jittered finite input queues exceeded the vote-work bound')
    return {'source_initial_offset':0,'receiver_initial_offset':1,
            'source_gaps':[1,3,2],'receiver_gaps':[2,3,1],
            'emitted_batches':emitted,'accepting_invocations':accepted,
            'actual_age_bound':bound,'maximum_sample_age':max_age,
            'maximum_reply_residence':max_residence,'maximum_queued_records':max_queued,
            'reply_vote_work':receiver.votes.work_record(),
            'scope':'One finite unequal-offset/jitter trace; not a clock/renewal supplier theorem'}


def path_and_vote_countercases():
    packet = Record('DATA',(0,0),0,600,Sample((0,0),600,0))
    network = Paths()
    network.inject(0,packet,0,claimed_path=4)
    for t in range(8):
        require(not network.tick(t), 'Claimed path acquired a different physical slot')
    require(network.wrong_predecessor == 1, 'Wrong predecessor was not rejected')
    receiver = Receiver()
    require(receiver.tick([(0,packet)]*1000) is None, 'Duplicate flooding fabricated a quorum')
    require(receiver.votes.parsed == 1 and receiver.votes.examined == 1000
            and receiver.votes.rejected == 999 and receiver.votes.work_units == 1011,
            'Duplicate examination/rejection work was hidden behind the parse count')
    linear_work = []
    for copies in (1,10,100,1000):
        probe = Receiver()
        probe.tick([(0,packet)]*copies)
        require(probe.votes.work_units == copies+11,'Direct API work is not charged per offered record')
        linear_work.append({'offered':copies,'work_units':probe.votes.work_units})
    behind_flood = Receiver()
    forged = Record('DATA',(0,0),0,0)
    result = behind_flood.tick([(0,forged)]*1000+[(p,packet) for p in (2,3,4)])
    require(result and result[0] == 600 and behind_flood.votes.examined == 1003,
            'A bad-lane prefix starved genuine later lanes or escaped accounting')
    # An actually shared mux can reach all actual slots: no path-name proof helps.
    mux = Receiver()
    forged = Record('DATA',(0,0),0,600)
    result = mux.tick([(i,forged) for i in range(5)])
    require(result and all(r.witness is None for _,r in result[2]), 'Shared mux countercase disappeared')
    # Old good-path votes + one current bad path create a false current quorum.
    stale = Receiver()
    stale.tick([(1,packet),(2,packet)])
    result = stale.tick([(0,forged)])
    require(result, 'Retained-vote countercase missing')
    expired = Receiver()
    expired.tick([(1,packet),(2,packet)])
    for _ in range(12):
        expired.tick([])
    require(expired.tick([(0,forged)]) is None, 'Expired good votes were revived by bad duplicate')
    flood = Paths()
    delivered = []
    for t in range(20):
        for _ in range(100):
            flood.inject(0,forged,t)
        if t == 0:
            flood.inject(4,packet,t)
        delivered += flood.tick(t)
    require(any(p == 4 and r.witness for p,r,_ in delivered), 'One-lane flooding starved an independent lane')
    require(flood.max_tick_work <= 20 and flood.dropped > 0, 'Finite flood limits not exercised')
    require(flood.injection_attempts == 2001
            and flood.work_record()['charged_work_units'] >= 2001,
            'Rejected Paths.inject attempts were not charged')
    return {'forged_path_label_rejected':True,'direct_duplicate_batch_work':receiver.votes.work_record(),
            'direct_batch_linear_work':linear_work,'genuine_lanes_after_flood_work':behind_flood.votes.work_record(),
            'shared_mux_can_forge_all_slots':True,'retained_vote_quorum_countercase':True,
            'expiry_blocks_retained_vote_quorum':True,'flood_dropped_records':flood.dropped,
            'independent_lane_delivered_during_flood':True,'flood_path_work':flood.work_record()}


def readback_and_support_countercases():
    stored = [True]*9
    active_max = 0
    for target in range(9):
        active_max = max(active_max,1)
        stored[target] = False  # Release does not restore this retained state.
    require(active_max == 1 and sum(not x for x in stored) == 9, 'Temporal union witness failed')
    image = [1,1]
    read = [image[0]]
    image[0] = 0
    read.append(image[1])
    require(read == [1,1] and image != read, 'Image coherence countercase failed')
    source = Source(conversion=1)
    physical = {(0,0):600,(0,1):900,(1,0):1200,(1,1):900}
    source.tick(0,Record('QUERY',(0,0)),physical)
    source.tick(1,Record('QUERY',(0,0)),physical)
    wrong = source.tick(2,Record('QUERY',(1,0)),physical)
    require(wrong is None, 'Cache was relabeled to a new physical target')
    right = source.tick(3,Record('QUERY',(1,0)),physical)
    require(right and right.key == (1,0) and right.value == 1200, 'New physical-target acquisition missing')
    bits = 0
    for bad_count in range(3):
        for bad in combinations(range(5),bad_count):
            for values in product((0,1),repeat=bad_count):
                rows = [1]*5
                for i,v in zip(bad,values): rows[i] = v
                require(median(rows) == 1, 'Stable-bit majority failed')
                bits += 1
    return {'maximum_current_intruders':active_max,'retained_bad_slots':9,
            'sequential_image_readback':read,'actual_image_after_readback':image,
            'wrong_bay_cache_relabel_refused':True,'stable_bit_cases':bits,
            'raw_history_example_bound':2*(2+int(F(2)+F(1,100)*(40+10))),
            'raw_history_example_conditions':'kappa=2,c=2,sigma=2,lambda=.01,H=40,W=10; H/closure are not established here'}


def digest(path):
    return hashlib.sha256(path.read_bytes().replace(b'\r\n',b'\n')).hexdigest()


def check_lean(lean):
    checker_path = HERE.parent/'integration/verify.py'
    spec = importlib.util.spec_from_file_location('local_information_strict_checker',checker_path)
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    process = subprocess.run([str(lean),'--version'],capture_output=True,text=True,encoding='utf-8')
    require(process.returncode == 0 and 'version 4.33.0,' in process.stdout,'Lean4.33.0 required')
    proofs = checker.proof_check(HERE/'Information.lean',str(lean))
    return {'version':process.stdout.strip(),'axiom_dependencies':proofs,
            'checker_sha256_lf':digest(checker_path)}


def main():
    require(not sys.flags.optimize and sys.version_info[:2] == (3,12),'Unoptimized Python3.12 required')
    sys.dont_write_bytecode = True
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--write',action='store_true')
    group.add_argument('--check',action='store_true')
    parser.add_argument('--lean',type=Path,default=LEAN)
    args = parser.parse_args()
    own_inputs = ('INFORMATION.md','Information.lean','information_model.py')
    before = {name:digest(HERE/name) for name in own_inputs}
    record_path = HERE/'information_results.json'
    expected = json.loads(record_path.read_text(encoding='utf-8')) if args.check else None
    if expected:
        require(expected['sources_sha256_lf'] == before,'Component source changed; review before deliberate refresh')
    observations = observation_checks()
    exhaustive = exhaustive_cache_checks()
    nominal = transport_trace()
    repaired = transport_trace(requester_egress_bad=True)
    legacy = transport_trace(indefinite=True,requester_egress_bad=True)
    require(not repaired['decisions'][0]['detach_guard'],'Repaired cache permitted high-load detachment')
    require(legacy['decisions'][0]['detach_guard'],'Missing-CLEAR stale-cache obstruction not exhibited')
    actual = {'schema':'local-control-information-v1','component_checks_passed':True,
              'scope':'Conditional component; selected Lean and finite operative traces, first-pass checking only',
              'python_major_minor':list(sys.version_info[:2]),'sources_sha256_lf':before,
              'observation_support':observations,'cache_exhaustion':exhaustive,
              'nominal_query_cycle':nominal,'damaged_requester_egress_repaired':repaired,
              'damaged_requester_egress_indefinite_cache':legacy,
              'pause_and_refresh':pause_and_refresh_countercases(),
              'unequal_clock_trace':unequal_clock_trace(),
              'path_and_vote':path_and_vote_countercases(),
              'readback_and_window':readback_and_support_countercases(),
              'lean':check_lean(args.lean)}
    require(before == {name:digest(HERE/name) for name in own_inputs},'Inputs changed during checks')
    if args.write:
        record_path.write_text(json.dumps(actual,indent=2,sort_keys=True)+'\n',encoding='utf-8',newline='\n')
    else:
        require(actual == expected,'Component evidence differs')
    print('PASS conditional information kernels: '+str(len(actual['lean']['axiom_dependencies']))+
          ' Lean declarations; '+str(exhaustive['traces'])+' finite cache traces; source suppliers remain open')


if __name__ == '__main__':
    main()

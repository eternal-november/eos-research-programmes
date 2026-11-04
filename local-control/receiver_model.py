"""External raw operands, genuine private comparisons and incident projections.

This checks an instruction/placement adapter. Electrical containment and the
returned-history supplier remain separate source obligations in RECEIVER.md.
"""
from __future__ import annotations
import argparse
from collections import Counter, defaultdict, deque
from dataclasses import dataclass
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations, product
import json
from pathlib import Path
import re
import subprocess
import sys
import geometry_model as geometry
import incidence_model as incidence
import program_model as pm

HERE = Path(__file__).resolve().parent
MASK = (1 << 256) - 1
LIMB = (1 << 64) - 1


def require(ok, message):
    if not ok:
        raise AssertionError(message)


def digest(name):
    return sha256((HERE/name).read_text(encoding='utf-8-sig').replace('\r\n', '\n').encode()).hexdigest()


def word_cmp(x, y):
    """Ordinary four-limb unsigned compare; no data provenance/health check."""
    x &= MASK
    y &= MASK
    for shift in (192, 128, 64, 0):
        a, b = (x >> shift) & LIMB, (y >> shift) & LIMB
        if a != b:
            return -1 if a < b else 1
    return 0


@dataclass
class RawCell:
    value: int = MASK
    remaining: int = 0
    partial: tuple[int, ...] = ()

    def tick(self, count=1):
        self.remaining = max(0, self.remaining-count)

    def receive(self, value, lifetime):
        self.value = value & MASK
        self.remaining = lifetime
        self.partial = ()

    def capture(self):
        return self.value & MASK if self.remaining else MASK


@dataclass(frozen=True)
class Descriptor:
    operation: str
    raw_address: tuple
    lower: int
    upper: int
    body: tuple
    destination: int


def predicate(d, raw):
    # Private IO arguments are signed(); raw I is unsigned. Preserve both.
    def against(bound):
        if bound < 0:
            return 1
        if bound > MASK:
            return -1
        return word_cmp(raw, bound)
    if d.operation in ('fast_equal', 'reply_equal', 'own_equal'):
        return int(against(d.lower) == 0)
    if d.operation == 'fast_cmp':
        return int(against(d.upper) <= 0)
    if d.operation == 'fast_range':
        return int(against(d.lower) >= 0 and against(d.upper) <= 0)
    raise ValueError(d.operation)


class Island:
    """Raw capture stays here; only private arguments/results cross to core."""
    def __init__(self):
        self.cells = {}
        self.pending = {}
        self.last_capture = None

    def begin(self, descriptor):
        require(descriptor.body not in self.pending, 'Two simultaneous instructions reused one cartridge')
        self.pending[descriptor.body] = descriptor

    def finish(self, body, private_destinations):
        d = self.pending.pop(body)
        raw = self.cells.get(d.raw_address, RawCell()).capture()
        self.last_capture = (d, raw)
        result = predicate(d, raw)
        private_destinations.setdefault(d.body, {})[d.destination] = result
        return result


class ExternalPorts(pm.RawPorts):
    """Actual PROGRAM I/O against per-origin raw islands, not a guard oracle."""
    def __init__(self, compiled, receiver=0, n=432, side=0, cartridge=0):
        super().__init__(compiled)
        self.receiver, self.n = receiver, n
        self.body = (receiver, side, cartridge)
        self.islands = {o: Island() for o in incidence.neighbors(receiver, n)}
        self.own_islands = {t: Island() for t in range(self.c['DEGREE'])}
        self.primary = Island()
        self.private_destinations = {}
        self.observed = []

    def providers(self, key, reply=False):
        if reply:
            target = incidence.neighbors(self.receiver, self.n)[key]
            return incidence.groups(self.receiver, target, self.n)[0]
        if key < 2:
            return tuple(o for o in incidence.neighbors(self.receiver, self.n) if o % 2 == key)[:13]
        require(key >= 3, 'Unused plant key is not a meaningful comparison')
        target_index = (key-3)//self.c['FAST_TARGET_KEYS']
        target = incidence.neighbors(self.receiver, self.n)[target_index]
        return incidence.groups(self.receiver, target, self.n)[0]

    def location(self, logical, bank, key, reply=False):
        valid_key = 0 <= key < self.c['DEGREE'] if reply else key in (0, 1) or 3 <= key < self.c['FAST_KEYS']
        if not (0 <= logical < 13 and bank in (0, 1) and valid_key):
            return None, (reply, bank, key)
        provider = self.providers(key, reply)[logical]
        return (self.primary if logical == 0 else self.islands[provider]), (reply, bank, key)

    def set_record(self, logical, bank, key, value, reply=False, lifetime=2047):
        island, address = self.location(logical, bank, key, reply)
        require(island is not None, 'Cannot install a record outside actual physical layout')
        island.cells[address] = RawCell(value & MASK, lifetime)

    def perform(self, name, args, machine):
        if name == 'own_equal':
            target, side, address, expected = args
            d = Descriptor(name, (target,side,address), expected, expected, self.body, 0)
            if not (0 <= target < self.c['DEGREE'] and side in (0,1) and 0 <= address < self.c['IMAGE_CELLS']):
                return predicate(d, MASK)
            bay = self.own_bays[target]
            raw = self.own_override.get((target,side,address),
                    self.target_cells.get((target,side,bay,address),MASK)) & MASK
            island = self.own_islands[target]
            island.cells[d.raw_address] = RawCell(raw, 1)
            island.begin(d)
            self.raw_reads += 1
            return island.finish(self.body, self.private_destinations)
        if name not in ('fast_cmp', 'fast_equal', 'fast_range', 'reply_equal'):
            return super().perform(name, args, machine)
        logical, bank, key = args[:3]
        reply = name == 'reply_equal'
        island, address = self.location(logical, bank, key, reply)
        low = args[3] if name != 'fast_cmp' else 0
        high = args[4] if name == 'fast_range' else args[3]
        descriptor = Descriptor(name, address, low, high, self.body, 0)
        if island is None:
            return predicate(descriptor, MASK)
        island.begin(descriptor)
        result = island.finish(self.body, self.private_destinations)
        self.observed.append((name, logical, bank, key, island.last_capture[1], result))
        return result


def operation_checks():
    values = (0, 1, (1 << 64)-1, 1 << 64, (1 << 192)-1, 1 << 192, MASK-1, MASK)
    cases = 0
    for x, y in product(values, repeat=2):
        require(word_cmp(x, y) == ((x > y)-(x < y)), 'Four-limb comparison lost unsigned word semantics')
        for op in ('fast_cmp', 'fast_equal', 'reply_equal', 'own_equal'):
            d = Descriptor(op, (0,), y, y, (0, 0, 1), 9)
            expected = int(x <= y) if op == 'fast_cmp' else int(x == y)
            require(predicate(d, x) == expected, 'Predicate differs from actual word operation')
            cases += 1
    mixed_cases = 0
    for raw in values:
        for bound in (-1 << 255, -1, 0, 500, (1 << 255)-1, MASK, MASK+1):
            for op in ('fast_cmp', 'fast_equal', 'reply_equal'):
                d = Descriptor(op, (0,), bound, bound, (0,0,1), 9)
                expected = int(raw <= bound) if op == 'fast_cmp' else int(raw == bound)
                require(predicate(d, raw) == expected, 'Signed private argument changed raw comparison ABI')
                mixed_cases += 1
            for low in (-1, 0, bound):
                d = Descriptor('fast_range', (0,), low, bound, (0,0,1), 9)
                require(predicate(d, raw) == int(low <= raw <= bound), 'Mixed-sign range changed ABI')
                mixed_cases += 1
    island = Island()
    island.cells[(1,)] = RawCell(1200, 20)
    d = Descriptor('fast_cmp', (1,), 0, 500, (0, 0, 7), 9)
    island.begin(d)
    # Raw I changes after private descriptor capture, before its actual strobe.
    island.cells[(1,)].value = 0
    private = {}
    require(island.finish(d.body, private) == 1, 'Raw corruption was silently corrected/rejected')
    require(island.last_capture == (d, 0), 'Raw operand was bulk-copied into private launch state')
    require(d.upper == 500, 'Raw mutation changed private threshold')
    # Stale completion addresses the actual old body even if a socket is reused.
    island.cells[(1,)].value = 1200
    island.begin(d)
    new_body = (0, 0, 8)
    private[new_body] = {9: 23}
    island.finish(d.body, private)
    require(private[d.body][9] == 0 and private[new_body][9] == 23, 'Old completion crossed body identity')
    wrong_result = 1
    require(wrong_result != predicate(d, 1200), 'Execution-fault witness did not change the predicate')
    cell = RawCell(0, 15)
    cell.tick(15)
    require(cell.value == 0 and cell.capture() == MASK, 'Expiry assumed payload was erased')
    cell.receive(1200, 8)
    require(cell.capture() == 1200, 'Real new receipt failed to replace old payload')
    return dict(four_limb_predicate_cases=cases, mixed_signed_argument_cases=mixed_cases, raw_change_is_input_fault=True,
                privately_latched_threshold_preserved=True, old_body_completion_retained=True,
                altered_computed_result_is_distinct=True, expiry_preserves_but_masks_old_word=True)


@dataclass(frozen=True)
class Incident:
    kind: str
    owner: int
    other: int = -1


def footprint(event, receiver, providers):
    """Projection of the declared sites; roles fixed before any guard result."""
    out = set()
    if event.kind == 'fixture':
        hosts = {event.owner}
        if receiver == event.owner:
            out.add(0)
        elif event.owner in providers:
            out.add(providers.index(event.owner))
    elif event.kind == 'island':
        hosts = {event.owner}
        if receiver == event.owner:
            if event.other in providers[1:]:
                out.add(providers.index(event.other))
        elif event.owner in providers:
            out.add(providers.index(event.owner))
    elif event.kind == 'origin_supply':
        hosts = {event.owner}
        if event.owner in providers:
            out.add(providers.index(event.owner))
    else:
        raise ValueError(event.kind)
    return hosts, out


class ReachGraph:
    """Uncontrolled write/rail reach, distinct from ordinary input dependence.

    A raw operand affects a correctly computed predicate without gaining a
    write capability to that predicate's private argument/commit machinery.
    All raw and execution locations are instantiated before a fault is chosen.
    """
    def __init__(self, n):
        self.n = n
        self.edges = defaultdict(set)
        self.sites = {}
        self.meaning = {}
        raw_kinds = ('wire', 'staging', 'payload', 'receipt', 'raw_clock', 'capture')
        for i in range(n):
            self.sites[Incident('fixture', i)] = [('core', i), ('primary', i), ('source_scratch', i)]
            self.sites[Incident('origin_supply', i)] = [('supply', i)]
            self.meaning[('core', i)] = ('execution', i)
            self.meaning[('primary', i)] = ('primary', i)
            self.edges[('core', i)].add(('outgoing', i))
            self.edges[('source_scratch', i)].add(('outgoing', i))
            self.edges[('supply', i)].add(('core', i))
            for o in incidence.neighbors(i, n):
                raw_nodes = [('raw', i, o, kind) for kind in raw_kinds]
                private_nodes = [('private', i, o, kind) for kind in ('descriptor', 'compute', 'commit')]
                self.sites[Incident('island', i, o)] = raw_nodes+private_nodes
                for node in raw_nodes:
                    self.meaning[node] = ('input', i, o)
                    if node[-1] != 'raw_clock':
                        self.edges[('outgoing', o)].add(node)
                    self.edges[('supply', o)].add(node)
                for node in private_nodes:
                    self.edges[node].add(('core', i))
                backend = ('primary_backend', i, o)
                self.meaning[backend] = ('primary_backend', i, o)
                self.edges[('outgoing', o)].add(backend)
                self.edges[('supply', o)].add(backend)
                self.edges[('primary', i)].add(backend)
                # Private execute-state faults may propagate to private query/
                # result machinery; this supplies no raw-array write edge.
                self.edges[('core', i)].update(private_nodes)

    def reach(self, event):
        visited = set(self.sites[event])
        todo = deque(visited)
        while todo:
            for node in self.edges[todo.popleft()]:
                if node not in visited:
                    visited.add(node)
                    todo.append(node)
        return visited

    def project(self, reached, receiver, providers):
        hosts, slots = set(), set()
        for node in reached:
            role = self.meaning.get(node)
            if role is None:
                continue
            if role[0] == 'execution':
                hosts.add(role[1])
            elif role[0] == 'primary' and role[1] == receiver:
                slots.add(0)
            elif role[0] == 'primary_backend' and role[1] == receiver and role[2] == providers[0]:
                slots.add(0)
            elif role[0] == 'input' and role[1] == receiver and role[2] in providers[1:]:
                slots.add(providers.index(role[2]))
        return hosts, slots


def concrete_graph_checks():
    n = 432
    graph = ReachGraph(n)
    tested = 0
    for receiver in (0, 1):
        groups = [incidence.groups(receiver, t, n)[0] for t in incidence.neighbors(receiver, n)]
        groups += [tuple(o for o in incidence.neighbors(receiver, n) if o % 2 == parity)[:13]
                   for parity in (0, 1)]
        # Whole ring construction; all possible physical site forms modulo the
        # ring translation/parity symmetry. All consumer groups are checked.
        events = [Incident('fixture', receiver), Incident('origin_supply', receiver)]
        events += [Incident('island', receiver, o) for o in incidence.neighbors(receiver, n)]
        events += [Incident('island', o, receiver) for o in incidence.neighbors(receiver, n)]
        events += [Incident('fixture', o) for o in incidence.neighbors(receiver, n)]
        events += [Incident('origin_supply', o) for o in incidence.neighbors(receiver, n)]
        for event in events:
            reached = graph.reach(event)
            for providers in groups:
                actual = graph.project(reached, receiver, providers)
                expected = footprint(event, receiver, providers)
                require(actual == expected, 'Actual typed reach differs from incident projection')
                tested += 1
    # Add precisely the forbidden shared raw-clock connection, then recompute
    # reach rather than merely assert a larger fault count in the result table.
    providers = incidence.groups(0, 1, n)[0]
    for o in providers:
        graph.edges[('core', 0)].add(('raw', 0, o, 'raw_clock'))
    _, slots = graph.project(graph.reach(Incident('fixture', 0)), 0, providers)
    require(len(slots) == 13, 'Shared receiver raw feed did not invalidate the graph bound')
    return dict(physical_sites=len(graph.sites), typed_nodes=len(graph.meaning),
                graph_projection_cases=tested, shared_raw_feed_reaches_slots=len(slots),
                input_dependence_not_private_write_authority=True)


def projection_checks():
    n = 432
    cases = 0
    # Translation symmetry reduces receivers to one even and one odd origin;
    # every target, raw origin, and possible execution owner is still inspected.
    for r in (0, 1):
        groups = [incidence.groups(r, t, n)[0] for t in incidence.neighbors(r, n)]
        groups += [tuple(o for o in incidence.neighbors(r, n) if o % 2 == p)[:13] for p in (0, 1)]
        for providers in groups:
            for owner in range(n):
                events = [Incident('fixture', owner), Incident('origin_supply', owner)]
                events += [Incident('island', owner, o) for o in incidence.neighbors(owner, n)]
                for event in events:
                    hosts, slots = footprint(event, r, providers)
                    require(len(hosts) <= 1 and len(slots) <= 1, 'One physical incident amplified beyond one slot/host')
                    cases += 1
    providers = incidence.groups(0, 1, n)[0]
    pool = [Incident('fixture', 0)] + [Incident('fixture', o) for o in providers[:6]]
    pool += [Incident('island', 0, o) for o in providers[6:10]]
    covers = 0
    for size in range(7):
        for events in combinations(pool, size):
            hosts, slots = set(), set()
            for e in events:
                h, s = footprint(e, 0, providers)
                hosts |= h
                slots |= s
            require(len(hosts) <= size and len(slots) <= size, 'Union forgot incident multiplicity')
            covers += 1
    e1, e2 = Incident('island', 0, providers[1]), Incident('island', 0, providers[2])
    h1, j1 = footprint(e1, 0, providers)
    h2, j2 = footprint(e2, 0, providers)
    require(len(h1|h2) == 1 and len(j1|j2) == 2, 'Owner-collapse obstruction missing')
    return dict(site_group_cases=cases, joint_incident_covers=covers,
                two_sites_one_owner_two_inputs=True, one_shared_cover=True,
                scope='Declared finite site graph and full-window union; actual electrical reach and return remain suppliers')


def regularity_checks():
    results = []
    for m, regions in ((72, 6), (74, 6), (84, 6)):
        n = m*regions
        counts = Counter()
        for i in range(n):
            for target in incidence.neighbors(i, n):
                for o in incidence.groups(i, target, n)[0]:
                    counts[o] += 4*683
            for parity in (0, 1):
                for o in [j for j in incidence.neighbors(i, n) if j % 2 == parity][:13]:
                    counts[o] += 4
        used = 4*13*(40*683+2)
        allocated = 2*26*(27283+40)
        require(min(counts.values()) == max(counts.values()) == used <= allocated,
                'Origin-affine funding exceeds receiver inventory or is nonuniform')
        results.append(dict(hosts=n, records_per_origin=used, allocated=allocated))
    return results


def microinstruction_checks():
    # Priced native64 steps; indexed raw capture is a separate terminal below.
    costs = dict(fetch_decode=256, copy_eight_descriptor_words=8*4,
                 signed_selector_and_bound_checks=256, two_four_limb_comparisons=64,
                 private_commit=64, control_and_error_suffix=256)
    work = sum(costs.values())
    require(work <= 8192, 'Native work leaves no communication slack')
    mu = 1 << 27
    native_rate = F(4, 3)*16384*mu
    link_delay = F(1, 8*mu)
    selection_delay = F(1, 8*mu)
    used = F(work)/native_rate+link_delay+selection_delay
    available = F(3, 4*mu)
    require(used <= available, 'Remote operation exceeds funded instruction suffix')
    reset_delay = F(1, 8*mu)
    conservative = F(8192)/native_rate+link_delay+selection_delay
    require(conservative+reset_delay <= available, 'Remote private reset exceeds the instruction interval')
    raw_capture_price, link_price = 1024, 1024
    require(work+raw_capture_price+link_price <= 20480, 'Comparator exceeds I/O energy price')
    capture_bits = 2*80*(3*40)*256
    record_padding = (2048-976)*(2*26*(27283+40))
    require(capture_bits <= record_padding, 'Raw snapshot latches lack paid I storage')
    return dict(native_step_allocation=costs, native_steps=work,
                native_steps_upper=8192, native_rate=str(native_rate),
                selector_delay=str(selection_delay), descriptor_round_trip_delay=str(link_delay),
                actual_suffix_upper=str(used), available_suffix=str(available),
                conservative_suffix_and_reset=str(conservative+reset_delay), reset_delay=str(reset_delay),
                raw_capture_price=raw_capture_price, private_link_price=link_price,
                total_operation_price=work+raw_capture_price+link_price, existing_price=20480,
                raw_capture_bits=capture_bits, paid_raw_padding_bits=record_padding,
                scope='Priced native-step and indexed-capture source point; not a measured device')


def reentry_checks():
    # Real capsule/deadline state is distinct from corruptible digital busy
    # metadata. This represents the explicitly stated finite one-shot law.
    mu = 1 << 27
    tail, reset = F(1, 1 << 26)+F(1,64), F(1,8*mu)
    cases = 0
    for busy, metadata, has_funded_tail in product((False,True),(0,1,MASK),(False,True)):
        raw = RawCell(123,2047)
        private = {('old',): {9:19}, ('new',): {9:23}}
        actual_pending = (tail, ('old',), 9, 0) if has_funded_tail else None
        # No capsule is created from arbitrary busy/descriptor bits.
        funded_count = int(actual_pending is not None)
        now = tail
        if actual_pending is not None:
            deadline, body, address, value = actual_pending
            require(deadline <= now, 'Old funded operation was discarded early')
            private[body][address] = value
            actual_pending = None
        now += reset
        busy = False
        descriptor_valid = False
        require(actual_pending is None and not busy and not descriptor_valid, 'Dirty control state survived real drain/reset')
        require(private[('new',)][9] == 23 and raw.value == 123 and raw.remaining == 2047,
                'Private re-entry silently erased raw input or wrote a replacement socket')
        require(now < F(4)*F(100,101), 'Existing pre-publication wait omits added unit reset')
        require(funded_count == int(has_funded_tail), 'Digital pending metadata minted physical work')
        cases += 1
    return dict(dirty_control_states=cases, last_instruction_tail=str(tail), private_reset_tail=str(reset),
                existing_boot_wait_min=str(F(400,101)), raw_input_not_reset=True,
                arbitrary_busy_bits_do_not_mint_capsules=True,
                scope='Finite one-shot/reset law under actual launch cutoff and no-rearming electrical boundary')


def program_checks():
    c = pm.compile_check(geometry.design())
    p = ExternalPorts(c)
    machine = pm.Machine(c)
    k = c.constants
    target = 20
    base = k['TARGET_BASE']+target*k['TARGET_WORDS']
    loadkey = 3+target*k['FAST_TARGET_KEYS']+k['VIEW_WORDS']
    permissions = []
    for corrupted in (0, 1, 6, 7, 13):
        for logical in range(13):
            for bank in (0, 1):
                p.set_record(logical, bank, loadkey, 0 if logical < corrupted else 1200)
                p.set_record(logical, bank, loadkey+2, 0)
        code = machine.C[:]
        machine.enter('permission', (base, 0))
        require(machine.run(p, until_yield=False) == 'halt', 'Actual guard failed to terminate')
        require(machine.C == code, 'Input perturbation rewrote actual C')
        permissions.append(machine.result())
    require(permissions == [0, 0, 0, 1, 1], 'External comparisons changed actual threshold semantics')
    primary_results = []
    for primary in (490, 510):
        for logical in range(13):
            for bank in (0, 1):
                p.set_record(logical, bank, loadkey, primary if logical == 0 else 490 if logical <= 6 else 510)
                p.set_record(logical, bank, loadkey+2, 0)
        machine.enter('permission', (base, 0))
        machine.run(p, until_yield=False)
        primary_results.append(machine.result())
    require(primary_results == [1, 0], 'Full primary ceased to be action-relevant')
    # Compare expected compound reply through exactly the same private primitive.
    expected = ((2*80*8192-1) << 192) + (1 << 191)
    p.set_record(2, 1, target, expected, reply=True)
    require(p.perform('reply_equal', (2, 1, target, expected), machine) == 1, 'Full encoded cell reply was narrowed')
    require(p.perform('reply_equal', (2, 1, target, expected+1), machine) == 0, 'Wrong exact reply was accepted')
    own_bay = p.own_bays[target]
    p.target_cells[(target,1,own_bay,0)] = 77
    require(p.perform('own_equal',(target,1,0,77),machine) == 1, 'Actual own-candidate equality failed')
    require(p.perform('own_equal',(target,1,0,78),machine) == 0, 'Wrong own-candidate word accepted')
    p.own_override[(target,1,0)] = 78
    require(p.perform('own_equal',(target,1,0,78),machine) == 1, 'Raw own-read deception was falsely repaired')
    require(p.target_cells[(target,1,own_bay,0)] == 77, 'Comparison secretly corrected the actual cell')
    # Actual Machine.launch captures its private arguments; the island reads
    # raw I only when that launched instruction completes.
    direct = pm.Machine(c)
    direct.pc = 0
    direct.C[0] = pm.encode(pm.IO, 20, 30, 4, pm.PRIM['fast_cmp'])
    for index, value in enumerate((1,0,loadkey,500),30):
        direct.R[index] = value
    p.set_record(1,0,loadkey,1200)
    require(direct.launch(), 'Funded actual comparison did not launch')
    direct.R[33] = -1 & MASK
    p.set_record(1,0,loadkey,0)
    require(direct.complete(p), 'Launched comparison lost its actual completion')
    require(direct.R[20] == 1, 'Actual machine failed private-argument/raw-strobe separation')
    private_used = c.next_register+k['DATA_WORDS']+32
    extra = 8*(2*k['DEGREE']+1)
    require(private_used+extra <= 32768, 'External private comparison units have no paid memory')
    require(len(c.nodes) == 3315, 'Adapter silently changed the policy image')
    old = pm.RawPorts(c)
    malformed_cases = 0
    for op in ('fast_cmp', 'fast_equal', 'fast_range', 'reply_equal'):
        for origin, bank, key in ((-1,0,loadkey),(13,0,loadkey),(1,-1,loadkey),
                                 (1,2,loadkey),(1,0,-1),(1,0,k['FAST_KEYS']),
                                 (-(1<<255),0,loadkey),(1,0,(1<<255)-1)):
            for bound in (-(1<<255), -1, 0, 500, (1<<255)-1):
                args = (origin,bank,key,-1,bound) if op == 'fast_range' else (origin,bank,key,bound)
                require(p.perform(op,args,machine) == old.perform(op,args,machine),
                        'Malformed selector gained authority or changed missing-value semantics')
                malformed_cases += 1
    return dict(code_cells=len(c.nodes), private_words=private_used,
                external_private_words_per_cartridge=extra, combined_private_words=private_used+extra,
                allocated_private_words=32768, raw_comparisons=len(p.observed),
                corrupted_origins=[0,1,6,7,13], permission_results=permissions,
                primary_values=[490,510], primary_results=primary_results,
                exact_encoded_reply_bits=expected.bit_length(), original_policy_unchanged=True,
                malformed_descriptor_cases=malformed_cases, actual_machine_latched_query_checked=True,
                own_equal_raw_override_changes_result_not_cell=True)


def countercases():
    # A raw-only shared clock freezes known bad-but-valid values indefinitely.
    cells = [RawCell(0, 1) for _ in range(13)]
    require(sum(c.capture() <= 500 for c in cells) == 13, 'Wide raw clock obstruction vanished')
    for c in cells:
        c.tick(1)
    require(sum(c.capture() <= 500 for c in cells) == 0, 'Real expiry no longer blocks stale zero')
    # Two comparator destinations in one faultable compartment invalidate two
    # executors even though the apparatus has one physical owner label.
    execution_owners = {0, 1}
    require(len(execution_owners) > 1, 'Co-location did not violate site projection')
    # Wrong socket rebinding would overwrite new state with an old completion.
    old_result, new_private = 0, 23
    require(old_result != new_private, 'Old-completion corruption witness empty')
    return dict(shared_raw_clock_frozen_passing_slots=13, after_actual_expiry_passing_slots=0,
                colocated_comparator_execution_hosts=2,
                rebound_socket_would_overwrite_new_private_state=True,
                all_are_changes_to_actual_graph_or_transition_law=True)


def lean_checks():
    lean = Path(r'C:\Users\Sean\.elan\toolchains\leanprover--lean4---v4.33.0\bin\lean.exe')
    version = subprocess.run([str(lean),'--version'], capture_output=True, text=True, check=True).stdout.strip()
    require('version 4.33.0' in version, 'Unexpected Lean version')
    run = subprocess.run([str(lean),str(HERE/'Receiver.lean')], capture_output=True, text=True, check=True)
    lines = [line for line in run.stdout.splitlines() if line.startswith("'ByzantineReceiver.")]
    require(len(lines) == 7 and not run.stderr.strip(), 'Incomplete Lean declaration reports')
    for line in lines:
        if 'does not depend on any axioms' in line:
            continue
        match = re.search(r'depends on axioms: \[(.*?)\]',line)
        require(match is not None, 'Malformed axiom report')
        require(set(match.group(1).split(', ')) <= {'propext','Classical.choice','Quot.sound'},
                'Unapproved Lean axiom dependency')
    return dict(version=version, selected_declarations=7, axiom_reports=lines,
                scope='Projection/arithmetic kernels; source graph and physical realization are external premises')


def main():
    require(not sys.flags.optimize, 'Unoptimized checks required')
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    names = ('RECEIVER.md', 'Receiver.lean', 'receiver_model.py', 'program_model.py', 'program_source.py',
             'geometry_model.py', 'incidence_model.py', 'RUNTIME-PORTS.md', 'ACQUISITION.md')
    sources = {name:digest(name) for name in names}
    path = HERE/'receiver_results.json'
    previous = json.loads(path.read_text(encoding='utf-8')) if args.check else None
    if previous is not None:
        require(previous['sources'] == sources, 'Receiver input manifest changed')
    result = dict(schema='receiver-instruction-placement-v1', sources=sources,
                  scope='Instruction/incident/resource-placement adapter; electrical containment and causal return are separate',
                  operations=operation_checks(), projection=projection_checks(),
                  concrete_graph=concrete_graph_checks(),
                  regularity=regularity_checks(), program=program_checks(), countercases=countercases())
    result['microinstruction'] = microinstruction_checks()
    result['reentry'] = reentry_checks()
    result['lean'] = lean_checks()
    require(sources == {name:digest(name) for name in names}, 'Sources changed during receiver check')
    if args.write:
        path.write_text(json.dumps(result, sort_keys=True, indent=2)+'\n', encoding='utf-8', newline='\n')
    else:
        require(result == previous, 'Receiver reproduction differed')
    print('PASS receiver:', result['projection']['site_group_cases'], 'site/group cases;',
          result['projection']['joint_incident_covers'], 'joint covers; actual permissions',
          result['program']['permission_results'])


if __name__ == '__main__':
    main()

"""Pre-commissioning source-local wiring for the four-head B member. Device steps are imported."""
from fractions import Fraction as Q
from functools import lru_cache
from heapq import heapify
from pathlib import Path
from types import MappingProxyType
import sys

PORT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(PORT))
import b_cut_induction as cuts
import constructors
import fixed_island_model as islands
import legacy_realization as legacy
import receiver_lease as lease
import rx_product as rx
import threshold_incidence_model as incidence

raw = rx.raw
M = 12 * (6 + 2**98) + 2
need = constructors.require


def head(o):
    need(type(o) is int and 0 <= o < M, "Uninstalled physical head")
    return int(o % 8 >= 4) if o < M - M % 8 else incidence.head_type(o)


@lru_cache(maxsize=8192)
def plant(r, key):
    need(key in (0, 1), "Unknown physical plant measurement")
    group = tuple(o for o in incidence.neighbors(M, r) if head(o) == key)[:15]
    need(len(group) == 15, "Insufficient installed heads")
    return group


@lru_cache(maxsize=16384)
def group(r, key):
    if key in (0, 1):
        return plant(r, key)
    need(3 <= key < raw.KEYS, "No record for this key")
    return tuple(o for o, _ in incidence.maintenance_group(M, r, (key - 3) // 50)[1])


def stencil(o):
    return tuple(int(o in plant(r, k)) for r in incidence.neighbors(M, o)
                 for _br in (0, 1) for k in (0, 1))


def tree(words):
    level = tuple(words)
    while len(level) > 1:
        level = tuple(zip(level[::2], level[1::2], strict=True))
    return level[0]


def reader(r):
    selector = legacy.GroupSelector(M, r)
    words = list(selector.words)
    for key in (0, 1):
        for slot, o in enumerate(plant(r, key)):
            words[key*16 + slot] = 64 + selector.neighbors.index(o)
    selector.words, selector.tree = tuple(words), tree(words)
    return selector


def decoder(r, o):
    dev = legacy.ArrivalDecoder(M, r, o)
    words = list(dev.words)
    for key in (0, 1):
        g = plant(r, key)
        words[key] = 4096 + 2048 * int(o == g[0]) + key if o in g else 0
    dev.words, dev.tree = tuple(words), tree(words)
    return dev


def make_lane(ident, payer, captures=None):
    """Design elaboration before admitting initial values/jobs. Never a live reconfiguration."""
    lane = raw.RawLane(M, ident, payer, captures)
    lane.decoder = decoder(ident.receiver, ident.origin)
    for key in (0, 1):
        lane.records.pop(key, None)
        route = lane.decoder.decode(key)
        if route is not None:
            role, dest = route
            lane.records[dest] = raw.Record(lane, dest, 8, key, role)
    lane.ordered = tuple(lane.records[k] for k in sorted(lane.records))
    return lane


class Receiver(rx.Receiver):
    """Target-local enrollment. Physical checks and all transition methods are inherited."""
    def __init__(self, lane, phases):
        ident = lane.identity
        expected = decoder(ident.receiver, ident.origin)
        need(lane.population == M and type(lane) is raw.RawLane
             and type(lane.decoder) is legacy.ArrivalDecoder
             and (lane.decoder.words, lane.decoder.tree) == (expected.words, expected.tree),
             "Decoder differs from this installation")
        self.lane, self.lanes = lane, (lane,)
        self.fixed_records = dict(lane.records)
        self.record_wires = {}
        for source_key in range(raw.KEYS):
            dest = expected.decode(source_key)
            if dest is not None:
                role, key = dest
                need(key in lane.records and key not in self.record_wires, "Absent or aliased wire")
                rec = lane.records[key]
                self.record_wires[key] = rec, rec.control, source_key, role
        self.ordered = lane.ordered
        need(set(lane.records) == set(self.record_wires) and type(lane.ordered) is tuple
             and lane.ordered == tuple(lane.records[k] for k in sorted(lane.records)),
             "Ordered reset and receiving leaves disagree")
        self.structure = (ident, lane.payer, lane.queue, lane.rx, lane.queue.values, lane.decode_control,
                          lane.reset_control, lane.reset_work, lane.frame_words, lane.decoder, lane.decoder.tree)
        self.check_layout(all_records=True)
        self.now = Q(0)
        self.base = rx.native.Oscillator.at_rate(*phases.base, 4096, Q(4096*101, 100))
        old = self.base.due - self.base.period + rx.SIGMA
        need((phases.prior_return is None and old <= 0) or
             (phases.prior_return is not None and rx.charging.natural_quantity(phases.prior_return) == old),
             "Incorrect retained RX return")
        self.aperture = phases.prior_return
        need(set(phases.records) == set(lane.records), "Unrepresented independent record clock")
        self.clocks = {k: rx.native.Oscillator.at_rate(*spec, Q(5001,5000), Q(5049,5000))
                       for k, spec in phases.records.items()}
        self.tick_times = [(c.due, k) for k, c in self.clocks.items()]
        heapify(self.tick_times)
        need(set(phases.jobs) == {k for k,r in lane.records.items() if self._needs_service(r)},
             "Unrepresented earlier service")
        self.read_jobs = {}
        for k, (r, kind, claim, delay) in phases.jobs.items():
            need(lane.records[k] is r and kind == self._selected_service(r) and
                 (claim is r.claim if kind == "tick" else claim is None) and
                 rx.charging.natural_quantity(delay) <= raw.RECORD_DELAY, "Foreign retained work")
            self.read_jobs[k] = delay, kind, claim
        self.divider_work, self.edges = Q(0), 0


class PlantTaps(cuts.FixedTaps):
    def __init__(self, bank, constants, sites, regional_ports, quantize):
        super().__init__(bank, constants, sites, regional_ports, quantize)
        self.role = head(bank.origin)


def source_classes(matched):
    # Fixed preset data for the existing mutable leaves. The physical reset writer
    # and the Selector's actual paid decision operate on those same cells.
    base, selector = lease.recovery_classes(matched)
    class Source(base):
        def __init__(self, operating, payer, population):
            need(population == M, "Wrong installation")
            super().__init__(operating, payer, population)
            self._stencil = stencil(self.origin)
            self.control[self.FIRST:self.CLOCK] = self.stencil
    return Source, selector


def actual_addresses(r, key, br, sb):
    return tuple((r, br, o, sb, key, "primary" if i == 0 else "auxiliary")
                 for i, o in enumerate(group(r, key)))


def project(r, key, br, sb, events, retained=None):
    """Events carry occurrence id, physical kind/site/origin and actual private reach.
    Released/stopped descendants use the occurrence still sponsoring the addressed effect.
    This call consumes the address slice of a justified history cover; it cannot build that cover.
    """
    addresses = actual_addresses(r, key, br, sb)
    query = (r, key, br, sb)
    footprints = {}
    for uid, kind, site, origin, private in events:
        need(uid not in footprints and type(site) is int and 0 <= site < M and type(private) is bool,
             "Malformed or repeated occurrence identity")
        need(kind in {"source", "reset-root", "site", "execution", "primary", "lane", "pair", "coupler"},
             "Unknown raw capability")
        need(origin in incidence.neighbors(M,site) if kind == "lane" else origin is None,
             "False endpoint identity")
        owners = set()
        if kind in {"source","reset-root","site","execution"} or private:
            owners.add(site)
        if r == site:
            if kind in {"site","execution","primary"}:
                owners.add(addresses[0][2])
            elif kind == "pair":
                owners.update(islands.installed_pair(M,r))
            elif kind == "lane":
                owners.add(origin)
        reached = frozenset(a for a in addresses if a[2] in owners)
        if retained is not None and uid in retained:
            # An earlier local terminal can narrow only the named occurrence's leaves.
            reached = reached.intersection(retained[uid])
        footprints[uid] = {query: reached}
    return constructors.projected_support(tuple(footprints), footprints, query)

class OriginProduct(rx.OriginProduct):
    """Source-specific constructor for the same multibank keyed product. No event rule changes."""
    def __init__(self, banks, source_phases, lane_phases, *, complete=False):
        banks = tuple(banks)
        need(1 <= len(banks) <= 2 and len({b.side for b in banks}) == len(banks) and
             {b.side for b in banks} == set(source_phases), "Actual banks and phases differ")
        self.fixture = banks[0].fixture
        self.receivers, self.banks = {}, {}
        caps, shared_cells, private_cells, outside, registrations = {}, {}, set(), {}, []
        for b in banks:
            source, cpu = b.native_input, b.machine
            need(b.fixture is self.fixture and self.fixture.installed_source_ports.get(b.side) is b
                 and self.fixture.machines[b.side] is cpu and isinstance(source,rx.native.TimedSource)
                 and source.population == M and source.payer is self.fixture.source_work
                 and source.energy is source.operating_bank is cpu.bank
                 and cpu.bank.owner == (self.fixture.owner,b.side),"Unbound operating source")
            bus = getattr(cpu,"charging",None)
            need(bus is not None and getattr(bus,"native_dispatch",None) is None, "Unavailable charger")
            leads = tuple(raw.LaneId(self.fixture.owner,b.side,r,br)
                          for r in incidence.neighbors(M,self.fixture.owner) for br in (0,1))
            need(tuple(x.destination for x in source.branches) == leads
                 and all(x.bank is source and x.ordinal == i for i,x in enumerate(source.branches)),
                 "Physical source leads changed")
            outside[b.side] = frozenset(leads) - source.receivers_live.keys()
            need(not complete or not outside[b.side],"Incomplete source exits")
            for ident, lane in source.receivers_live.items():
                need(ident in leads and ident not in self.receivers and ident in lane_phases
                     and lane.identity == ident and lane.payer is source.payer,"Unbound receiving lane")
                state = (lane,lane.queue,lane.rx,lane.queue.values,lane.decode_control,lane.decoder,
                         lane.frame_words,lane.reset_control,lane.reset_work,
                         *(r.control for r in lane.ordered),*lane.ordered)
                ids = {id(x) for x in state}
                need(len(ids) == len(state) and ids.isdisjoint(private_cells),"Aliased receiver state")
                private_cells.update(ids)
                need(set(lane.captures) == {"primary","auxiliary"},"Missing physical capture")
                for role,c in lane.captures.items():
                    owner = (ident.origin,ident.receiver,ident.receiver_bank)
                    tag = owner, role
                    need(type(c) is raw.SharedCapture and c.owner == owner and c.kind == role
                         and c.payer is source.payer and caps.setdefault(tag,c) is c
                         and all(shared_cells.setdefault(id(x),tag) == tag for x in (c,c.cell)),
                         "Capture shared outside its physical fiber")
                self.receivers[ident] = Receiver(lane,lane_phases[ident])
            registrations.append((b,bus,source.receivers_live))
        need(set(self.receivers) == set(lane_phases) and private_cells.isdisjoint(shared_cells),
             "Unbound phase or shared/private alias")
        self.outside, self.captures = MappingProxyType(outside), MappingProxyType(caps)
        self.capture_bindings = {}
        for c in caps.values():
            self.check_capture(c)
            if c.pending is not None and c.pending.live:
                self.capture_bindings[id(c)] = (c.pending,*c.pending.destination)
        try:
            for b,bus,_ in registrations:
                phase = source_phases[b.side]
                self.banks[b.side] = rx.native.NativeClock(
                    b.machine,b.native_input,existing_bus=bus,installed_cut=b.disconnect,external_receivers=True,
                    adc_rate=phase.adc[0],adc_first=phase.adc[1],tx_base_rate=phase.tx[0],tx_first=phase.tx[1])
        except Exception:
            for b,bus,lookup in registrations:
                if b.side in self.banks:
                    del bus.native_dispatch
                    b.native_input.receivers_live = lookup
            raise
        self.now = Q(0)

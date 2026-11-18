"""A-prime's gate and two operating/transit paths on one finite-work installation."""

import json
from dataclasses import dataclass
from fractions import Fraction as Q
from pathlib import Path
import subprocess
import sys
from types import ModuleType

from projected_work_flow import frozen_gate, SOURCE

HERE = Path(__file__).resolve().parent
PREFIX = "theories-and-designs/byzantine-control/"
gate = frozen_gate()
DELTA = Q(1, 2**30)


def check(ok, message):
    if not ok:
        raise ValueError(message)


def at(commit, name):
    return subprocess.check_output(["git", "show", f"{commit}:{PREFIX}{name}"], cwd=HERE)


def old_module(name):
    path = HERE.parent / "local-control" / name
    module = ModuleType("_aprime_" + path.stem)
    module.__file__ = str(path)
    sys.modules[module.__name__] = module
    exec(compile(at(gate.FROZEN, "local-control/" + name), str(path), "exec"), module.__dict__)
    return module


class ThermalZone:
    """Exact heat and bath ledger for constant-power subarcs, using finite sums c*exp(a)."""

    def __init__(self, capacity, bath_rate):
        self.decay = Q(bath_rate) / Q(capacity)
        self.thermal = {}
        self.bath = {}
        self.cross_in = Q(0)
        self.cross_out = Q(0)

    @staticmethod
    def plus(*parts):
        total = {}
        for expression, sign in parts:
            for exponent, coefficient in expression.items():
                total[exponent] = total.get(exponent, 0) + sign * coefficient
        return {k: v for k, v in total.items() if v}

    def impulse(self, heat):
        check(heat >= 0, "Negative gate heat")
        self.thermal = self.plus((self.thermal, 1), ({0: Q(heat)}, 1))

    def advance(self, dt, heat_rate):
        check(dt > 0 and heat_rate >= 0, "Invalid local thermal profile")
        old = self.thermal
        equilibrium = Q(heat_rate) / self.decay
        shifted = self.plus((old, 1), ({0: equilibrium}, -1))
        new = self.plus(({k - self.decay * dt: v for k, v in shifted.items()}, 1), ({0: equilibrium}, 1))
        self.bath = self.plus((self.bath, 1), (old, 1), ({0: dt * heat_rate}, 1), (new, -1))
        self.thermal = new

    def accounted(self, nonthermal):
        return self.plus(({0: Q(nonthermal)}, 1), (self.thermal, 1), (self.bath, 1))


@dataclass(frozen=True, eq=False)
class GateRequest:
    """A captured, already partly paid local request with its original physical slot."""

    _owner: object
    _slot: tuple
    _packet: object
    _capture_cost: Q


class Fixture(gate.Completion):
    """Gate/parent/charger projections of the SAME U, E, T and physical coordinates."""

    def __init__(self, p, resources, owner, upstream, operating, transit):
        upstream = Q(upstream)
        cap = Q(resources["point"]["new_upstream_capacity"])
        tc = Q(resources["point"]["per_bank_transit_capacity"])
        check(
            0 <= upstream <= cap
            and len(operating) == len(transit) == 2
            and all(0 <= e <= p["EMAX"] for e in operating)
            and all(0 <= x <= tc for x in transit),
            "Outside an installed work store",
        )
        super().__init__(p, owner, upstream)
        self.E[:] = list(map(Q, operating))
        self.T[:] = list(map(Q, transit))
        self.Ucap, self.Tcap = cap, tc
        self.U_initial = Q(upstream)
        th = resources["thermal"]
        self.zone = ThermalZone(th["thermal_capacity"], th["passive_bath_coefficient"])
        self.gate_heat_framed = Q(0)
        self.non_gate_withdrawals = Q(0)
        self.non_gate_deposits = Q(0)
        self.converter_heat = Q(0)
        self.stroke_heat = Q(0)
        self.stock_spill = Q(0)
        self.pending_updates = {}
        self.last_offer = {}
        self.now = Q(0)
        self.sampler = gate.PredecessorSampler(self)
        self.carriage = gate.Abort(Q(p["ABORT_LIMIT"]))
        self.trips = [gate.Trip(), gate.Trip()]
        self.refresh_surviving_levels()

    def check_U_balance(self):
        self.zone.impulse(self.heat - self.gate_heat_framed)
        self.gate_heat_framed = self.heat
        check(
            0 <= self.U <= self.Ucap
            and self.U + self.heat + self.non_gate_withdrawals
            == self.U_initial + self.non_gate_deposits,
            "A common U transfer has no physical owner",
        )

    def refresh_surviving_levels(self):
        """Sample the still-surviving prestate before freezing it; retain actual surface ties."""
        if self.held_plane:
            return
        self.keeper = gate.keeper(
            getattr(self, "keeper", 0), self.positions["blend"], self.p["BLEND_LIMIT"]
        )
        self.output["keeper"] = self.keeper
        self.output["abort"] = self.carriage.raw()
        self.output["normal-cam"] = int(self.carriage.normal)
        for g in self.gates:
            name = g.name
            if g.family == "cam":
                vals = gate.cam_band_values(
                    self.positions["cam"], int(name.split(":")[1]), self.p, self.carriage.normal
                )
                if bool(self.output[name]) not in vals:
                    self.output[name] = int(next(iter(vals)))
            elif g.family == "writer":
                self.output[name] = int(self.positions[g.coordinate] < g.level)
            elif g.family == "catch" and self.positions[g.coordinate] != g.level:
                self.output[name] = 0
            elif g.family == "trip":
                self.output[name] = int(self.trips[g.side].enabled)
            elif g.family == "activation":
                z = self.positions[g.coordinate]
                self.output[name] = (
                    int(z == 0)
                    | int(z >= self.p["POWER_AT"]) << 1
                    | int(z >= self.p["DRIVER_AT"]) << 2
                    | int(z == self.p["WARM_AT"]) << 3
                )

    def endpoint_ports(self):
        """Completely connected or cut endpoints for the short exact charts, one observed CPU per bank."""
        conn = []
        bleed = []
        cpu = []
        for side in (0, 1):
            cut = self.positions[f"cut{side}"]
            shunt = self.positions[f"shunt{side}"]
            check(
                (cut == 0 and shunt == 0) or cut == self.p["CUT_LIMIT"],
                "Use the constitutive transfer for a partly diverted incoming supply",
            )
            conn.append(int(cut == 0))
            bleed.append(0 if cut == 0 else Q(1, 10))
            trip = self.output[f"trip{side}"] if self.held_plane else self.trips[side].enabled
            cpu.append(
                bool(
                    trip
                    and self.positions[f"act{side}:0"] >= self.p["POWER_AT"]
                    and self.E[side] > self.p["EOFF"]
                )
            )
        return dict(chi=tuple(conn), bleed=tuple(bleed), cpu_enabled=tuple(cpu))

    def undervoltage_contact(self, side):
        """Completed material trip. The sampler still reads the literal strict E predicate."""
        check(side in (0, 1), "No such bank contact")
        trip = self.trips[side]
        if self.held_plane or not trip.enabled or self.E[side] > self.p["EOFF"]:
            return False
        trip.enabled = False
        return True

    def slot_for(self, packet):
        # Families sharing one installed block also share its hardware root envelope.
        k, t = packet.kind, packet.target
        if k in ("hold", "report") and type(t) is str and t in self.output:
            return ("gate", t)
        if k in ("jam", "detach") and type(t) is str and t in self.positions:
            return ("pose", t)
        if k == "route" and type(t) is int and 0 <= t < len(self.route):
            return ("route", t)
        if k == "local-actuator" and type(t) is int and t in (0, 1):
            return ("drive", t)
        if (
            k == "pc"
            and isinstance(t, tuple)
            and len(t) == 2
            and type(t[0]) is int
            and type(t[1]) is int
            and t[0] in (0, 1)
            and 0 <= t[1] < self.p["B"]
        ):
            return ("gate", f"activation{t[0]}:{t[1]}")
        return ("fixed-ingress",)

    def wire_value(self, value):
        if type(value) is bool:
            return value
        if type(value) is int and -(1 << 256) <= value < (1 << 256):
            return value
        if type(value) is str and (value in self.positions or value in self.output):
            return value
        if (
            type(value) is tuple
            and len(value) == 2
            and all(type(x) is int and -(1 << 256) <= x < (1 << 256) for x in value)
        ):
            return value
        return None  # A physically malformed fixed word, never a caller-owned mutable object.

    def submit(self, kind, target, value, *, defer=False):
        # This entry is an actual physical update root, outside the ordinary ISA.
        kinds = ("report", "hold", "pc", "route", "jam", "detach", "local-actuator")
        packet = self.capture(
            kind if kind in kinds else "malformed", self.wire_value(target), self.wire_value(value)
        )
        slot = self.slot_for(packet)
        old = self.last_offer.get(slot)
        check(old is None or self.now - old >= Q(1, gate.RATE), "No new physical root at this slot")
        self.last_offer[slot] = self.now
        if not defer:
            self.refresh_surviving_levels()
            return self.apply(packet)
        if slot in self.pending_updates:
            paid = min(self.U, Q(gate.UPDATE_WORK))
            self.U -= paid
            self.heat += paid
            self.check_U_balance()
            return "busy/paid-refusal"
        paid = min(self.U, Q(256))
        self.U -= paid
        self.heat += paid
        self.check_U_balance()
        if paid < 256:
            return "capture-underfunded"
        token = GateRequest(self, slot, packet, paid)
        self.pending_updates[slot] = token
        return token

    def settle(self, token):
        if (
            not isinstance(token, GateRequest)
            or token._owner is not self
            or self.pending_updates.get(token._slot) is not token
        ):
            return "no-pending-right"
        del self.pending_updates[token._slot]
        self.refresh_surviving_levels()
        packet = token._packet
        regular = gate.UPDATE_WORK - token._capture_cost
        entry = gate.UPDATE_WORK if self._valid_entry(packet) and not self.held_plane else 0
        paid = regular + entry if self.U >= regular + entry else min(self.U, Q(regular))
        self.U -= paid
        self.heat += paid
        result = self._commit(packet) if paid == regular + entry else "partial/no-change"
        self.check_U_balance()
        return result


class BankPort:
    """The legacy instruction cell's source energy is its actual E, not a copied value."""

    def __init__(self, fixture, side):
        self.fixture = fixture
        self.side = side
        self.spent = Q(0)  # Native dissipation from this cell AFTER E paid its charger.

    @property
    def energy(self):
        return self.fixture.E[self.side]


class RawCapture:
    def __init__(self, population, origin, destination, role, receiver_bank, cartridge, thermal):
        check(
            type(population) is int
            and population >= 432
            and population % 2 == 0
            and all(type(o) is int and 0 <= o < population for o in (origin, destination))
            and origin in tuple((destination + i) % population for i in (*range(-20, 0), *range(1, 21)))
            and origin != destination
            and role in ("primary", "auxiliary")
            and receiver_bank in (0, 1)
            and 0 <= cartridge < 80,
            "Wrong origin-affine capture identity",
        )
        self.owner = origin
        self.thermal_zone = thermal
        self.zone = (destination, origin, role)
        self.socket = (origin, destination, receiver_bank, cartridge, role)
        self.energy = Q(0)
        self.heat = Q(0)
        self.received = Q(0)
        self.pending = None
        self.snapshot = None
        self.records = {}
        self.due = None

    def launch(self, now, source_bank, key):
        if self.pending is not None or self.energy != 1024:
            return None
        check(source_bank in (0, 1) and type(key) is int and key >= 0, "Uninstalled selector")
        check((source_bank, key) in self.records, "No installed record at this capture")
        self.pending = (object(), source_bank, key)
        self.due = Q(now) + DELTA
        return self.pending

    def finish(self, now, token):
        if token is None or token is not self.pending or self.due != now:
            return False
        check(self.energy == 0, "Unspent raw work at its selected terminal")
        _, source_bank, key = token
        self.pending = self.due = None
        self.snapshot = self.records[source_bank, key]
        return True


def held_rates(
    host,
    cells,
    capture,
    *,
    chi,
    bleed,
    cpu_enabled,
    efforts,
    gross_input=Q(0),
    other_local_load=Q(0),
    mechanical=None,
):
    """Instantaneous port evaluation; the returned rates are not independent histories."""
    check(
        capture.owner == host.owner
        and len(cells) == 2
        and all(cell.source.fixture is host and cell.source.side == i for i, cell in enumerate(cells)),
        "An E-funded parent or U-funded capture has the wrong owner",
    )
    check(
        len(chi) == len(bleed) == len(cpu_enabled) == 2
        and all(c in (0, 1) for c in chi)
        and all(k >= 0 for k in bleed)
        and gross_input >= 0
        and other_local_load >= 0,
        "Invalid held physical ports",
    )
    g = min(1, host.U)
    # Interior active requests per free charger. A charged cap closes both ends.
    raw_power = Q(1024) / DELTA * g if capture.pending is None and capture.energy < 1024 else 0
    e_to_cpu = tuple(
        c.price / c.recharge_time * min(1, e) if en and not c.active and c.charge < c.price else 0
        for c, e, en in zip(cells, host.E, cpu_enabled)
    )
    transit_in = tuple(g * Q(41, 10) * host.Tcap * x for x in chi)
    tnet = tuple(i - Q(41, 10) * t for i, t in zip(transit_in, host.T))
    tspill = tuple(max(0, n) if t == host.Tcap else 0 for n, t in zip(tnet, host.T))
    pilot_draw = pilot_return = pilot_heat = Q(0)
    if mechanical is not None or host.held_plane:
        if mechanical is not None:
            check(
                getattr(mechanical, "__self__", None) is host
                and mechanical == getattr(host, "motion", None),
                "Foreign mechanical port",
            )
            law = mechanical(efforts)
            pilot_draw, pilot_return, pilot_heat = law["pilot"]
        else:
            law = gate.actuator_rates(host, efforts)
        drives = law["banks"]
        housing_heat = law["mechanical_dissipation"]
        field_power = law["external_input_power"]
        velocities = law["velocities"]
    else:
        check(
            not any(a for _, a in host.local_drive) and not any(efforts),
            "This executable normal subarc covers stationary poses; use the winding/stop law for motion",
        )
        drives = [dict(draw=0, returned=0, heat=0) for _ in cells]
        velocities = {k: Q(0) for k in host.positions}
        housing_heat = field_power = Q(0)
    enet = tuple(
        4 * t + a["returned"] - a["draw"] - k * e - cpu
        for t, e, k, a, cpu in zip(host.T, host.E, bleed, drives, e_to_cpu)
    )
    espill = tuple(max(0, n) if e == host.p["EMAX"] else 0 for n, e in zip(enet, host.E))
    # The displayed trace chooses the least admitted efficiency 1/2 on the
    # transit and remote raw converters. Local CPU chargers use ideal transfer.
    local_load = g * other_local_load
    u_out = 2 * (sum(transit_in) + raw_power) + local_load + pilot_draw
    unet = gross_input + pilot_return - u_out
    uspill = max(0, unet) if host.U == host.Ucap else 0
    heat_conv = sum(transit_in) + raw_power + sum(a["heat"] for a in drives) + pilot_heat
    heat_loss = local_load + sum(host.T) / 10 + sum(k * e for k, e in zip(bleed, host.E)) + housing_heat
    heats = heat_conv + heat_loss + uspill + sum(tspill) + sum(espill)
    dU = unet - uspill
    dT = tuple(n - s for n, s in zip(tnet, tspill))
    dE = tuple(n - s for n, s in zip(enet, espill))
    # Local bounds certify the heat/flow ports, not an unearned method-level success.
    check(
        dU + sum(dT) + sum(dE) + sum(e_to_cpu) + heats == gross_input + field_power - raw_power,
        "Host-zone nonthermal plus thermal rate lost a cross-zone port",
    )
    check(
        all(t or n >= 0 for t, n in zip(host.T, dT))
        and all(e or n >= 0 for e, n in zip(host.E, dE))
        and (host.U > 0 or dU >= 0),
        "A lower stop supplied unpriced work",
    )
    return dict(
        U=dU,
        T=dT,
        E=dE,
        CPU=e_to_cpu,
        capture=raw_power,
        Uout=u_out,
        Urefund=pilot_return,
        Usupply=gross_input,
        field=field_power,
        velocities=velocities,
        conversion=heat_conv,
        loss=heat_loss,
        spill=uspill + sum(tspill) + sum(espill),
    )


def constant_arc(host, cells, capture, dt, *, native_returns=None, receiver_winding=None, **inputs):
    """Analytic linear subarc at a stated constant drift, ending exactly at most at its first cap."""
    dt = Q(dt)
    check(
        dt > 0
        and (
            inputs.get("mechanical") is not None
            or (all(k == 0 for k in inputs["bleed"]) and not any(inputs["efforts"]))
        ),
        "This exact elapsed witness requires a declared constant port chart",
    )
    native_returns = {} if native_returns is None else native_returns
    end = host.now + dt
    for j, c in enumerate(cells):
        if c.active:
            check(
                c.last_energy_time == host.now and end <= c.due and (end < c.due or j in native_returns),
                "Split at the original parent deadline and supply its real return",
            )
    if capture.pending is not None:
        check(
            end <= capture.due and capture.energy == 1024 * (capture.due - host.now) / DELTA,
            "Split at the existing raw capture terminal",
        )
    law = held_rates(host, cells, capture, **inputs)
    receiving_heat = Q(0)
    cross_input = law["field"]
    if receiver_winding is not None:
        line, receiving_heat, shaft = receiver_winding
        check(
            inputs.get("mechanical") is not None
            and receiving_heat >= 0
            and line == receiving_heat + shaft,
            "Unmatched receiving-zone winding port",
        )
        cross_input += line - shaft  # The wiring moved that shaft interface inside this material zone.
    check(
        all(x == 0 for x in law["T"])
        and law["spill"] == 0
        and host.U >= 1
        and host.U + dt * law["U"] >= 1
        and 0 <= host.U + dt * law["U"] <= host.Ucap
        and all(
            (e >= 1 and 1 <= e + dt * n <= host.p["EMAX"]) or (e == 0 and n == 0)
            for e, n in zip(host.E, law["E"])
        )
        and all(k == 0 or n == 0 for k, n in zip(inputs["bleed"], law["E"])),
        "Crossed a stock regime; use the general held-flow solution",
    )
    check(
        all(c.charge + rate * dt <= c.price for c, rate in zip(cells, law["CPU"]))
        and capture.energy + dt * law["capture"] <= 1024,
        "Crossed an eligible charger capacity",
    )
    check(host.held_plane or dt <= host.sampler.remaining, "Crossed a due native sampler")
    for name, z in host.positions.items():
        if name != "cam":
            check(0 <= z + dt * law["velocities"][name] <= host.limits[name], "Crossed a stroke stop")
    if not host.held_plane:
        host.sampler.flow_clock(dt)
    host.U += dt * law["U"]
    host.non_gate_deposits += dt * (law["Usupply"] + law["Urefund"])
    host.non_gate_withdrawals += dt * law["Uout"]
    host.converter_heat += dt * law["conversion"]
    host.stroke_heat += dt * law["loss"]
    for j, c in enumerate(cells):
        host.E[j] += dt * law["E"][j]
        c.charge += dt * law["CPU"][j]
    for name, v in law["velocities"].items():
        host.positions[name] += dt * v
        if name == "cam":
            host.positions[name] %= host.limits[name]
    capture.energy += dt * law["capture"]
    capture.received += dt * law["capture"]
    native_heat = sum((c.price / (c.due - c.started) for c in cells if c.active), Q(0))
    host.zone.advance(dt, law["conversion"] + law["loss"] + native_heat + law["spill"] + receiving_heat)
    host.zone.cross_in += dt * (law["Usupply"] + cross_input)
    host.zone.cross_out += dt * law["capture"]
    capture.thermal_zone.cross_in += dt * law["capture"]
    capture.thermal_zone.advance(dt, 1024 / DELTA if capture.pending is not None else Q(0))
    host.now = end
    if capture.pending is not None:
        pulse = dt * 1024 / DELTA
        capture.energy -= pulse
        capture.heat += pulse
    for j, c in enumerate(cells):
        if c.active:
            c.elapse(end, native_returns.get(j))
    host.check_U_balance()
    return law


def rated_transfers(requests, incidence, limits, compulsory, allocations):
    """One actual sending power per edge under all of its incident physical budgets.

    Coefficients are held conversion/port incidences. A physical receiving cut
    counts the actual delivered part, while a sending cut counts its gross part.
    """
    check(
        set(requests) == set(incidence) and set(limits) == set(compulsory) == set(allocations),
        "Incomplete physical outlet or budget",
    )
    for wall, limit in limits.items():
        admitted = allocations[wall]
        check(
            set(admitted) == {e for e, walls in incidence.items() if wall in walls},
            "A cut forgot a shared port",
        )
        check(
            0 <= compulsory[wall] <= limit
            and all(a >= 0 for a in admitted.values())
            and sum(admitted.values()) <= limit - compulsory[wall],
            "Allocated a physical cut twice",
        )
    gross = {}
    for e, request in requests.items():
        walls = incidence[e]
        check(
            request >= 0 and walls and set(walls) <= set(limits) and all(c > 0 for c in walls.values()),
            "Unrooted or negative transfer",
        )
        gross[e] = min(request, *(Q(allocations[w][e]) / c for w, c in walls.items()))
    return gross


def check_shared_limits():
    inc = {"raw": {"sender": 1, "island": Q(1, 2)}, "other": {"sender": 1, "world": 1}}
    limits = {"sender": 100, "island": 50, "world": 60}
    standing = {"sender": 5, "island": 0, "world": 7}
    shares = {"sender": {"raw": 60, "other": 35}, "island": {"raw": 16}, "world": {"other": 20}}
    assert rated_transfers({"raw": 200, "other": 100}, inc, limits, standing, shares) == {
        "raw": 32,
        "other": 20,
    }
    # All simultaneous feasible arrays are recovered by using their realized
    # incidence-weighted powers as allocations at the relevant source cuts.
    count = 0
    for a in range(0, 101, 5):
        for b in range(0, 61, 5):
            if a + b > 95 or b > 53:
                continue
            expected = {"raw": a, "other": b}
            exact = {
                w: {e: expected[e] * systems[w] for e, systems in inc.items() if w in systems}
                for w in limits
            }
            assert rated_transfers(expected, inc, limits, standing, exact) == expected
            count += 1
    return count


def exterior_flow(effort, work_request, floor=Q(1, 4)):
    """One optional physical continuation for a power-rated world channel at zero effort.

    work_request is the SIGNED requested work of this actual channel after funding;
    keep different channel requests and payer identities separate.
    """
    check(floor > 0 and abs(work_request) <= 2**96, "Unfunded/unrated single WORLD port")
    x = Q(effort)
    demand = Q(work_request)
    scale = max(abs(x), floor)
    return demand * x / scale**2


def world_checks():
    pmax = Q(2**96)
    for x in (Q(-2), Q(-1, 4), Q(-1, 10), 0, Q(1, 10), Q(1, 4), Q(7, 20), Q(13, 20), 3):
        for work in (-pmax, 0, pmax):
            y = exterior_flow(x, work)
            assert abs(x * y) <= abs(work) and abs(y) <= 4 * pmax
            if abs(x) >= Q(1, 4):
                assert x * y == work
            if x == 0:
                assert y == 0
    return 27


def assembled_cases():
    p, geo, resources = gate.parameters()
    machine = old_module("program_model.py")
    ports = old_module("port_model.py")
    design = dict(geo["design"])
    design["physical_parameters"] = tuple(map(tuple, design["physical_parameters"]))
    compiled = machine.Compiler(machine.Design(**design)).compile()
    tc = Q(resources["point"]["per_bank_transit_capacity"])
    cap = p["EMAX"]
    host = Fixture(
        p, resources, 2, resources["point"]["new_upstream_capacity"], (cap / 2, cap / 2), (tc, tc)
    )
    host.sampler.remaining = DELTA
    cells = tuple(ports.Slot(BankPort(host, b), price=Q(20480), recharge_time=2 * DELTA) for b in (0, 1))
    th = resources["thermal"]
    remote_zone = ThermalZone(th["thermal_capacity"], th["passive_bath_coefficient"])
    census = json.loads(at(gate.FROZEN, "local-control/port_source_results.json"))["world"][
        "regional_population"
    ]
    n = 6 * int(census)
    plant0 = [o for o in old_module("incidence_model.py").neighbors(0, n) if o % 2 == 0][:13]
    assert 2 in plant0[1:]
    caprow = RawCapture(n, 2, 0, "auxiliary", 0, 0, remote_zone)
    eff = [Q(0)] * len(host.route)
    # A supplied common powered slice: both physical bulk routes are connected,
    # only A's observed cartridge is positioned for CPU operation.
    host.positions["carrier0"] = p["SEAT_LIMIT"]
    for b0 in range(p["B"]):
        host.positions[f"seat0:{b0}"] = p["SEAT_LIMIT"]
    host.positions["act0:0"] = p["WARM_AT"]
    host.positions["clamp0"] = p["CLAMP_LIMIT"]
    host.trips[1].transition(host.E[1], p["EOFF"], p["EON"], zero=True)
    host.refresh_surviving_levels()
    inp = dict(**host.endpoint_ports(), efforts=eff, other_local_load=Q(1, 1024))
    assert inp["chi"] == (1, 1) and inp["cpu_enabled"] == (True, False)

    def stocks():
        return (
            host.U
            + sum(host.E)
            + sum(host.T)
            + sum(c.charge + c.source.spent for c in cells)
            + host.heat
            + host.converter_heat
            + host.stroke_heat
        )

    initial = stocks()

    def zone_balance():
        e = host.U + sum(host.E) + sum(host.T) + sum(c.charge for c in cells)
        assert host.zone.accounted(e) == {0: initial + host.zone.cross_in - host.zone.cross_out}
        expect = remote_zone.cross_in - remote_zone.cross_out
        assert remote_zone.accounted(caprow.energy) == ({0: expect} if expect else {})

    zone_balance()
    out = constant_arc(host, cells, caprow, DELTA, **inp)
    assert (
        caprow.energy == 1024
        and cells[0].charge == 10240
        and out["Uout"] > 0
        and stocks() + caprow.energy == initial
    )
    assert host.sampler.strobe() == "captured" and host.heat == 2048
    caprow.records[0, 0] = 991
    first = caprow.launch(host.now, 0, 0)
    assert not caprow.finish(host.now, first)
    constant_arc(host, cells, caprow, DELTA, **inp)
    assert (
        caprow.finish(host.now, first) and caprow.snapshot == 991 and not caprow.finish(host.now, first)
    )
    assert (
        cells[0].charge == 20480
        and caprow.energy == 0
        and stocks() + caprow.energy + caprow.heat == initial
    )

    cpu = machine.Machine(compiled)
    host.body_machines[0, 0] = cpu
    cpu.C[0] = machine.encode(machine.STOREC, 3, 4)
    cpu.R[3] = 991
    cpu.R[4] = 7
    assert host.endpoint_ports()["cpu_enabled"][0]
    assert cells[0].offer(host.now, "old parent", Q(3, 4 * 2**26)) and cpu.launch(funded=cells[0].active)
    old = cpu.pending_instruction
    later = host.submit("hold", "normal-cam", 0, defer=True)
    assert isinstance(later, GateRequest)
    # Distinct paid roots: the same older endpoint can still arrive after an immediate update.
    constant_arc(host, cells, caprow, DELTA, **inp)
    assert host.submit("hold", "normal-cam", 1) == "held" and host.output["normal-cam"] == 1
    assert host.settle(later) == "held" and host.output["normal-cam"] == 0
    assert host.settle(later) == "no-pending-right"
    assert host.submit("pc", (0, 0), 0) == "pc-reset/old-IR-retained" and cpu.pending_instruction is old
    due = cells[0].due
    constant_arc(
        host,
        cells,
        caprow,
        due - host.now,
        native_returns={0: lambda _: check(cpu.complete(machine.RawPorts(compiled)), "No old return")},
        **inp,
    )
    assert host.now == due and not cells[0].active
    assert cpu.C[7] == 991 and cpu.pending_instruction is None
    dest = list(host.positions).index("reset1")
    assert host.submit("local-actuator", 0, (dest, 68)) == "local-actuator/held-plane"
    assert host.submit("local-actuator", 1, (dest, -10)) == "local-actuator/held-plane"
    rates = held_rates(host, cells, caprow, **inp)
    assert rates["velocities"]["reset1"] == Q(11, 10)
    initial2 = stocks() + caprow.energy + caprow.heat
    constant_arc(host, cells, caprow, DELTA, **inp)
    assert stocks() + caprow.energy + caprow.heat == initial2
    zone_balance()
    # The same mathematical derivative takes simultaneous transit, post-cut bleed,
    # hostile backdrive, subunit source stock, upper overflow and real no-work cases.
    phase_rows = 0
    for u in (0, Q(1, 2), 1, host.Ucap):
        for e in (0, Q(1, 4), 1, cap):
            for cut in (False, True):
                host.U = Q(u)
                host.E[0] = Q(e)
                host.E[1] = cap
                host.T[:] = [0, tc]
                rr = held_rates(
                    host,
                    cells,
                    caprow,
                    chi=(int(not cut), 1),
                    bleed=(Q(1, 10) * cut, 0),
                    cpu_enabled=(not cut, True),
                    efforts=eff,
                    gross_input=Q(3),
                )
                assert rr["capture"] == 0
                phase_rows += 1
    starved = Fixture(p, resources, 2, 300, (0, 0), (0, 0))
    claim = starved.submit("hold", "normal-cam", 1, defer=True)
    assert isinstance(claim, GateRequest) and starved.U == 44
    try:
        starved.submit("hold", "normal-cam", 1)
    except ValueError:
        pass
    else:
        raise AssertionError("Repeated same-time root at a single physical slot")
    assert starved.settle(claim) == "partial/no-change" and not starved.held_plane and starved.U == 0
    assert starved.heat == 300 and not starved.pending_updates and starved.sampler.clock_rate() == 0
    assert starved.zone.accounted(starved.U) == {0: Q(300)}
    for update_first in (False, True):
        tied = Fixture(p, resources, 2, 2048, (0, 0), (0, 0))
        tied.sampler.remaining = 0  # An actual already-due root at this cut.
        tied.positions["cut1"] = p["CUT_LIMIT"]
        if update_first:
            assert tied.submit("hold", "normal-cam", 1) == "held"
            assert tied.sampler.strobe() == "held-plane/no-autonomous-gate-update"
        else:
            assert tied.sampler.strobe() == "captured"
            assert tied.submit("hold", "normal-cam", 1) == "partial-work/no-gate-change"
        assert tied.held_plane == update_first and tied.U == 0 and tied.heat == 2048
        assert tied.cleanup_sample[0] == (not update_first)
    boundary = Fixture(p, resources, 2, 4096, (p["EOFF"], cap), (0, 0))
    assert not gate.physical_contact_snapshot(boundary)["low-E", 0]
    assert boundary.undervoltage_contact(0) and not boundary.undervoltage_contact(0)
    assert not boundary.trips[0].enabled and not gate.physical_contact_snapshot(boundary)["low-E", 0]
    # The electrical upgrade and a held HIGH pose do not create a fresh POWER crossing.
    boundary.E[0] = p["EON"]
    assert not boundary.trips[0].transition(boundary.E[0], p["EOFF"], p["EON"], old_done=True)[0]
    # Honest all-interval price and shared U lower-stock arithmetic.
    gate_record = json.loads(at(SOURCE, "portability/gate_source_completion_results.json"))
    gb = gate_record["bounds"]
    point = resources["point"]
    assert Q(gb["new_upstream_rate_upper"]) == Q(point["upstream_rate"])
    assert Q(gb["new_upstream_burst"]) == Q(point["upstream_burst"]) + gb["additional_burst"]
    assert Q(gb["same_upstream_capacity"]) - Q(gb["new_upstream_burst"]) - 2 * Q(
        gb["new_upstream_rate_upper"]
    ) == Q(gb["usable_reserve_lower"])
    gross = Q(resources["thermal"]["nominal_primitive_peak_fit_upper"])
    fixture_extra = Q(687859, 20)
    # Deliberate overbound, including already-paid mechanical terms again
    # for a peak feasibility check only; no new recoverable E/U is claimed.
    check(
        gross + 41 * fixture_extra < Q(15 * (1 << 96)),
        "Ordinary and added mechanical ports exceed material budget",
    )
    return dict(
        simultaneous_feasible_cut_allocations=check_shared_limits(),
        closed_material_trip_preserves_strict_sample=True,
        two_operating_banks=True,
        exterior_world_port_faces=world_checks(),
        paid_affected_parent_word=cpu.C[7],
        remote_capture_energy=1024,
        once_only_old_gate=True,
        host_and_remote_Y_with_bath=True,
        all_stock_cut_derivatives=phase_rows,
        single_U_reserve=gb["usable_reserve_lower"],
        added_burst=gb["additional_burst"],
    )


if __name__ == "__main__":
    if sys.version_info[:2] != (3, 12) or not __debug__:
        raise SystemExit("Use unoptimized Python 3.12")
    result = assembled_cases()
    print(json.dumps(result, indent=2, sort_keys=True))

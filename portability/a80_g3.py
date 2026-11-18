"""Conjugate ports, clocked contacts and one zone balance for the amended A80 member."""

from fractions import Fraction as Q
from math import floor
from pathlib import Path
import sys

import a80_return_seat as seat

src = seat.source
g = src.gate
K = Q(11, 15)
VMAX = seat.VMAX


def require(ok, msg):
    if not ok:
        raise ValueError(msg)


class MeasuredClock(seat.SeatClock):
    def strobe(self):
        return self.state.measured_strobe()


class JoinedSeat(seat.ReturnFixture):
    def __init__(self, p, resources, keeper=0, **options):
        super().__init__(p, resources, keeper, **options)
        self.pose_names = tuple(self.positions)
        self.efforts = [Q(0)] * len(self.route)
        self.bound_coils = None
        self.electrical_trace = None
        self.disturbance = {}
        self.pilot = {}
        self.held_law = (self.threshold, self.compliance)
        self.controls_extra = ("cam-clamp-here", "rewind-path", "rewind-key", "normal-cam-stops")
        self.new_controls += self.controls_extra
        require(len(self.new_controls) <= seat.EXTRA_BLOCKS, "Pilot descriptor bound")
        self.gates = (*self.gates, *(g.Gate(n, "return-pole", None) for n in self.controls_extra))
        self.output.update(dict.fromkeys(self.controls_extra, 0))
        old = self.sampler
        self.sampler = MeasuredClock(self, old.period, old.remaining)
        self.refresh_surviving_levels()

    def refresh_surviving_levels(self):
        super().refresh_surviving_levels()
        if self.held_plane or not hasattr(self, "controls_extra"):
            return
        c = self.carriage
        # ARM the keeper stop in FULL. A shaft moving toward that stop is not clamped
        # at its current angle at the instant an unrelated physical takeover occurs.
        self.output["cam-clamp-here"] = int(
            c.phase in ("ENTERING", "RETURN") or (c.phase == "FULL" and not self.prepark[self.keeper])
        )
        self.output["rewind-detent"] = int(c.phase == "FULL")
        self.output["rewind-path"] = int(c.phase == "FULL" and self.prepark[self.keeper])
        self.output["rewind-key"] = self.keeper
        self.output["normal-cam-stops"] = int(c.normal)
        if c.phase == "NORMAL":
            self.output["direction-in"], self.output["direction-out"] = 0, 1
        elif c.phase == "ENTERING":
            self.output["direction-in"], self.output["direction-out"] = 0, 1
        elif c.phase == "FULL":
            self.output["direction-in"], self.output["direction-out"] = 0, 0

    def connected_pairs(self):
        """Effort routing and its transpose use the same rigid-coordinate representative."""
        names = self.pose_names
        attached = {
            n: f"carrier{n[4]}" for n in names if n.startswith("seat") and n not in self.detached
        }
        require(
            all(self.positions[n] == self.positions[a] for n, a in attached.items()),
            "Broken rigid identification",
        )
        routes = []
        for i, (j, sign) in enumerate(self.route):
            if self.held_plane:
                require(-1 <= j < len(names) and sign in (-1, 1), "Uninstalled force binding")
                if j < 0:
                    routes.append(None)
                    continue
            else:
                j = i % self.driven
                sign = 1
            n = names[j]
            routes.append((attached.get(n, n), sign))
        return attached, routes

    def geometry(self, name):
        """(locked, allow positive, allow negative, keeper stop) at the actual cut."""
        phase = self.carriage.phase
        if name == "cam":
            if self.held_plane:
                lock = bool(self.output["cam-clamp-here"])
                armed = bool(self.output["rewind-detent"])
                path = bool(self.output["rewind-path"])
                return (
                    lock or (armed and not path),
                    not (armed or path),
                    True,
                    self.output["rewind-key"] if armed else None,
                )
            if phase == "FULL":
                return (not self.prepark[self.keeper], False, True, self.keeper)
            return (phase in ("ENTERING", "RETURN"), True, True, None)
        if name == "abort":
            if self.held_plane:
                return (
                    False,
                    bool(self.output["direction-out"]),
                    bool(self.output["direction-in"]),
                    None,
                )
            if phase == "RETURN":
                return (False, not self.keys[self.keeper], self.keys[self.keeper], None)
            return (phase == "FULL", True, False, None)
        lock = (
            bool(self.output["return-lock:" + name])
            if self.held_plane and "return-lock:" + name in self.output
            else phase == "RETURN" and not self.held_plane
        )
        return (lock, True, True, None)

    def motion(self, efforts):
        require(efforts is self.efforts and len(efforts) == len(self.route), "Foreign winding vector")
        if self.bound_coils is not None:
            self.efforts[:] = [Q(0)] * len(self.route)
            for coil in self.bound_coils:
                self.efforts[coil.index] += coil.effort
        attached, routes = self.connected_pairs()
        force = dict.fromkeys((n for n in self.pose_names if n not in attached), Q(0))
        for fi, route in zip(efforts, routes):
            require(abs(fi) <= Q(11, 5), "Individual signed current exceeds its physical leaf bound")
            if route is not None:
                force[route[0]] += route[1] * fi
        require(
            all(
                n in self.pose_names[: self.driven] and abs(v) <= VMAX
                for n, v in self.disturbance.items()
            ),
            "Uninstalled disturbance or excess effort",
        )
        for n, d in self.disturbance.items():
            force[n] += d
        eforces = []
        for i, (j, amplitude) in enumerate(self.local_drive):
            require(self.held_plane or (j == -1 and amplitude == 0), "Unpaid local actuator access")
            n = None if j < 0 else attached.get(self.pose_names[j], self.pose_names[j])
            f = Q(amplitude) * min(1, self.E[i]) if n is not None else Q(0)
            if n is not None:
                force[n] += f
            eforces.append((n, f, min(1, self.E[i]) if amplitude and n is not None else Q(0)))
        require(
            all(
                n in self.pose_names[: self.driven] and abs(f) <= seat.PILOT_REACTION
                for n, f in self.pilot.items()
            ),
            "Uninstalled pilot or exceeded added reaction",
        )
        pforces = {n: q * min(1, self.U) for n, q in self.pilot.items()}
        for n, f in pforces.items():
            force[n] += f
        blocked = self.jammed | {carrier for n, carrier in attached.items() if n in self.jammed}
        theta, c = self.held_law if self.held_plane else (self.threshold, self.compliance)
        require(theta >= 0 and 0 < c <= 2, "Invalid material stroke law")
        vel = {}
        for name, f in force.items():
            cap = 1 if name == "cam" else VMAX
            v = min(cap, max(0, (f - theta) / c)) - min(cap, max(0, (-f - theta) / c))
            locked, pos, neg, key = self.geometry(name)
            if locked or name in blocked or (v > 0 and not pos) or (v < 0 and not neg):
                v = Q(0)
            x = self.positions[name]
            if name == "cam":
                if self.output["normal-cam-stops"] if self.held_plane else self.carriage.normal:
                    for j in range(26):
                        if (
                            self.positions[name] == j * self.p["SEGMENT"] + self.p["GUARD"]
                            and not self.output[f"cam-stop:{j}"]
                        ):
                            v = Q(0)
                if key is not None and x == key * 13 * self.p["SEGMENT"] and v < 0:
                    v = Q(0)
            elif (x == 0 and v < 0) or (x == self.limits[name] and v > 0):
                v = Q(0)
            vel[name] = v
        vel.update({n: vel[a] for n, a in attached.items()})
        rows = []
        for n, f, h in eforces:
            w = f * vel[n] if n is not None else Q(0)
            rows.append(
                dict(
                    draw=2 * max(w, 0) + h,
                    returned=max(-w, 0) / 2,
                    heat=max(w, 0) + max(-w, 0) / 2 + h,
                    work=w,
                )
            )
        wpos = sum((max(f * vel[n], 0) for n, f in pforces.items()), Q(0))
        wneg = sum((max(-f * vel[n], 0) for n, f in pforces.items()), Q(0))
        holding = sum((seat.PILOT_REACTION * min(1, self.U) for q in self.pilot.values() if q), Q(0))
        phase = (2 * wpos + holding, wneg / 2, wpos + wneg / 2 + holding)
        returns = tuple(Q(0) if r is None else r[1] * vel[r[0]] for r in routes)
        external = sum(f * v for f, v in zip(efforts, returns)) + sum(
            f * vel[n] for n, f in self.disturbance.items()
        )
        heat = sum(f * vel[n] for n, f in force.items())
        require(
            heat >= 0 and heat == external + wpos - wneg + sum(r["work"] for r in rows),
            "Actual stop or its conjugate work projection was lost",
        )
        return dict(
            velocities=vel,
            banks=rows,
            pilot=phase,
            mechanical_dissipation=heat,
            external_input_power=external,
            force=force,
            return_velocities=returns,
        )

    def measured_strobe(self):
        if self.held_plane:
            return "held"
        require(self.sampler.remaining == 0, "No genuine sample root")
        if self.U < seat.PRICE:
            # A due root can exhaust the local cell without acquiring a new reading.
            paid = self.U
            self.sampler.remaining = self.sampler.period
            self.sampler.samples += 1
            self.sampler.work += paid
            self.U -= paid
            self.heat += paid
            self.check_U_balance()
            return "unfunded"
        return super().sample(self.motion(self.efforts)["force"]["abort"])

    def sample(self, pressure):
        if self.held_plane or self.U < seat.PRICE:
            return self.measured_strobe()
        actual = self.motion(self.efforts)["force"]["abort"]
        require(
            Q(pressure) == actual, "A reported or earlier pressure is not the current mechanical port"
        )
        return super().sample(actual)

    def _commit(self, request):
        if request.kind == "hold" and request.target == "seat-pulse" and self._valid_entry(request):
            self.return_force = self.motion(self.efforts)["force"]["abort"]
        return super()._commit(request)

    def advance(self, cells, capture, dt, **ports):
        """Exact plateau on a fixed chart. Other elapsed histories use the held-flow theorem."""
        dt = Q(dt)
        require(self.positions["abort"] == self.carriage.position, "Duplicate carriage state")
        actual = self.endpoint_ports()
        require(
            all(ports.get(n) == values for n, values in actual.items()),
            "Clock chart uses a foreign cut or supply",
        )
        at = self.motion(self.efforts)
        for coord, v in at["velocities"].items():
            on_chart = coord in ("cam", "blend", "abort") or (
                self.held_plane and coord in ("reset0", "reset1")
            )
            require(
                not v or on_chart, "Use the original boundary solver for moving bank/authority contacts"
            )
        pre = src.held_rates(self, cells, capture, mechanical=self.motion, efforts=self.efforts, **ports)
        for b, (e, rate) in enumerate(zip(self.E, pre["E"])):
            if not self.held_plane and self.trips[b].enabled and e > self.p["EOFF"]:
                require(e + dt * rate >= self.p["EOFF"], "Split at the true Eoff trip")
        before = self.keeper
        if self.carriage.phase in ("NORMAL", "ENTERING") and at["velocities"]["abort"] != 0:
            raise ValueError("Use the inherited oriented NORMAL/ENTERING boundary solver")
        for n in ("cam", "blend"):
            v = at["velocities"][n]
            if n == "cam" and v < 0:
                _, _, _, k = self.geometry(n)
                if k is not None:
                    gap = (self.positions[n] - k * 13 * self.p["SEGMENT"]) % self.limits[n]
                    require(-dt * v <= gap, "Split at the keeper detent")
            if (
                n == "cam"
                and v != 0
                and (self.output["normal-cam-stops"] if self.held_plane else self.carriage.normal)
            ):
                circumference = self.limits["cam"]
                sign = 1 if v > 0 else -1
                stops = [
                    j * self.p["SEGMENT"] + self.p["GUARD"]
                    for j in range(26)
                    if not self.output[f"cam-stop:{j}"]
                ]
                if not self.held_plane:
                    stops.extend(
                        j * self.p["SEGMENT"] + h
                        for j in range(26)
                        for h in (Q(self.p["SEGMENT"], 4), Q(3 * self.p["SEGMENT"], 4))
                    )
                distances = [((point - self.positions[n]) * sign) % circumference for point in stops]
                require(
                    all(dt * abs(v) <= gap for gap in distances if gap > 0),
                    "Split at a true cam contact",
                )
        electrical = coil_plan(self, at, dt) if self.bound_coils is not None else None
        received = electrical[2] if electrical is not None else None
        law = src.constant_arc(
            self,
            cells,
            capture,
            dt,
            mechanical=self.motion,
            efforts=self.efforts,
            receiver_winding=received,
            **ports,
        )
        if electrical is not None:
            self.electrical_trace = pay_coils(electrical)
        self.carriage.position = self.positions["abort"]
        if not self.held_plane:
            self.keeper = g.keeper(before, self.positions["blend"], self.p["BLEND_LIMIT"])
            self.refresh_surviving_levels()
        return law


class Coil:
    """One stored directional current with an actual funding bank and a fixed mechanical receiver."""

    def __init__(self, donor, bank, target, index, direction, initial, node_voltages):
        self.donor = donor
        self.bank = bank
        self.target = target
        self.index = index
        self.sign = direction
        self.current = Q(initial)
        self.v_s, self.v_r = map(Q, node_voltages)
        require(
            direction in (-1, 1)
            and 0 <= self.current <= 3
            and 0 <= self.v_s <= 300
            and 0 <= self.v_r <= 300,
            "Invalid winding or retained capacitor voltage",
        )

    @property
    def effort(self):
        return self.sign * K * self.current

    def plateau(self, receiver_velocity):
        # A steady finite branch of the two physical series limiters and winding.
        # Both existing capacitor voltages are inputs from the prestate.
        x = self.current
        vs = self.v_s
        vr = self.v_r
        r = Q(1, 10000)
        need = 100 * x + 14 + self.sign * K * receiver_velocity
        require(
            x > 0 and need == vr and 299 <= vr <= 300,
            "Use the full electrical flow when the actual winding current is evolving",
        )
        line = (vs - vr) / (2 * r)

        def shunt(v):
            return 1000 * max(0, v - Q(2999, 10))

        require(abs(line) <= 5 and line == x + shunt(vr) + vr / 1000, "Receiving capacitor is evolving")
        drive = line + shunt(vs) + vs / 1000
        u = vs + r * drive
        require(abs(drive) <= 5 and Q(599, 2) <= u <= 300, "No stationary upstream full-drive source")
        source_loss = r * drive**2 + r * line**2 + vs * shunt(vs) + vs**2 / 1000
        receiver_loss = r * line**2 + vr * shunt(vr) + vr**2 / 1000
        winding_heat = 100 * x * x + 14 * x
        shaft = self.effort * receiver_velocity
        wire = (vs + vr) * line / 2
        require(
            u * drive == source_loss + wire
            and wire == receiver_loss + vr * x
            and vr * x == winding_heat + shaft,
            "Unequal physical work at a matched terminal",
        )
        return u * drive, source_loss, wire, receiver_loss + winding_heat, shaft, winding_heat


def bind_fields(host, coils):
    require(host.bound_coils is None, "Installation cannot replace a live field roster")
    entries = {}
    hosts = {}
    neighbors = tuple(
        (host.owner + i) % (6 * (12 * (6 + 2**98) + 2)) for i in (*range(-20, 0), *range(1, 21))
    )
    for coil in coils:
        require(
            coil.target is host
            and isinstance(coil.donor, src.Fixture)
            and hosts.setdefault(coil.donor.owner, coil.donor) is coil.donor,
            "Foreign field target or donor clone",
        )
        require(type(coil.index) is int and 0 <= coil.index < len(host.route), "No such field terminal")
        leaf = coil.index // host.driven
        require(
            leaf < 80 and coil.donor.owner == neighbors[leaf // 2] and coil.bank == leaf % 2,
            "Donor bank or fixed physical winding destination mismatch",
        )
        key = (coil.index, coil.sign)
        require(key not in entries, "A winding occurs twice")
        entries[key] = coil
    host.bound_coils = tuple(entries.values())
    host.efforts[:] = [Q(0)] * len(host.route)
    for c in host.bound_coils:
        host.efforts[c.index] += c.effort


def layout(host):
    ports = src.old_module("port_model.py")
    cells = tuple(
        ports.Slot(src.BankPort(host, b), price=Q(20480), recharge_time=2 * src.DELTA) for b in (0, 1)
    )
    # Already funded ready cells and true empty/current-parent states can be
    # part of a supplied material cut, never an inference from the gate flag.
    for c in cells:
        c.charge = c.price
    remote = src.ThermalZone(host.zone_capacity, host.bath)
    n = 6 * (12 * (6 + 2**98) + 2)
    raw = src.RawCapture(n, host.owner, 1, "auxiliary", 0, 0, remote)
    raw.energy = Q(1024)
    return cells, raw


def fixture(p, up, phase, z, cam, keeper=0, upstream=None):
    h = JoinedSeat(p, up, keeper, upstream=upstream)
    h.zone_capacity = Q(up["thermal"]["thermal_capacity"])
    h.bath = Q(up["thermal"]["passive_bath_coefficient"])
    tc = Q(up["point"]["per_bank_transit_capacity"])
    cap = Q(p["EMAX"])
    h.E[:] = [cap / 2, 0] if keeper == 0 else [0, cap / 2]
    h.T[:] = [tc, 0] if keeper == 0 else [0, tc]
    h.positions["cam"] = Q(cam)
    h.positions["abort"] = Q(z)
    h.carriage.position = Q(z)
    h.carriage.phase = phase
    h.carriage.normal = phase == "NORMAL"
    h.carriage.full = phase in ("FULL", "RETURN")
    h.carriage.active = phase != "NORMAL"
    h.refresh_surviving_levels()
    return h


def recoil_checks(p, up):
    h = fixture(p, up, "RETURN", 100, 1)
    # Coherent held takeover while a genuine 68 effort is routed to a clamped shaft.
    dest = h.pose_names.index("reset1")
    require(
        h.submit("local-actuator", 0, (dest, 68)) == "local-actuator/held-plane", "No genuine held drive"
    )
    at = h.motion(h.efforts)
    raw = g.actuator_rates(h, h.efforts)["banks"][0]
    require(
        raw["draw"] == Q(753, 5) and at["banks"][0]["draw"] == 1 and at["velocities"]["reset1"] == 0,
        "Pasting posthoc locks failed to distinguish the E debit",
    )
    cells, caprow = layout(h)
    h.advance(cells, caprow, src.DELTA, **h.endpoint_ports())
    require(h.submit("hold", "return-lock:reset1", 0) == "held", "Wrong explicit pole")
    h.pilot["reset1"] = Q(-1, 1000)
    at = h.motion(h.efforts)
    require(
        at["velocities"]["reset1"] == VMAX and at["pilot"] == (Q(1, 1000), Q(11, 20000), Q(31, 20000)),
        "The existing E actuator did not backdrive the separately paid U pilot",
    )
    law = h.advance(cells, caprow, src.DELTA, **h.endpoint_ports())
    require(law["Urefund"] == Q(11, 20000), "Missing returned U work on the common flow")
    # A jam removes genuine motion from both converters without erasing their holding draw.
    h.submit("jam", "reset1", True)
    require(h.motion(h.efforts)["banks"][0]["draw"] == 1, "Jammed E torque was charged as moving")
    # Failure can bypass a real seat at zero, but cannot use a stale unrelated scalar.
    c = fixture(p, up, "RETURN", 0, 1)
    c.return_force = -68
    require(
        c.submit("hold", "seat-pulse", 1) == "held-no-seat",
        "Previous force manufactured fresh inward pressure",
    )
    return True


def sample_checks(p, up):
    # Both orders of a ready clock and an independently paid placement override.
    # At the true zero-stop C_0 holds; existing 34 negative windings supply pressure.
    for change_first in (False, True):
        h = fixture(p, up, "RETURN", 0, 0, upstream=seat.PRICE)
        for j in range(34):
            h.efforts[(2 * j) * h.driven + h.pose_names.index("abort")] = -2
        h.sampler.remaining = 0
        if change_first:
            result = h.submit("hold", "trip0", 0)
            require(
                result == "held"
                and h.sampler.strobe() == "held"
                and h.carriage.phase == "RETURN"
                and h.U == seat.PRICE - 2 * g.UPDATE_WORK,
                "False tied funded seat",
            )
        else:
            require(
                h.sampler.strobe() == "normal-seat" and h.carriage.phase == "NORMAL" and h.U == 0,
                "True funded contact lost in opposite order",
            )
            require(
                h.submit("hold", "trip0", 0) == "partial-work/no-gate-change" and not h.held_plane,
                "Empty U granted a tied takeover",
            )
        h.check_U_balance()
    h = fixture(p, up, "RETURN", 0, 1, upstream=4095)
    h.sampler.remaining = 0
    h.return_force = -2
    before = h.output.copy()
    require(
        h.sampler.strobe() == "unfunded"
        and h.sampler.work == 4095
        and h.U == 0
        and h.return_force == -2
        and h.output == before
        and h.sampler.clock_rate() == 0,
        "Partial work read fresh pressure, reset material outputs or re-enabled its own clock",
    )
    z = fixture(p, up, "RETURN", 0, 1)
    z.return_force = -68
    token = z.submit("hold", "seat-pulse", 1, defer=True)
    require(
        z.settle(token) == "held-no-seat" and z.settle(token) == "no-pending-right",
        "Old update borrowed an earlier measured pressure or acted twice",
    )
    return True


def detent_checks(p, up):
    h = fixture(p, up, "FULL", 10000, Q(1, 2))
    # Working fixture can use nominal received effort before physical takeover.
    shaft = h.pose_names.index("cam")
    h.prepark = (True, False)
    for j in range(34):
        h.efforts[(2 * j) * h.driven + shaft] = -2
    require(h.motion(h.efforts)["velocities"]["cam"] == -1, "Unparked FULL cam did not begin rewinding")
    h.submit("hold", "normal-cam", 0)
    require(
        h.motion(h.efforts)["velocities"]["cam"] == -1,
        "Unrelated takeover clamped the cam at its current angle",
    )
    cells, raw = layout(h)
    h.advance(cells, raw, Q(1, 2), **h.endpoint_ports())
    require(
        h.positions["cam"] == 0 and h.motion(h.efforts)["velocities"]["cam"] == 0,
        "The retained keeper detent did not park the cam",
    )
    # Same physical stop, different keeper. At a FULL blend-end event select
    # the new keeper without rotating the actual cam or zeroing its currents.
    k = fixture(p, up, "FULL", 10000, Q(1, 2))
    k.prepark = (True, True)
    k.positions["blend"] = p["BLEND_LIMIT"] - Q(11, 20)
    sb = k.pose_names.index("blend")
    for j in range(34):
        k.efforts[(2 * j) * k.driven + shaft] = -2
        k.efforts[(2 * j) * k.driven + sb] = 2
    ks, kr = layout(k)
    k.advance(ks, kr, Q(1, 2), **k.endpoint_ports())
    require(
        k.keeper == 1 and k.positions["cam"] == 0 and k.motion(k.efforts)["velocities"]["cam"] == -1,
        "Keeper change reset the pose or retained the obsolete stop",
    )
    for phase, start in (("ENTERING", Q(1, 2)), ("NORMAL", Q(p["GUARD"]))):
        z = fixture(p, up, phase, 0, start)
        for j in range(34):
            z.efforts[(2 * j) * z.driven + shaft] = 2
        require(z.motion(z.efforts)["velocities"]["cam"] == 0, "Expected an actual stopped cam")
        z.submit("hold", "trip0", 0)
        require(z.motion(z.efforts)["velocities"]["cam"] == 0, "Unaddressed fixed cam stop vanished")
        if phase == "NORMAL":
            z.submit("hold", "cam-stop:0", 1)
            require(z.motion(z.efforts)["velocities"]["cam"] == 1, "Held open predecessor cannot move")
    return True


def coil_plan(target, local, dt):
    """Read all actual endpoints first. Rejection leaves every owner at the old cut."""
    banks = {}
    send_loss = {}
    sending = {}
    gross = loss = shaft = wire = winding_heat = Q(0)
    for c in target.bound_coils:
        e, sh, transfer, rh, w, wh = c.plateau(local["return_velocities"][c.index])
        ds = banks.setdefault(c.donor, [Q(0), Q(0)])
        ds[c.bank] += e
        send_loss[c.donor] = send_loss.get(c.donor, Q(0)) + sh
        sending[c.donor] = sending.get(c.donor, Q(0)) + transfer
        gross += e
        loss += rh
        shaft += w
        wire += transfer
        winding_heat += wh
    donor_steps = []
    for f, loads in banks.items():
        gauge = f.endpoint_ports()
        check_power = gauge["cpu_enabled"]
        require(
            f.now == target.now and f.U >= 1 and not f.held_plane,
            "Need a matched, funded plateau supplier",
        )
        require(
            all(t == f.Tcap * conn for t, conn in zip(f.T, gauge["chi"])), "Donor transit is evolving"
        )
        inlet = sum(Q(41, 10) * t for t in f.T)
        ee = [4 * t - load - k * e for t, load, k, e in zip(f.T, loads, gauge["bleed"], f.E)]
        require(
            f.U - 2 * inlet * dt >= 1 and (f.held_plane or dt <= f.sampler.remaining),
            "Split at donor supply or clock event",
        )
        require(
            all(
                not load
                or (
                    awake
                    and f.positions[f"act{b}:0"] >= f.p["DRIVER_AT"]
                    and min(e, e + dt * delta) > f.p["EOFF"]
                )
                for b, (load, awake, e, delta) in enumerate(zip(loads, check_power, f.E, ee))
            ),
            "A requested electrical source has lost its true donor driver",
        )
        require(
            all(k == 0 or delta == 0 for k, delta in zip(gauge["bleed"], ee))
            and all(0 <= e + dt * delta <= f.p["EMAX"] for e, delta in zip(f.E, ee)),
            "Donor stock boundary",
        )
        heat = inlet + sum(f.T) / 10 + sum(k * e for k, e in zip(gauge["bleed"], f.E))
        donor_steps.append((f, sending[f], inlet, ee, heat + send_loss[f]))
    total_heat = sum(send_loss.values()) + loss
    require(gross == total_heat + shaft and wire == loss + shaft, "Unmatched capacitor/shaft rates")
    return (
        dt,
        donor_steps,
        (wire, loss, shaft),
        tuple(dt * x for x in (gross, total_heat, shaft, winding_heat)),
    )


def pay_coils(plan):
    dt, donor_steps, _, totals = plan
    for f, transfer, inlet, ee, heat in donor_steps:
        if not f.held_plane:
            f.sampler.flow_clock(dt)
        f.U -= 2 * inlet * dt
        f.non_gate_withdrawals += 2 * inlet * dt
        for b, v in enumerate(ee):
            f.E[b] += dt * v
        f.zone.advance(dt, heat)
        f.zone.cross_out += dt * transfer
        f.now += dt
        f.check_U_balance()
    return totals


def wound_rebound(p, up):
    """One time interval including sender, winding and target material zones."""
    h = fixture(p, up, "RETURN", Q(10000) - VMAX, Q(1, 2))
    cells, raw = layout(h)
    target_initial = h.U + sum(h.E) + sum(h.T) + sum(s.charge for s in cells)
    n = 6 * (12 * (6 + 2**98) + 2)
    neighbors = tuple((h.owner + i) % n for i in (*range(-20, 0), *range(1, 21)))
    tc = Q(up["point"]["per_bank_transit_capacity"])
    cap = Q(p["EMAX"])
    catalog = {}
    coils = []
    vr = 100 * Q(57, 20) + 14 + K * VMAX
    line = Q(57, 20) + vr / 1000
    vs = vr + 2 * Q(1, 10000) * line
    for j, o in enumerate(neighbors[:34]):
        donor = src.Fixture(p, up, o, h.Ucap / 2, (cap / 2, 0), (tc, 0))
        donor.positions["act0:0"] = p["WARM_AT"]
        donor.positions["cut1"] = p["CUT_LIMIT"]
        donor.positions["shunt1"] = p["ISO_LIMIT"]
        donor.trips[1].transition(0, p["EOFF"], p["EON"], zero=True)
        catalog[o] = donor
        coils.append(
            Coil(donor, 0, h, 2 * j * h.driven + h.pose_names.index("abort"), 1, Q(57, 20), (vs, vr))
        )
    # This raw cut has one actual pending local strobe at its observation origin.
    # It is not 34 simultaneously issued claims or a result-conditioned sample.
    bind_fields(h, coils)
    h.sampler.remaining = Q(0)
    require(
        h.sampler.strobe() == "observed" and not h.keys[0],
        "Winding pressure failed the wrong-key branch",
    )
    law = h.motion(h.efforts)
    v = law["velocities"]["abort"]
    dt = Q(1)
    require(v == VMAX and len(catalog) == 34, "Expected 34 real donors on the outward shaft")
    Cs = Cr = Q(1, 10000)
    sender_caps = {o: sum(Cs * c.v_s**2 / 2 for c in coils if c.donor is f) for o, f in catalog.items()}

    def target_fields():
        return sum(c.current**2 + Cr * c.v_r**2 / 2 for c in coils)

    target_initial += target_fields()
    donor_before = {o: s.U + sum(s.E) + sum(s.T) + sender_caps[o] for o, s in catalog.items()}
    target_arc = h.advance(cells, raw, dt, **h.endpoint_ports())
    paid, all_line_heat, shaft, winding_heat = h.electrical_trace
    for o, donor in catalog.items():
        require(
            donor.now == h.now
            and donor.zone.accounted(donor.U + sum(donor.E) + sum(donor.T) + sender_caps[o])
            == {0: donor_before[o] - donor.zone.cross_out},
            "Unmatched donor bath or electrical export",
        )
    require(
        target_arc["field"] * dt == shaft
        and h.carriage.position == h.carriage.length
        and h.sampler.strobe() == "rebound"
        and h.carriage.phase == "FULL",
        "No charged full-stop event",
    )
    after = h.U + sum(h.E) + sum(h.T) + sum(s.charge for s in cells) + target_fields()
    require(
        h.zone.accounted(after) == {0: target_initial + sum(s.zone.cross_out for s in catalog.values())}
        and h.sampler.work == 2 * seat.PRICE,
        "Receiver shaft or sampler heat was not in its actual zone",
    )
    require(
        paid == all_line_heat + shaft
        and winding_heat + shaft == Q(14525633, 500)
        and winding_heat == Q(289731, 10),
        "Power at the receiver winding and upstream funding port incorrectly identified",
    )
    return paid, all_line_heat, shaft


def pilot_budget():
    # Even allowing one independent active pilot effort per *named* pose; the
    # physical source uses at most one on each independent driven coordinate.
    cap = Q(335) * seat.PILOT_REACTION * (2 * VMAX + 1)
    # The enlargement of the one existing sampler slot was priced at 2^31
    # per q. Keep EVERY extra physical descriptor at its full raw ceiling.
    # Extra normal per-strobe work consumes the actual sampler root bound.
    surplus = (seat.PRICE - g.PREDICATE_WORK) * (g.RATE - 1)
    require(cap == Q(134, 125) and cap < surplus, "Added pilot draw exceeds real paid headroom")
    for length in (Q(0), src.DELTA, Q(1, 7), Q(1), Q(17, 3), Q(10**7)):
        extra = seat.PRICE - g.PREDICATE_WORK
        require(
            extra * (1 + floor(length)) + cap * length <= extra * (1 + g.RATE * length),
            "New left-edge strobe or sustained pilot work exceeded the retained envelope",
        )
    th = g.parameters()[2]["thermal"]
    extra_heat = 335 * seat.PILOT_REACTION * (1 + 2 * VMAX)
    require(
        Q(th["nominal_primitive_peak_fit_upper"]) + 41 * (Q(687859, 20) + extra_heat) < 15 * 2**96,
        "A real thermal boundary exceeded its hard gross-work allowance",
    )
    return cap


def check():
    p, _, up = g.parameters()
    stored = src.at("7bce24369d3a7c31331704bb3c7038fac0e4374e", "portability/a80_return_seat.py")
    current = Path(seat.__file__).read_bytes().replace(b"\r\n", b"\n")
    require(stored.replace(b"\r\n", b"\n") == current, "A80 amendment changed; rebind the source")
    require(
        recoil_checks(p, up) and detent_checks(p, up) and sample_checks(p, up),
        "Integrated gate comparison failed",
    )
    gap = 2 * (28 - VMAX - seat.PILOT_REACTION)
    require(
        gap == Q(26899, 500) and Q(8313448, 225) / gap == Q(166268960, 242091),
        "Surviving force reversal variation was miscounted",
    )
    work, heat, shaft = wound_rebound(p, up)
    point = pilot_budget()
    print(
        f"Matched two E actuators, pilot U and both capacitor nodes; 34 donor electrical work {work}, complete lead and winding heat {heat}, shaft work {shaft}"
    )
    print(
        f"Paid fresh full-stop rebound; maximum added pilot U draw {point}/q fits the installed sampler envelope"
    )


if __name__ == "__main__":
    if not __debug__ or sys.version_info[:2] != (3, 12):
        raise SystemExit("Use unoptimized Python 3.12")
    check()

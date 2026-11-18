"""Eighty-body sampled return completion on A-prime's actual frozen instruction family."""

import argparse
import ast
import hashlib
import json
import math
import sys
from fractions import Fraction as Q
from pathlib import Path

import a_prime_source_assembly as source


gate = source.gate
HERE = source.HERE
B_SEAT = "f90a57d119286ca90aa245e902c59fad27aa1890"
PRICE = 4096
EXTRA_BLOCKS = 192
PILOT_REACTION = Q(1, 1000)
DELTA = Q(101, 100)
VMAX = Q(11, 10)


def need(condition, detail):
    if not condition:
        raise AssertionError(detail)


def record(commit, path):
    return json.loads(source.at(commit, path).decode("utf-8-sig"))


def replace_once(text, old, new):
    need(text.count(old) == 1, "Changed source adapter anchor")
    return text.replace(old, new)


class Text:
    def __init__(self, body):
        self.body = body

    def read_text(self, encoding):
        return self.body


def compile_images():
    isa = source.old_module("program_model.py")
    p, g, upstream = gate.parameters()
    design = dict(g["design"])
    design["physical_parameters"] = tuple(map(tuple, design["physical_parameters"]))
    design = isa.Design(**design)
    original = gate.frozen("program_source.py")
    isa.SOURCE = Text(original)
    old = isa.Compiler(design).compile()
    oldbound = isa.WorkBound(old).report()
    image_hash = lambda c: hashlib.sha256(
        b"".join(n.to_bytes(24, "little") for n in c.image)
    ).hexdigest()
    need(image_hash(old) == g["compiler"]["encoded_image_sha256"], "Wrong full-size original image")

    # Reuse the priced predecessor return-lease source transformation. Do not
    # import B's private allocation, geometry constants or one-body admission.
    seed = source.at(B_SEAT, "portability/abort_protocol_alternative.py").decode("utf-8-sig")
    mod = ast.Module(
        body=[
            f
            for f in ast.parse(seed).body
            if isinstance(f, ast.FunctionDef) and f.name in ("replace_once", "edited")
        ],
        type_ignores=[],
    )
    env = {"need": need}
    exec(compile(mod, "<pinned return lease>", "exec"), env)
    body = env["edited"](original)
    hole = "        w[base + RANK_VALID] = 0\n\n\ndef helper(t):"
    body = replace_once(body, hole, hole.replace("\n\n\n", "\n        clear_target(base)\n\n\n"))
    hole = "                w[base + RANK_VALID] = 0\n                emit(t, MODE_PORT, cold, 0, FORCE)"
    body = replace_once(
        body,
        hole,
        hole.replace("                emit", "                clear_target(base)\n                emit"),
    )
    start = original.index("def contact(")
    zero = original[start : original.index("def clear_target(", start)].replace(
        "def contact(", "def contact_zero("
    )
    zero = zero.replace("key, 1)", "key, 0)")
    wrong = """def geometry_wrong(t, anchor, active):
    b = 1 - anchor
    return contact_zero(t, BLEND_AT_A + anchor) or contact_zero(t, ISO_SEATED_A + b) or contact_zero(t, SHUNT_SEATED_A + b) or contact_zero(t, CUT_OPEN_A + b) or (active and contact_zero(t, ACT_ZERO_A + b * BAYS + active - 1)) or contact_zero(t, CLAMP_OPEN_A + b) or contact_zero(t, RESET_OPEN_A + b) or contact_zero(t, CAM_ENTRY_A + anchor)

"""
    body = replace_once(body, "def clear_target(", zero + wrong + "def clear_target(")
    body = replace_once(
        body,
        "    if ready and contact(t, CAM_ENTRY_A + anchor):",
        "    if ready and contact(t, ISO_SEATED_A + cold) and contact(t, SHUNT_SEATED_A + cold) and contact(t, CAM_ENTRY_A + anchor):",
    )
    body = replace_once(
        body,
        "        emit(t, REWIND_PORT, cold, 0, FORCE)\n    return 0",
        "        emit(t, REWIND_PORT, cold, 0, FORCE)\n    if w[base + EXITING_ABORT]:\n        return geometry_wrong(t, anchor, active)\n    return 0",
    )
    body = replace_once(
        body, "        abort_action(t, base)", "        wrong_for_old = abort_action(t, base)"
    )
    hole = "        if old_exit:\n            emit(t, MODE_PORT, cold, 0, -FORCE)\n        if w[base + EXITING_ABORT]:"
    body = replace_once(
        body,
        hole,
        "        if old_exit:\n            if wrong_for_old:\n                emit(t, MODE_PORT, cold, 0, FORCE)\n            else:\n                emit(t, MODE_PORT, cold, 0, -FORCE)\n        if w[base + EXITING_ABORT]:",
    )
    isa.SOURCE = Text(body)
    base_bounds = isa.WorkBound

    class Bounds(base_bounds):
        def limit(self, fn, node):
            return super().limit("contact" if fn == "contact_zero" else fn, node)

    new = isa.Compiler(design).compile()
    bound = Bounds(new).report()
    cert = isa.processing_certificate(new, bound)
    need(
        new.constants == old.constants and new.constants["BAYS"] == 80 and new.constants["QUORUM"] == 7,
        "Wrong roster or changed memory constants",
    )
    need(
        bound["padded_frame_upper"] == oldbound["padded_frame_upper"]
        and bound["stack_depth"] == oldbound["stack_depth"]
        and bound["private_words_with_metadata"] + 648 <= 32768
        and len(new.nodes) <= 8192,
        "Physical image or job budget exceeded",
    )
    return (
        isa,
        new,
        bound,
        cert,
        p,
        g,
        upstream,
        dict(
            old_image=image_hash(old),
            new_image=image_hash(new),
            old_cells=len(old.nodes),
            new_cells=len(new.nodes),
            old_registers=old.next_register,
            new_registers=new.next_register,
            active=bound["active_frame_upper"],
            padded=bound["padded_frame_upper"],
            helper=bound["instruction_upper_bounds"]["helper"],
            private_plus_receiver=bound["private_words_with_metadata"] + 648,
            stack_depth=bound["stack_depth"],
        ),
    )


def compiled_case(isa, c, bound, *, half, bad, old_exit, qualified, unavailable=False):
    k = c.constants
    cold = 1 - half
    ports = isa.RawPorts(c)
    m = isa.Machine(c)
    m.W[:] = [0] * len(m.W)
    v = isa.populated_view(c, half, 0, 1)
    for anchor in (0, 1):
        v[k["ANCHOR_IS_A"] + anchor] = v[k["BLEND_AT_A"] + anchor] = v[k["CAM_ENTRY_A"] + anchor] = int(
            anchor == half
        )
    for fld in (
        "ISO_SEATED_A",
        "SHUNT_SEATED_A",
        "CUT_OPEN_A",
        "POWER_OFF_A",
        "CLAMP_OPEN_A",
        "RESET_OPEN_A",
    ):
        v[k[fld] + cold] = 1
    for j in range(80):
        v[k["ACT_ZERO_A"] + cold * 80 + j] = 1
    v[k["MODE"]] = v[k["NORMAL_STOP"]] = 0
    v[k["ABORT_FULL"]] = 1
    is_act = type(bad) is int
    if is_act:
        loc = k["ACT_ZERO_A"] + cold * 80 + bad
    elif bad is None:
        loc = None
    else:
        loc = k[bad] + (half if bad in ("CAM_ENTRY_A", "BLEND_AT_A") else cold)
    if loc is not None:
        v[loc] = isa.WORD_MASK if unavailable else 0
    ports.set_view(0, v)
    z = k["TARGET_BASE"]
    m.W[z + k["STAGE_ID"]] = 27
    m.W[z + k["EXITING_ABORT"]] = int(old_exit)
    if is_act and qualified:
        m.W[z + k["ABORT_SIGNATURE"]] = k["ACT_PORT"] + k["PORTS"] * (cold + 2 * bad)
    m.enter("helper", (0,))
    need(
        m.run(ports, budget=bound["instruction_upper_bounds"]["helper"] + 32, until_yield=False)
        == "halt",
        "No actual helper return",
    )
    packet = next(e[2:] for e in reversed(ports.events) if e[0] == "command")
    wanted = -20 if bad is None or (old_exit and unavailable) else 20
    need(
        packet[0] == 26
        and packet[3] == wanted
        and bool(m.W[z + k["EXITING_ABORT"]]) == (old_exit or bad is None),
        "Retained owner or MODE sign changed",
    )
    if is_act and qualified:
        need(tuple(packet[4:]) == (k["ACT_PORT"], bad, -20), "Wrong physical body selected")
    if bad is not None and not qualified:
        need(packet[4] == 0, "Fresh ACTION bypassed its signature wait")
    return dict(
        half=half,
        bad=bad,
        old_exit=old_exit,
        qualified=qualified,
        unavailable=unavailable,
        packet=packet,
        instructions=m.steps,
    )


class SeatClock(gate.PredecessorSampler):
    def strobe(self):
        return self.state.sample(self.state.return_force)


class ReturnFixture(source.Fixture):
    """The target's fresh-seat and signed-rewind mechanism, with its one actual U."""

    def __init__(self, p, up, keeper, upstream=None, *, threshold=Q(29), compliance=Q(2)):
        need(28 <= threshold <= 29 and 0 < compliance <= 2, "Outside the source stroke parameters")
        self.threshold = Q(threshold)
        self.compliance = Q(compliance)
        super().__init__(
            p,
            up,
            0,
            up["point"]["new_upstream_capacity"] if upstream is None else upstream,
            (0, 0),
            (0, 0),
        )
        self.keeper = keeper
        self.positions["blend"] = keeper * p["BLEND_LIMIT"]
        cold = 1 - keeper
        for tag in ("iso", "shunt", "cut"):
            self.positions[f"{tag}{cold}"] = self.limits[f"{tag}{cold}"]
        self.positions["cam"] = keeper * 13 * p["SEGMENT"]
        self.keys = (False, False)
        self.prepark = (False, False)
        self.strong = (False, False)
        self.last_seat_source = None
        # Physical failure controls are installed in this fixture rather than
        # transmitted by an ordinary command/ISA operation.
        self.return_force = Q(0)
        self.lock_names = tuple(
            f"return-lock:{n}" for n in tuple(self.positions)[: self.driven] if n not in ("abort", "cam")
        )
        self.new_controls = (
            "direction-out",
            "direction-in",
            "seat-pulse",
            "rewind-detent",
            *self.lock_names,
        )
        need(len(self.new_controls) <= EXTRA_BLOCKS, "Not enough actual local control slots")
        self.gates = (*self.gates, *(gate.Gate(n, "return-pole", None) for n in self.new_controls))
        self.output.update(dict.fromkeys(self.new_controls, 0))
        old = self.sampler
        self.sampler = SeatClock(self, old.period, old.remaining)
        self.refresh_surviving_levels()

    def refresh_surviving_levels(self):
        super().refresh_surviving_levels()
        if self.held_plane or not hasattr(self, "new_controls"):
            return
        inside = self.carriage.phase == "RETURN"
        self.output["direction-out"] = int(inside and not self.keys[self.keeper])
        self.output["direction-in"] = int(inside and self.keys[self.keeper])
        self.output["rewind-detent"] = int(self.carriage.phase in ("FULL", "RETURN"))
        self.output["seat-pulse"] = 0
        for name in self.lock_names:
            self.output[name] = int(inside)

    def _commit(self, request):
        if request.kind == "hold" and request.target == "seat-pulse" and self._valid_entry(request):
            self.held_plane = True
            car = self.carriage
            if (
                request.value & 1
                and car.phase == "RETURN"
                and car.position == 0
                and self.return_force < -self.threshold
                and "abort" not in self.jammed
            ):
                car.phase = "NORMAL"
                car.normal = True
                car.active = car.full = False
                self.output["abort"] = car.raw()
                self.output["normal-cam"] = 1
                return "held-false-seat"
            return "held-no-seat"
        return super()._commit(request)

    def sample(self, pressure):
        if self.held_plane:
            return "held"  # No nominal sampler sees the failed plane's concentrated forces.
        need(abs(pressure) <= 176 + VMAX + PILOT_REACTION, "Outside rated true mode effort")
        need(self.sampler.remaining == 0, "No genuine local sample")
        self.return_force = Q(pressure)
        self.sampler.remaining = self.sampler.period
        amount = min(self.U, PRICE)
        self.sampler.samples += 1
        self.sampler.work += amount
        self.U -= amount
        self.heat += amount
        self.check_U_balance()
        if amount != PRICE:
            return "unfunded"
        raw = gate.physical_contact_snapshot(self)
        pred, _ = gate.fold_contact_snapshot(raw, 80)
        for j, bit in enumerate(pred):
            self.output[f"cam-stop:{j}"] = int(bit)
        keys = []
        pre = []
        strong = []
        for a in (0, 1):
            b = 1 - a
            ports = (
                raw["blend", a],
                self.positions[f"iso{b}"] == self.limits[f"iso{b}"],
                self.positions[f"shunt{b}"] == self.limits[f"shunt{b}"],
                raw["cut-end", b],
                pred[13 * a + 1],
                raw["clamp-zero", b],
                raw["reset-zero", b],
            )
            geom = all(ports)
            pre.append(geom and raw["low-E", b])
            keys.append(geom and raw["cam-entry", a])
            strong.append(keys[-1] and raw["low-E", b])
        self.prepark, self.keys, self.strong = tuple(pre), tuple(keys), tuple(strong)
        car = self.carriage
        a = self.keeper = gate.keeper(self.keeper, self.positions["blend"], self.p["BLEND_LIMIT"])
        need(self.positions["abort"] == car.position, "Carriage position has an alias")
        result = "observed"
        if "abort" not in self.jammed:
            if car.phase == "RETURN" and car.position == 0 and strong[a] and pressure < -self.threshold:
                car.phase = "NORMAL"
                car.active = car.full = False
                car.normal = True
                result = "normal-seat"
                self.last_seat_source = (self.now, a)
            elif (
                car.phase == "RETURN"
                and car.position == car.length
                and not keys[a]
                and pressure > self.threshold
            ):
                car.phase = "FULL"
                car.active = car.full = True
                result = "rebound"
            elif (
                car.phase == "FULL"
                and car.position == car.length
                and strong[a]
                and pressure < -self.threshold
            ):
                car.phase = "RETURN"
                result = "depart"
        self.output["abort"] = car.raw()
        self.output["normal-cam"] = int(car.normal)
        self.refresh_surviving_levels()
        return result

    def cleanup_port(self, name, effort, free_velocity):
        """Apply the actual receiver-side lock to the original shaft effort-flow port."""
        need(name in tuple(self.positions)[: self.driven] and name != "abort", "Unknown cleanup output")
        need(
            abs(free_velocity) <= VMAX
            and abs(effort) <= len(self.route) * Q(11, 5) + 2 * 68 + VMAX + PILOT_REACTION,
            "Unrated cleanup shaft",
        )
        if self.held_plane:
            locked = bool(
                self.output["rewind-detent"] if name == "cam" else self.output["return-lock:" + name]
            )
        else:
            locked = self.carriage.phase == "RETURN"
        v = Q(0) if locked or name in self.jammed else Q(free_velocity)
        return v, effort * v, (-effort if locked or name in self.jammed else Q(0))

    def interior_move(self, force, dt, *, failed_law=None):
        # Supplied constant genuine signed shaft force on this subarc. All other
        # selected motion coordinates are blocked in RETURN; no coil state is erased.
        car = self.carriage
        if self.held_plane:
            threshold, compliance = failed_law or (self.threshold, self.compliance)
            need(threshold >= 0 and 0 < compliance <= 2, "Invalid held passive stroke law")
            cap = len(self.route) * Q(11, 5) + 2 * 68 + VMAX + PILOT_REACTION
        else:
            need(failed_law is None, "Held physical failure needs its real takeover root")
            threshold, compliance = self.threshold, self.compliance
            cap = 176 + VMAX + PILOT_REACTION
        need(
            car.phase == "RETURN"
            and dt >= 0
            and self.sampler.clock_rate() * dt <= self.sampler.remaining
            and abs(force) <= cap,
            "Wrong subarc, force, or missing paid strobe",
        )
        self.return_force = Q(force)
        old = car.position
        out = bool(self.output["direction-out"]) if self.held_plane else not self.keys[self.keeper]
        inward = bool(self.output["direction-in"]) if self.held_plane else self.keys[self.keeper]
        speed = min(VMAX, max(0, (abs(force) - threshold) / compliance))
        if "abort" not in self.jammed:
            if force > 0 and out:
                car.position = min(car.length, old + speed * dt)
            if force < 0 and inward:
                car.position = max(0, old - speed * dt)
        self.positions["abort"] = car.position
        self.sampler.flow_clock(dt)
        self.now += dt
        work = force * (car.position - old)
        need(work >= 0, "Pawl generated work")
        self.mechanical_input += work
        self.mechanical_heat += work
        return car.position - old

    def rewind(self, force, dt):
        car = self.carriage
        need(
            car.phase == "FULL"
            and not self.held_plane
            and self.sampler.clock_rate() * dt <= self.sampler.remaining
            and dt >= 0
            and abs(force) <= 176 + Q(11, 10) + PILOT_REACTION,
            "Wrong rewind arc",
        )
        c = self.limits["cam"]
        entry = self.keeper * 13 * self.p["SEGMENT"]
        gap = (self.positions["cam"] - entry) % c
        speed = min(1, max(0, (-force - self.threshold) / self.compliance))
        travel = min(gap, dt * speed) if self.prepark[self.keeper] and "cam" not in self.jammed else 0
        self.positions["cam"] = (self.positions["cam"] - travel) % c
        self.sampler.flow_clock(dt)
        self.now += dt
        self.mechanical_input -= force * travel
        self.mechanical_heat -= force * travel
        return travel


def seat_checks(p, up):
    denied = 0
    for a in (0, 1):
        for j in range(80):
            # One independent, legal observation cut per missing body. Actual
            # intervening coordinates do not jump on a constructed trajectory.
            fixture = ReturnFixture(p, up, a)
            b = 1 - a
            c = fixture.carriage
            c.phase = "RETURN"
            c.active = c.full = True
            c.normal = False
            fixture.positions[f"act{b}:{j}"] = 1
            fixture.interior_move(0, 1)
            need(
                fixture.sample(-68) == "observed" and c.phase == "RETURN",
                "Missing activation admitted NORMAL",
            )
            denied += 1
        fixture = ReturnFixture(p, up, a)
        c = fixture.carriage
        c.phase = "RETURN"
        c.active = c.full = True
        c.normal = False
        fixture.interior_move(0, 1)
        need(fixture.sample(-68) == "normal-seat", "Genuinely keyed endpoint failed to seat")
    fixture = ReturnFixture(p, up, 0)
    c = fixture.carriage
    c.phase = "RETURN"
    c.active = c.full = True
    c.normal = False
    c.position = c.length - Q(1, 2)
    fixture.positions["abort"] = c.position
    fixture.positions["cam"] = Q(1, 2)
    fixture.interior_move(0, 1)
    need(
        fixture.sample(68) == "observed" and fixture.interior_move(Q(68), 1) == Q(1, 2),
        "Unready state did not reach full stop",
    )
    need(fixture.sample(68) == "rebound" and c.phase == "FULL", "No physical full-stop capture")
    need(fixture.rewind(-68, 1) == Q(1, 2), "Failed to acquire off-entry stop")
    need(fixture.sample(-68) == "depart" and fixture.positions["cam"] == 0, "Rewind missed keyed stop")
    low = ReturnFixture(p, up, 1, PRICE - 1)
    c = low.carriage
    c.phase = "RETURN"
    c.normal = False
    c.full = c.active = True
    low.keys = (False, True)
    low.interior_move(0, 1)
    need(low.sample(-68) == "unfunded" and c.phase == "RETURN", "Stale direction minted a fresh seat")
    obj = ReturnFixture(p, up, 0)
    c = obj.carriage
    c.phase = "RETURN"
    c.active = c.full = True
    c.normal = False
    obj.positions["cam"] = 1
    obj.return_force = Q(-68)
    need(
        obj.cleanup_port("act1:79", Q(68), 1) == (0, 0, -68),
        "Loaded interior port escaped the housing stop",
    )
    need(
        obj.submit("hold", "seat-pulse", 1) == "held-false-seat"
        and c.phase == "NORMAL"
        and obj.positions["cam"] == 1,
        "A physical-site failure was made semantically harmless",
    )
    obj2 = ReturnFixture(p, up, 0)
    obj2.carriage.phase = "RETURN"
    obj2.carriage.full = obj2.carriage.active = True
    obj2.carriage.normal = False
    need(
        obj2.submit("hold", "return-lock:act1:79", 0) == "held"
        and obj2.cleanup_port("act1:79", Q(68), 1) == (1, 68, 0),
        "Held failure silently kept the extra actuator lock healthy",
    )
    need(
        obj2.sample(Q(30000)) == "held"
        and obj2.submit("hold", "direction-out", 1) == "held"
        and obj2.interior_move(Q(30000), Q(1, 11), failed_law=(Q(0), Q(1))) == Q(1, 10),
        "Whole-plane failure lost its actual concentrated drive",
    )
    return dict(
        held_concentrated_drive_preserved=True,
        all_missing_ACT_inputs_refused=denied,
        explicit_both_keepers=True,
        held_false_seat=True,
        stale_key_low_U_refused=True,
        old_circular_point_sampler_countercase="cam(0)=1/2, v=-1, integer samples miss point entry perpetually",
    )


def budgets(isa, c, bound, cert, p, geometry, up):
    k = c.constants
    old = geometry["timing"]
    port = record(gate.FROZEN, "local-control/port_source_results.json")
    schedule = port["return_schedule"]
    first_gate = record(source.SOURCE, "portability/gate_source_completion_results.json")["bounds"]
    f = Q(cert["frame_max"])
    fmin = Q(cert["frame_min"])
    J = Q(cert["per_target_response"])
    age = Q(cert["pose_age"])
    old_R = Q(old["settle"])
    need(
        (f, age, J) == (Q(1114113, 1048576), 1953, 11 * f),
        "Altered programme has a different timing carrier",
    )
    stage = (k["POST_STAGE_FRAMES"] + 1) * f + J
    R = max(old_R, age + 2 * stage + 2 * J + 15)
    W = age + f + 2 * J + 15 + 1
    diff = R - old_R
    S = lambda l: R + Q(l)
    C = lambda l: R + Q(l) / Q(9, 10)
    # Retained integer code thresholds/guard on the new helper's *actual* bound.
    A = Q(cert["functional_guard_horizon"])
    load = Q(3, 2) * (1 - Q(k["LOAD_MARGIN"], 1000) + Q(1, 100)) + Q(273, 4194304) * A
    clearance = Q(1, 5) - Q(k["ISOLATION_MARGIN"], 1000) + Q(1, 100) + Q(1, 10) + Q(11, 400000) * A
    need(load < 1 and clearance < Q(1, 5), "Possible factual-pressure or clearance violation")
    pose_error = Q(cert["raw_pose_measurement_error"]) + VMAX * (
        age + Q(cert["comparison_to_emission"]) + Q(cert["cut_withdrawal"])
    )
    need(
        k["CLAMP_VERIFY_RADIUS"] >= 2 * pose_error
        and k["JOIN_ERROR"] >= k["CLAMP_VERIFY_RADIUS"] + pose_error,
        "Source clamp comparisons require a new margin",
    )
    need(
        Q(p["GUARD"]) == 16000
        and R < k["SEGMENT"] / Q(4)
        and C(k["SEGMENT"]) < 50000
        and R < k["RESET_LIMIT"] / VMAX,
        "Changed response no longer fits phase4/first deadband/probe",
    )
    need(
        6 * Q(22, 5) + Q(11, 10) + PILOT_REACTION < 28
        and 68 - 6 * Q(22, 5) - Q(11, 10) - PILOT_REACTION - 29 > 2,
        "Force supplier lost stiction or unit speed",
    )
    # First aperture is separate from raw issuer observations. Original boot already includes ENTRY.
    boot = Q(cert["new_bank_entry_before_driver_geometry"])
    birth = boot + stage + J + 15 + 60 + DELTA
    need(
        birth < Q(100000, 11) and (k["POST_STAGE_FRAMES"] - 1) * fmin > W + J,
        "Full stroke / NORMAL posthold no longer covers a formed issuer",
    )
    work = Q(old["timer_window"])
    h = k["HIGH_STEP"]
    spans = list(map(Q, old["rank_spans"]))
    floored = tuple(int(m // h) + 1 for m in spans)
    old_bins = tuple(math.ceil(m / h) + 1 for m in spans)
    savings = sum((a - b) * work for j, (a, b) in enumerate(zip(old_bins, floored)) if j != 4)
    need(
        savings == 12 * work and all((b - 1) * h <= m < b * h for b, m in zip(floored, spans)),
        "Invalid closed rank bin",
    )
    need(
        work == Q(cert["local_nontransferable_work"]),
        "Inconsistent local time scale",
    )
    # These are ACTUAL numbers of occurrences of S/C/last-settle in the bound formulas.
    half_multiplicity = (3, 80, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 0)
    n_half = sum(half_multiplicity) + 13
    n_abort = 2 + 1 + 3 + 80 + 1 + 1 + 1 + 1
    need((n_half, n_abort) == (109, 90), "Omitted a true settle cost")
    half = Q(schedule["half_cycle"]) + n_half * diff + 13 * DELTA
    generic = 2 * W + Q(schedule["abort"]) + n_abort * diff + 60 + 5 * (R + DELTA)
    # Thirteen old band allowances and original phase4, PLUS an additional complete fresh4 + band.
    partial = (
        Q(old["partial"]) - savings + 14 * diff + S(k["RESET_LIMIT"]) + C(k["SEGMENT"]) + 14 * DELTA
    )
    entering = W + stage + R + 10000 + DELTA
    rebound = W + R + 10000 + DELTA
    qualified = 60 + 2 * R + 10000 + 2 * DELTA
    short_normal = R + R / Q(9, 10) + 5 * (C(k["SEGMENT"]) + DELTA) + S(k["RESET_LIMIT"]) + DELTA
    short_full = (
        2 * W + S(k["BLEND_LIMIT"]) + S(k["RESET_LIMIT"]) + S(26 * k["SEGMENT"]) + 5 * (R + DELTA) + 60
    )
    quick = short_normal + entering + short_full + qualified
    quiet = 2 * quick + 2
    banks = 2 * k["DEGREE"]
    exposure = 2 * banks
    stripe = (exposure + 1) * quiet
    spacing = Q(k["POWER_AT"]) / VMAX
    need(
        stripe < spacing and short_normal < Q(old["earliest_timeout"]), "Quiet interval / timeout failed"
    )
    H = Q(10456118540836)
    rate = Q(schedule["original_raw_acquisition_rate"])
    total = (
        50000
        + partial
        + max(entering, rebound)
        + generic
        + qualified
        + quick
        + stripe
        + 2 * half
        + Q(old["old_suffix"])
    )
    need(total < H and 3 + math.floor(3 + 2 * H * rate) == 6, "Fixed A-prime H or old raw rate lost")
    # Recheck the changed nominal phase costs against the original minimum timer.
    phasevals = {int(n.split("_")[0]): Q(val) for n, val in schedule["phase_bounds"].items()}
    bounded_short = max(
        phasevals[j] + half_multiplicity[j] * diff + C(k["SEGMENT"]) + DELTA
        for j in range(13)
        if j not in (1, 8)
    )
    long = Q(old["healthy_long_stage_milestone"]) + 81 * diff
    need(
        bounded_short < Q(old["earliest_timeout"]) and long < Q(old["earliest_timeout"]),
        "Normal phase or serial ACT milestone now misses actual earliest timeout",
    )
    need(
        Q(k["POWER_AT"]) / VMAX > Q(cert["complete_scan"]) + R
        and Q(geometry["geometry"]["post_driver_overlap"]) > work,
        "A genuine least-candidate scan and actual driver handoff no longer fit",
    )
    extra = EXTRA_BLOCKS * 1024 + PRICE - 2048
    bits = first_gate["mode_descriptor_bits"]
    prior = up["point"]["receiver"]["consumed_raw_padding"]
    need(
        prior + bits + extra <= up["point"]["receiver"]["available_raw_padding"],
        "Additional fixture descriptors alias an existing field",
    )
    old_point = up["point"]
    U = Q(old_point["new_upstream_capacity"])
    D = Q(first_gate["new_upstream_rate_upper"])
    B = Q(first_gate["new_upstream_burst"]) + 2 * extra
    need(
        D == Q(old_point["upstream_rate"]) and U - B - 2 * D > PRICE,
        "Same U supply does not buy the gates",
    )
    # The original 502-input strobe already folds both all-zero banks.
    # New taps, truth/pressure logic and up to two writes per extra local pilot have distinct prices.
    cap = 502 + 488 + 28 + 502 + 256 + 8 + 128 + 2 * EXTRA_BLOCKS
    need(cap <= PRICE, "Claimed new strobe costs more than its uptake")
    return dict(
        R=R,
        wash=W,
        phase4_and_band=S(k["RESET_LIMIT"]) + C(k["SEGMENT"]),
        new_full_entry_birth=birth,
        minimum_full_stroke=Q(100000, 11),
        posthold=(k["POST_STAGE_FRAMES"] - 1) * fmin,
        rank_span=spans,
        old_bin_count=old_bins,
        sharp_bin_count=floored,
        savings=savings,
        normal_multiplicity=n_half,
        abort_multiplicity=n_abort,
        partial=partial,
        fresh_half=half,
        generic_FULL=generic,
        entering=entering,
        rebound=rebound,
        qualified_return=qualified,
        short_normal=short_normal,
        short_full=short_full,
        quick=quick,
        quiet_epoch=quiet,
        worst_exposures=exposure,
        stripe=stripe,
        true_same_bank_spacing=spacing,
        additional_soft_exposures_that_fit=math.ceil(spacing / quiet) - 1 - (exposure + 1),
        total=total,
        H=H,
        strict_slack=H - total,
        returned_cover=6,
        unchanged_rate=rate,
        changed_functional_horizon=A,
        upper_load=load,
        upper_clearance_deficit=clearance,
        short_stage_upper=bounded_short,
        long_ACT_milestone_upper=long,
        new_descriptors=EXTRA_BLOCKS,
        new_or_repurposed_bits=extra,
        strobe_work_upper=cap,
        host_U_cap=U,
        host_U_rate=D,
        host_U_burst=B,
        host_U_floor=U - B - 2 * D,
        normal_source_G1_G2_closed=False,
    )


def produce():
    isa, c, b, cert, p, g, up, meta = compile_images()
    scenarios = [
        dict(half=0, bad=0, old_exit=True, qualified=True),
        dict(half=1, bad=79, old_exit=True, qualified=True),
        dict(half=0, bad=79, old_exit=True, qualified=False, unavailable=True),
        dict(half=1, bad="ISO_SEATED_A", old_exit=False, qualified=False),
        dict(half=0, bad="SHUNT_SEATED_A", old_exit=True, qualified=False),
        dict(half=0, bad=None, old_exit=False, qualified=False),
    ]
    return dict(
        checker_sha256=hashlib.sha256(Path(__file__).read_bytes().replace(b"\r\n", b"\n")).hexdigest(),
        frozen_A=gate.FROZEN,
        inherited_gate=source.SOURCE,
        return_lease_source=B_SEAT,
        image=meta,
        physical=seat_checks(p, up),
        time_and_resources=budgets(isa, c, b, cert, p, g, up),
        branches=[compiled_case(isa, c, b, **row) for row in scenarios],
        scoped_conditional_itinerary=True,
        all_mode_A80_family_admitted=False,
    )


def plain(x):
    if isinstance(x, Q):
        return str(x)
    if isinstance(x, (tuple, list)):
        return [plain(v) for v in x]
    if isinstance(x, dict):
        return {k: plain(v) for k, v in x.items()}
    return x


if __name__ == "__main__":
    if not __debug__ or sys.version_info[:2] != (3, 12):
        raise SystemExit("Use unoptimized Python 3.12")
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--write", action="store_true")
    modes.add_argument("--check", action="store_true")
    args = parser.parse_args()
    record_path = HERE / "a80_return_seat_results.json"
    data = json.dumps(plain(produce()), sort_keys=True, indent=2) + "\n"
    if args.write:
        record_path.write_text(data, encoding="utf-8", newline="\n")
    else:
        need(data == record_path.read_text(encoding="utf-8"), "A80 amended-source check changed")
    print("PASS A80 compiled conditional return and fixed-H budget; whole family open")

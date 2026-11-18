"""One-body mechanical catalogue, sampled releases and post-handoff source ports.

A finite mathematical operation adapter. Scope and unimplemented joins are
specified in THRESHOLD-GATE-SOURCE.md. Use unoptimized Python 3.12.
"""
from __future__ import annotations
import argparse
from dataclasses import dataclass
from fractions import Fraction as Q
from types import MappingProxyType
import json
from pathlib import Path
import subprocess
import sys

import cam_reformation as cam
import gate_source_completion as gates
import input_lifecycle as inputs
import parent_retirement as retirement
import threshold_design as design
import threshold_field_source as field

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
BASE = "52a2eab8261543b1c113d51111eadc8170d09c44"
INPUT_BASE = "318b343be4953f8ec58121ac1785b121c17794d2"
PREFIX = "theories-and-designs/byzantine-control/portability/"
PULSE_ROOTS = tuple(row["right"] for row in cam.BANDS)
INPUT_ROOTS = tuple(right for _, _, right, _ in inputs.MODES)
MODE_ROOTS = tuple(sorted(set(PULSE_ROOTS) | set(INPUT_ROOTS)))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def record(name):
    return json.loads((HERE / name).read_text(encoding="utf-8-sig"))


def parameters(compiled):
    p, _, _ = gates.parameters()
    for name in ("CLAMP_LIMIT", "WARM_AT", "POWER_AT", "CUT_LIMIT", "RESET_LIMIT", "BLEND_LIMIT", "SEGMENT"):
        p[name] = compiled.constants[name]
    p.update(B=compiled.constants["BAYS"], D=compiled.constants["DEGREE"],
             WRITER_CUTOFF=cam.CUTOFF, DRIVER_AT=cam.DRIVER)
    require(p["B"] == 1 and p["D"] == 40, "Threshold physical dimensions differ")
    require(p["WRITER_CUTOFF"] == design.CLAMP_CUTOFF and
            p["DRIVER_AT"] == p["POWER_AT"]+design.VECTOR_DRIVER_OFFSET,
            "Threshold contacts have another geometry")
    return p


def catalogue(p):
    template, poses, driven = gates.catalogue(p)
    blocks = [g for g in template if g.family != "writer"]
    require(len(blocks) == 81, "Unexpected old private-writer interface")
    for side in (0, 1):
        blocks.append(gates.Gate(f"field-clutch:{side}", "incoming-field", f"clamp{side}", cam.CUTOFF, side))
        for root in MODE_ROOTS:
            blocks.append(gates.Gate(f"reset-rail:{side}:{int(root)}", "outgoing-reset", f"clamp{side}", root, side))
        for name, level in (("receiver-arm", cam.ARM), ("vector-driver", cam.DRIVER)):
            blocks.append(gates.Gate(f"{name}:{side}", name, f"act{side}:0", level, side))
    blocks.extend((gates.Gate("rewind-direction", "abort-routing", "cam"),
                   gates.Gate("rewind-entry:0", "abort-park", "cam", Q(0), 0),
                   gates.Gate("rewind-entry:1", "abort-park", "cam", 13*p["SEGMENT"], 1)))
    require(len({g.name for g in blocks}) == len(blocks) == 112, "Duplicated or missing contact")
    return tuple(blocks), poses, driven


@dataclass(frozen=True)
class PhaseRails:
    field: int
    raw_input: int


def reset_rails(p, *, normal, cam_position, side, clamp):
    """Source contact input; None retains ordinary/previous ownership.

    Only the selected cold side at the physical phase-six work circuit can
    advance the outgoing reformation bands. Existing source-to-endpoint
    delays and already captured mode jobs still apply after selection.
    """
    require(type(normal) is bool and type(side) is int and side in (0, 1), "Malformed physical contact")
    position = cam.exact(cam_position)
    clamp = cam.exact(clamp)
    require(0 <= position < 26*p["SEGMENT"] and 0 <= clamp <= cam.CLAMP_END,
            "Outside installed cam/clamp geometry")
    band = (1-side)*13+6
    work = gates.cam_band_values(position, band, p, normal)
    results = set()
    for enabled in work:
        if not enabled:
            results.add(None)
        else:
            input_mode = next((m for m, _, right, _ in inputs.MODES if clamp < right), inputs.OPEN)
            results.add(PhaseRails(cam.contact(clamp), input_mode))
    return frozenset(results)


class SharedContacts:
    """Predecessor sampler view of *existing* host U and two actual CPU E cells.

    Pose arrays are the mechanical variables of this local fixture. The
    operating balances are read-only projections. No second E is installed.
    Positive gate work on U is transferred into fixture heat exactly once.
    """
    def __init__(self, p, owner, source_work, machines, *, initial_driver=None):
        require(isinstance(source_work,inputs.SourceWork) and source_work.origin == owner,
                "Wrong physical U owner")
        require(len(machines) == 2 and all(isinstance(m,retirement.RetirableParent) for m in machines)
                and machines[0].bank is not machines[1].bank and machines[0].setter is not machines[1].setter
                and machines[0].fabric is not machines[1].fabric, "Expected distinct operating banks, setters and route fabrics")
        self.p, self.owner, self.source_work = p, owner, source_work
        for side,machine in enumerate(machines):
            if hasattr(machine.bank,"owner"):
                require(machine.bank.owner==(owner,side),"Operating E belongs to another host or side")
        self.machines = tuple(machines)
        self.installed_source_ports = {}
        self.blocks, self.limits, self.driven = catalogue(p)
        self.positions = {name: Q(0) for name in self.limits}
        self.output = {block.name: 0 for block in self.blocks}
        self.route=[(index%self.driven,1) for index in range(2*p["D"]*self.driven)]
        self.local_drive=[(-1,0),(-1,0)]
        self.detached=set()
        self.cleanup_sample = (False, False)
        self.rewind_sample = (False, False)
        self.keeper = 0
        self.abort_carrier = gates.Abort(Q(p["ABORT_LIMIT"]))
        self.output["normal-cam"]=int(self.abort_carrier.normal)
        self.held_plane, self.jammed = False, set()
        self.escrow = {(side, kind):field.WorkCell(Q(8),Q(0)) for side in (0,1) for kind in ("arm","driver")}
        self.heat = self.gate_work = self.mechanical_input = self.mechanical_heat = Q(0)
        self.initial_driver = initial_driver
        self.initial_route_stock = Q(0)
        if initial_driver is not None:
            require(type(initial_driver) is int and initial_driver in (0,1), "Invalid initial serving bank")
            self.escrow[initial_driver,"driver"] = field.WorkCell(Q(8),Q(8))
            self.initial_route_stock = Q(8)
            self.output[f"vector-driver:{initial_driver}"] = 1

    def abort_arc(self, velocity, duration):
        require(not self.held_plane and self.positions["abort"]==self.abort_carrier.position,
                "No surviving coherent abort carrier")
        velocity,duration=cam.exact(velocity),cam.exact(duration)
        require(duration>=0 and abs(velocity)<=cam.VMAX,"Invalid abort drive arc")
        if duration==0:
            # This operator supplies a material arc. A numerical force at a
            # singleton time supplies no displacement or completed departure.
            return []
        # Even the NORMAL -> ENTERING latch consumes actual motion. A jam
        # removes the motion input while all independent source clocks can run.
        actual_velocity=Q(0) if "abort" in self.jammed else velocity
        events=self.abort_carrier.advance(actual_velocity,duration,self.cleanup_sample[self.keeper])
        self.positions["abort"]=self.abort_carrier.position
        self.output["abort"]=self.abort_carrier.raw()
        self.output["normal-cam"]=int(self.abort_carrier.normal)
        return events

    def blend_arc(self, position, duration):
        position,duration=cam.exact(position),cam.exact(duration)
        require(0<=position<=self.p["BLEND_LIMIT"] and duration>=0 and
                abs(position-self.positions["blend"])<=cam.VMAX*duration,"Invalid monotone blend arc")
        require("blend" not in self.jammed or position==self.positions["blend"],"A jammed blend cannot move")
        self.positions["blend"]=position
        if not self.held_plane:
            self.keeper=gates.keeper(self.keeper,position,self.p["BLEND_LIMIT"])

    def check_rigid_seats(self):
        for side in (0,1):
            seat=f"seat{side}:0"
            require(seat in self.detached or self.positions[seat]==self.positions[f"carrier{side}"],
                    "Attached seat and actual carrier disagree")

    def carrier_arc(self, side, position, duration):
        require(type(side) is int and side in (0,1),"Invalid carrier side")
        self.check_rigid_seats()
        position,duration=cam.exact(position),cam.exact(duration)
        carrier,seat=f"carrier{side}",f"seat{side}:0"
        delta=position-self.positions[carrier]
        require(duration>=0 and 0<=position<=self.limits[carrier] and abs(delta)<=cam.VMAX*duration,
                "Invalid carrier arc")
        blocked=carrier in self.jammed or (seat not in self.detached and seat in self.jammed)
        require(not blocked or delta==0,"A jammed rigid assembly cannot move")
        self.positions[carrier]=position
        if seat not in self.detached:
            self.positions[seat]=position

    @property
    def normal(self):
        return bool(self.output["normal-cam"]) if self.held_plane else self.abort_carrier.normal

    @property
    def E(self):
        return tuple(m.bank.stock for m in self.machines)

    @property
    def U(self):
        return self.source_work.stock

    @U.setter
    def U(self, new):
        amount = self.U - new
        require(amount >= 0 and self.source_work.debit(amount), "Unfunded fixture update")
        self.gate_work += amount

    def check_U_balance(self):
        require(self.heat+sum(cell.stock for cell in self.escrow.values()) == self.initial_route_stock+self.gate_work and self.source_work.spent >= self.gate_work and self.U >= 0,
                "Unmatched fixture heat or U debit")

    def held_takeover(self, block, value):
        """The dedicated physical site update port, disjoint from every ISA address."""
        require(type(value) is int and value in (0, 1), "One physical contact bit required")
        require(block in {"vector-driver:0","vector-driver:1","field-clutch:0","field-clutch:1"},
                "This operation is only the physical vector/clutch override port")
        required = gates.UPDATE_WORK * (1 + int(not self.held_plane))
        paid = min(self.U, Q(gates.UPDATE_WORK)) if self.U < required else Q(required)
        self.U -= paid
        self.heat += paid
        self.check_U_balance()
        if paid < required:
            return "partial/no-change"
        self.held_plane = True
        self.output[block] = value
        return "held"


    def physical_pose_request(self, request):
        """Actual capture and cost law for a held pose route or existing-E actuator.

        The bounded installed namespace is the ordinary shaft/pose catalogue.
        A field-bit endpoint is not implicitly converted into a mechanical pose.
        """
        require(isinstance(request,gates.Captured) and request.owner==self.owner,
                "Foreign fixture update")
        indexed=(type(request.target) is int and 0<=request.target<len(self.route))
        tagged=(type(request.value) is tuple and len(request.value)==2)
        valid=(request.kind=="route" and indexed and tagged and type(request.value[0]) is int
               and -1<=request.value[0]<len(self.positions) and type(request.value[1]) is int
               and request.value[1] in (-1,1))
        if request.kind=="local-actuator":
            valid=gates.Completion._valid_local_drive(self, request)
        material_change=request.kind in ("jam","detach")
        if material_change:
            valid=(type(request.target) is str and request.target in self.positions and type(request.value) is bool
                   and (request.kind=="jam" or request.target.startswith("seat")))
        price=gates.UPDATE_WORK*(1+int(valid and not material_change and not self.held_plane))
        paid=Q(price) if self.U>=price else min(self.U,Q(gates.UPDATE_WORK))
        self.U-=paid;self.heat+=paid;self.check_U_balance()
        if paid<price:
            return "partial/no-change"
        if not valid:
            return "uninstalled"
        if material_change:
            return gates.Completion._commit(self,request)
        self.held_plane=True
        if request.kind=="route":
            self.route[request.target]=request.value
        else:
            self.local_drive[request.target]=request.value
        return "held-pose-update"


class CapturePort:
    """Transient selected source wire; stores no return, grant or energy."""
    cut=False
    valid_slot=staticmethod(field.PulseSelector.valid_slot)

    def __init__(self,pulse):
        self.pending=pulse.pending
        self.trigger_energy=pulse.trigger_energy


@dataclass(frozen=True)
class InitialPulseRow:
    """An installed transmitting aperture and its receiving control line at time zero."""
    pulse: field.PulseSelector
    control: cam.ControlLine


class LiveSourceBank:
    """One common local source strobe route, with the installed endpoint rows.

    The positive fixture uses one actual cam handoff; several fixed endpoint
    rows can share this very bank gate and setter. No receive-end status line
    is consulted to authorize the local source sampler. Each channel retains
    its own paid aperture and independently retained packets/motor.
    """
    def __init__(self, fixture, side, dispatcher, endpoint, setter_control, additional_rows=()):
        self._bind_bank(fixture,side,setter_control)
        rows=[]
        for sender, target in ((dispatcher,endpoint), *additional_rows):
            h=sender.ordinary_handoff
            require(type(h) is cam.PulseHandoff and h.pulse is sender.p and h.setter is sender.s is self.setter
                    and h.control is sender.line and h.resident is sender.resident,
                    "Actual transferred row and source setter required")
            rows.append((target,h))
        require(self.activation == dispatcher.activation == cam.DRIVER, "Inconsistent actual handoff pose")
        require(self.machine.powered and not dispatcher.p.cut, "No actual source opening event")
        self.cut = False
        self._install(rows,Q(0))
        self._grant("driver")
        for e,row in self.rows.items():
            if not self._reserve_quench(row.pulse.reset_source_reserve,self.row_quench[e]):
                row.pulse.cut=True
                row.pulse.reset_control_inhibit=True
        if not self._reserve_quench(self.setter.reset_reserve,self.setter_quench):
            self.setter.cut=True
            self.setter.reset_control_inhibit=True
        fixture.output[f"vector-driver:{side}"] = int(self.gate)

    @property
    def activation(self):
        return self.fixture.positions[f"act{self.side}:0"]

    def _bind_bank(self, fixture, side, setter_control):
        require(type(side) is int and side in (0,1), "Unknown source bank")
        require(side not in fixture.installed_source_ports, "This bank already has an installed source gate")
        require(type(setter_control) is cam.ControlLine, "Actual bank-local setter control required")
        self.fixture, self.side = fixture, side
        self.machine = fixture.machines[side]
        self.setter = self.machine.setter
        self.setter_control = setter_control
        self.native_input = None

    def wire_input(self, source):
        require(self.native_input is None and isinstance(source,inputs.LocalSourceBank) and
                source.origin==self.fixture.owner and source.bank==self.side and
                source.payer is self.fixture.source_work and source.energy is self.machine.bank,
                "Native input and contacts must use the same host U and bank E")
        self.native_input=source

    def _install(self, rows, entry_stock):
        installed = {}
        pulse_ids = {id(r.pulse) for b in self.fixture.installed_source_ports.values() for r in b.rows.values()}
        for endpoint, row in rows:
            require(type(endpoint) is field.Destination and endpoint.body in self.setter.targets and
                    type(endpoint.bank) is int and endpoint.bank in (0,1) and type(endpoint.bit) is int
                    and 0 <= endpoint.bit < field.L, "Uninstalled physical endpoint")
            require(type(row.pulse) is field.PulseSelector and type(row.control) is cam.ControlLine
                    and row.control is not self.setter_control, "Separate pulse and receiver control required")
            require(endpoint not in installed and id(row.pulse) not in pulse_ids,"Duplicated aperture or physical pulse")
            installed[endpoint]=row
            pulse_ids.add(id(row.pulse))
        require(installed,"Empty source row installation")
        self.rows=MappingProxyType(installed)
        self.row_quench={e:field.WorkCell(Q(8),entry_stock) for e in installed}
        self.setter_quench=field.WorkCell(Q(8),entry_stock)
        self.initial_quench = (len(installed)+1)*entry_stock
        self.local_switch_debit=self.local_switch_heat=Q(0)
        self.fixture.installed_source_ports[self.side]=self

    @classmethod
    def at_initial(cls, fixture, side, source, setter_control, rows):
        """Elaborate the initial physical product. Re-entry uses the ordinary causal operations."""
        bank=cls.__new__(cls)
        bank._bind_bank(fixture,side,setter_control)
        require(fixture.initial_driver is not None and fixture.gate_work==0 and not fixture.held_plane
                and fixture.normal,"Expected an intact time-zero fixture")
        active=side==fixture.initial_driver
        bank.wire_input(source)
        require(source.powered==bank.machine.powered==active and source.admission==active and
                bank.activation==(cam.WARM if active else 0) and bank.gate==active
                and fixture.positions[f"cut{side}"]==(0 if active else fixture.p["CUT_LIMIT"])
                and bank.setter.cut==bank.setter.reset_control_inhibit==(not active),"Wrong initial gate or setter")
        rows=tuple(rows)
        mode=10 if active else 0
        require(setter_control.words==[mode]*8 and all(setter_control.valid),"Wrong initial setter control")
        for _,row in rows:
            require(type(row) is InitialPulseRow and row.pulse.cut==row.pulse.reset_control_inhibit==(not active)
                    and row.control.words==[mode]*8 and all(row.control.valid),"Wrong initial aperture")
        bank.cut=not active
        bank._install(rows,Q(8) if active else Q(0))
        bank.switch_balance()
        fixture.check_U_balance()
        return bank

    @property
    def arm(self):
        return self.fixture.escrow[self.side,"arm"].stock == 8

    @property
    def gate(self):
        return self.fixture.escrow[self.side,"driver"].stock == 8

    def _grant(self, kind):
        cell = self.fixture.escrow[self.side, kind]
        if cell.stock == 8:
            return True
        if cell.stock or self.fixture.U < 32:
            return False
        self.fixture.U -= 32
        self.fixture.heat += 24
        cell.stock = Q(8)
        cell.delivered_input += 8
        self.fixture.check_U_balance()
        return True

    def _quench(self, kind):
        cell = self.fixture.escrow[self.side,kind]
        residual = cell.stock
        cell.debit(residual)
        self.fixture.heat += residual
        self.fixture.check_U_balance()

    def switch_balance(self):
        retained=sum(cell.stock for cell in self.row_quench.values())+self.setter_quench.stock
        require(retained+self.local_switch_heat==self.initial_quench+self.local_switch_debit,
                "Endpoint switching parcel was duplicated or lost")

    def _reserve_quench(self, payer, cell):
        if cell.busy:
            return False
        if cell.stock==8:
            return True
        if cell.stock or not payer.debit(16):
            return False
        self.local_switch_debit+=16
        self.local_switch_heat+=8
        cell.stock+=8
        cell.delivered_input+=8
        self.switch_balance()
        return True

    def _drop_endpoint(self,cell):
        remaining=cell.stock
        cell.debit(remaining)
        self.local_switch_heat+=remaining
        self.switch_balance()

    def _break(self):
        # The common source connection is the physical source of new
        # strobes. Losing it does not modify an emitted packet or its clock.
        self._quench("driver")
        if not self.fixture.held_plane:
            self.fixture.output[f"vector-driver:{self.side}"] = 0
        self._drop_endpoint(self.setter_quench)
        self.setter.cut = True
        self.setter.reset_control_inhibit = True
        for cell in self.row_quench.values():
            if cell.stock:
                # Physical local one-shot quench load, powered by its existing
                # parcel. Receiver slots/force/clock and stored source mode
                # words are untouched at the common break.
                cell.busy=True

    def drain_source_leaves(self, dt):
        dt=cam.exact(dt)
        require(dt>=0,"Negative quench time")
        for endpoint,cell in self.row_quench.items():
            if not cell.busy or cell.stock<4 or not dt:
                continue
            work=min(cell.stock-4,4*2**20*dt)
            cell.debit(work)
            self.local_switch_heat+=work
            if cell.stock==4:
                require(cell.debit(4),"Unfunded aperture terminal strobe")
                self.local_switch_heat+=4
                self.rows[endpoint].pulse.cut=True
                self.rows[endpoint].pulse.reset_control_inhibit=True
                cell.busy=False
        self.switch_balance()

    def _actual_bank_available(self):
        return (not self.cut and self.machine.powered and
                self.fixture.positions[f"cut{self.side}"]!=self.fixture.p["CUT_LIMIT"])

    def _vector_grant(self,endpoint):
        row=self.rows[endpoint]
        if self.fixture.held_plane:
            # A paid physical bypass selects a different issue path. The
            # conforming local aperture remains in its actual retained state.
            return bool(self.fixture.output[f"vector-driver:{self.side}"])
        escrow=self.row_quench[endpoint]
        return (self._actual_bank_available() and self.activation>=cam.DRIVER and self.gate and
                not escrow.busy and escrow.stock==8 and not row.pulse.cut)

    def native_reset_request(self, endpoint, selector):
        if not self._vector_grant(endpoint):
            return "inhibited"
        # The differently scoped receiver/native-inhibit pole may still refuse.
        return self.rows[endpoint].pulse.native_reset_request(selector)

    def setter_reset_request(self):
        if (not self._actual_bank_available() or not self.gate or self.activation<cam.DRIVER
                or (self.fixture.held_plane and not self.fixture.output[f"vector-driver:{self.side}"])):
            return "inhibited"
        return self.setter.native_reset_claim()

    def disconnect(self):
        require(self.fixture.positions[f"cut{self.side}"] == self.fixture.p["CUT_LIMIT"]
                or not self.machine.powered, "Missing actual cut or loss of operating route")
        if not self.cut:
            self._quench("arm")
        self.cut = True
        self._break()
        self.machine.inhibit()
        if self.native_input is not None:
            self.native_input.cold_cut()

    def reconnect(self):
        require(self.fixture.positions[f"cut{self.side}"] == 0, "Supply cut still engaged")
        self.cut = False

    def prepare_strobe(self, *, working_contact):
        """One bounded LOCAL phase6 sampling edge after final recharge."""
        s, i = self.fixture, self.side
        if s.held_plane:
            return "held-plane"
        selected = reset_rails(s.p, normal=s.normal,
                               cam_position=s.positions['cam'], side=i, clamp=s.positions[f'clamp{i}'])
        require(type(working_contact) is bool and
                working_contact in {v is not None for v in selected}, "Inconsistent phase contact")
        if not (working_contact and PhaseRails(9, inputs.OPEN) in selected and self.cut and
                s.positions[f"cut{i}"]==s.p["CUT_LIMIT"] and self.activation==0):
            return "unqualified"
        if self.arm:
            return "already-armed"
        if not self._grant("arm"):
            return "unfunded"
        return "armed"

    def setter_mode_commit(self, line, code, *, working_contact):
        """An actual bounded receiver commit on the one bank-local setter line."""
        require(line is self.setter_control and type(code) is int and 0<=code<16,
                "Foreign control line or out-of-wire mode")
        s,i = self.fixture,self.side
        rails=reset_rails(s.p,normal=s.normal,cam_position=s.positions["cam"],
                          side=i,clamp=s.positions[f"clamp{i}"])
        require(type(working_contact) is bool and working_contact in {v is not None for v in rails},
                "Impossible local setter contact")
        if (s.held_plane or not line.valid[7] or line.words[7]!=code or not working_contact or PhaseRails(9,inputs.OPEN) not in rails
                or not self.cut or self.activation!=0 or code!=9):
            return "unqualified"
        if not self.setter.cut:
            return "already-released"
        if self.setter.reset_reserve.stock<48:
            return "unfunded"
        require(self.setter.reset_reserve.debit(32) and
                self._reserve_quench(self.setter.reset_reserve,self.setter_quench),
                "Setter release lost reserved work")
        self.setter.cut=False
        self.setter.native_inhibit=False
        return "released"

    def activation_arc(self, new, dt, *, working_contact):
        # The event is the physical oriented transition at DRIVER. Split
        # other world/clock/POWER events before calling this local arc.
        s, i = self.fixture, self.side
        new,dt = cam.exact(new),cam.exact(dt)
        old = self.activation
        require(0 <= new <= cam.WARM and dt>=0 and abs(new-old)<=cam.VMAX*dt, "Invalid ACT segment")
        require(type(working_contact) is bool, "Missing contact order")
        up = old < cam.DRIVER <= new
        if up and not s.held_plane:
            allowed = gates.cam_band_values(s.positions["cam"],13*(1-i)+8,s.p,s.normal)
            require(working_contact in allowed, "Impossible phase8 contact")
        key=f"act{i}:0"
        require(key not in s.jammed or old==new,"A jammed ACT cannot traverse a contact")
        down=old>=cam.DRIVER>new
        if not (up or down):
            self.drain_source_leaves(dt)
            s.positions[key]=new
            return "no-upward-crossing"
        crossing=dt*(cam.DRIVER-old)/(new-old)
        self.drain_source_leaves(crossing)
        s.positions[key]=cam.DRIVER
        if down:
            self._break()
            result="no-upward-crossing"
        else:
            result=self._driver_crossing(working_contact)
        self.drain_source_leaves(dt-crossing)
        s.positions[key]=new
        return result

    def _driver_crossing(self, working_contact):
        s,i=self.fixture,self.side
        if (s.held_plane or not working_contact or self.cut or s.positions[f"cut{i}"]!=0
                or not self.arm or not self.machine.powered):
            return "crossing-inhibited"
        if not self._grant("driver"):
            return "unfunded"
        self._quench("arm")
        s.output[f"vector-driver:{i}"] = 1
        for endpoint,row in self.rows.items():
            # Same per-channel activation price and reserve as the first
            # CamBank handoff. Partial funding has per-channel outcomes.
            escrow=self.row_quench[endpoint]
            if escrow.busy:
                continue
            payer=row.pulse.reset_source_reserve
            if escrow.stock==0 and payer.stock>=48 and payer.debit(32) and self._reserve_quench(payer,escrow):
                row.pulse.cut = False
                row.pulse.reset_control_inhibit = False
        self.setter.reset_control_inhibit = False
        return "gate-open"

    def capture(self, endpoint, slot, now):
        if not self._vector_grant(endpoint):
            return "cut"
        row=self.rows[endpoint]
        # The already-qualified physical wire feeds the original capture
        # transition, on the same slots and work cells. In held mode its
        # separate bypass can be connected even while the local pole stays cut.
        wire=CapturePort(row.pulse)
        return field.PulseSelector.capture(wire,slot,self.setter.held.get(endpoint,0),now=now)

    def deliver(self, endpoint, slot, now):
        return self.rows[endpoint].pulse.deliver(slot,now=now)

    def receiver_arm_commit(self, endpoint, line, code):
        """Remote receiver uses only its actual paid local received mode."""
        h=self.rows[endpoint]
        require(h.control is line and type(code) is int and 0<=code<16,"Foreign receiver arm")
        if not line.valid[7] or line.words[7]!=code or code!=10:
            return "no-arm"
        pulse=h.pulse
        if not pulse.native_inhibit and not pulse.reset_motor_owner and not pulse.maintenance_control_enabled:
            return "already-armed"
        if not pulse.reset_reserve.debit(32):
            return "arm-unfunded"
        pulse.native_inhibit=False
        pulse.reset_motor_owner=False
        pulse.maintenance_control_enabled=False
        return "receiver-armed"

    def setter_offer(self, args):
        if (not self._actual_bank_available() or self.machine.offer_inhibit or self.setter_quench.stock!=8
                or (self.gate and self.activation<cam.DRIVER)):
            return "cut"
        return self.setter.issue(args)


class ThresholdSampler(gates.PredecessorSampler):
    """B1 coherent sample; the pre-park and completed cleanup are distinct."""
    def strobe(self):
        s = self.state
        if s.held_plane:
            return "held-plane"
        s.check_rigid_seats()
        require(self.remaining==0, "No physical sampling edge")
        self.remaining = self.period
        work = min(s.U, Q(gates.PREDICATE_WORK))
        s.U -= work
        s.heat += work
        self.work += work
        self.samples += 1
        s.check_U_balance()
        if work != gates.PREDICATE_WORK:
            return "partial/held"
        raw = gates.physical_contact_snapshot(s)
        pred, cleanup = gates.fold_contact_snapshot(raw,1)
        for j,value in enumerate(pred):
            s.output[f"cam-stop:{j}"] = int(value)
        def pre_park(anchor):
            cold = 1-anchor
            return all((raw['blend',anchor],raw['cut-end',cold],raw['low-E',cold],
                        raw['zero',cold,0],raw['clamp-zero',cold],raw['reset-zero',cold]))
        s.rewind_sample = tuple(pre_park(i) for i in (0,1))
        s.cleanup_sample = cleanup
        require(all(cleanup[i] == (s.rewind_sample[i] and raw['cam-entry',i]) for i in (0,1)),
                "Rewind qualification tested its own termination")
        return "captured"


def rewind_segment(s, carriage, effort, dt, *, threshold=Q(29), compliance=Q(2)):
    """Held physical arc; assume no internal clock, keeper or mode event."""
    force,dt = cam.exact(effort),cam.exact(dt)
    require(carriage is s.abort_carrier and type(carriage) is gates.Abort and not s.held_plane
            and carriage.position==s.positions["abort"], "Use actual surviving abort carrier")
    require(dt>=0 and abs(force)<=2*s.p['D']*Q(11,5)+Q(11,10)+field.REACTION and
            28<=threshold<=29 and 0<compliance<=2,"Unrated actual shaft effort or stroke law")
    require(carriage.phase in ('ENTERING','FULL','RETURN'), "Normal motion has separate ownership")
    pos,circ=s.positions['cam'],s.limits['cam']
    anchor=s.keeper=gates.keeper(s.keeper,s.positions['blend'],s.p['BLEND_LIMIT'])
    entry=anchor*13*s.p['SEGMENT']
    gap=(pos-entry)%circ
    # A closed directional pawl forces v=0. Winding currents are not reset.
    speed=min(Q(1),max(Q(0),(-force-threshold)/compliance))
    travel=min(gap,speed*dt) if (carriage.phase=='FULL' and s.rewind_sample[anchor]
                                   and 'cam' not in s.jammed) else Q(0)
    s.positions['cam']=(pos-travel)%circ
    heat=-force*travel
    require(heat>=0 and (pos!=entry or s.positions['cam']==entry), "Powered motion overshot the actual anchor")
    s.mechanical_input+=heat
    s.mechanical_heat+=heat
    return travel


def sampled_rewind(sampler, effort, duration):
    """Compose the actual mechanical arc with every intervening paid sample.

    Other forces, contacts, ports, U inflow/draw and the carriage phase
    are held. Split at their own events if composing a larger trajectory.
    """
    remaining=cam.exact(duration)
    require(remaining>=0 and isinstance(sampler,ThresholdSampler) and not sampler.state.held_plane,
            "Invalid sampled rewind interval")
    travel=Q(0)
    while remaining>0 or sampler.remaining==0:
        if sampler.remaining==0:
            sampler.strobe()
            continue
        rate=sampler.clock_rate()
        step=min(remaining,sampler.remaining/rate) if rate else remaining
        travel+=rewind_segment(sampler.state,sampler.state.abort_carrier,effort,step)
        sampler.flow_clock(step)
        remaining-=step
    return travel


def field_clutch(x, efforts, native, dt, clamp, *, native_engaged, failed_contact=None):
    """Memoryless clutch. The conjugate velocity passed back per donor is g*x_dot."""
    x,native,dt,clamp=map(cam.exact,(x,native,dt,clamp))
    require(dt>=0 and 0<=clamp<=cam.CLAMP_END and type(native_engaged) is bool,"Invalid clutch arc")
    fs=tuple(cam.exact(v) for v in efforts)
    require(len(fs)<=80 and all(abs(v)<=field.FORCE for v in fs),"Unrated installed field effort")
    require(native_engaged or native==0,"Unpowered native drive")
    require(failed_contact is None or type(failed_contact) is bool,"Invalid physical clutch failure")
    open_=(clamp<cam.CUTOFF) if failed_contact is None else failed_contact
    end=field.bit_flow(x,sum(fs,Q(0)),native,dt,open_contact=open_,native_engaged=native_engaged)
    dx=end-x
    port_work=tuple(f*dx if open_ else Q(0) for f in fs)
    require(sum(port_work,Q(0))+native*dx==(native+(sum(fs,Q(0)) if open_ else 0))*dx,
            "Clutch lost an effort/flow pair")
    return end,port_work


def joins(p):
    inlet=record("input_lifecycle_results.json")["resources"]
    parent=record("parent_retirement_results.json")["resources"]
    memory=record("legacy_realization_results.json")['inventory']['memory_by_owner']['local_route_metadata']
    packed=record("parent_realization_results.json")["cost_bounds"]["new_private_routing_bits"]
    itinerary=record("interrupted_renewal_results.json")
    version_a=record("gate_source_completion_results.json")["bounds"]
    cam_budget=record("cam_reformation_results.json")["arithmetic"]["resources"]
    blocks,poses,driven=catalogue(p)
    pairs=2*p['D']*driven
    entries=len(blocks)+len(poses)+pairs+2+1
    bits=1024*entries+2048
    offset=memory['new_owner_upper']+packed+parent['added_reset_fanout_control_bits']+inlet['additional_control_bits']
    require(len(MODE_ROOTS)==11 and len(blocks)==112 and pairs==1360,"B contact allocation changed")
    require(offset+bits<=memory['old_owner_allocation'], "Descriptor injection escaped installed old metadata")
    burst=Q(2*bits+1024); rate=Q(bits*gates.RATE)+Q(bits,1024)
    # The two local source arm strobes and their driver releases also
    # consume this finite fixture work; charge them conservatively again.
    burst+=2*2*64
    rate+=2*2*32*(cam.CONTROL_MAX+gates.RATE)
    channels=4*field.DEGREE*field.L
    endpoint_bits=channels+2  # local irreversible quench mode on each new source-side parcel
    burst+=32*endpoint_bits
    rate+=2*8*2**20*endpoint_bits+Q(endpoint_bits,1024)
    capacity,old_rate,old_burst=map(Q,(inlet['updated_upstream_capacity'],inlet['updated_upstream_rate'],inlet['updated_upstream_burst']))
    additional_stock=32+8*(channels+2)
    capacity-=additional_stock
    reserve=capacity-old_burst-burst-2*(old_rate+rate)
    supply=Q(cam_budget['unchanged_supply_rate'])
    old_external_slack=Q(parent['old_external_rate_slack'])
    require(rate<old_external_slack,"Descriptor work does not fit old owner-rate row")
    input_peak=Q(record("input_lifecycle_results.json")['resources']['combined_native_peak'])
    extra_peak=2*bits*gates.RATE+2*2*64*gates.RATE+Q(bits,1024)+8*(channels+2)*2**20
    require(41*(input_peak+extra_peak)<2**93 and 4*41*(input_peak+extra_peak)<2**94,
            "New gate-mode work exceeds physical gross work ratings")
    require(reserve>2048 and old_rate+rate<supply,"Threshold gate demand exceeds actual U envelope")
    # Passive breakaway contacts at the source gate and receiving clutch
    # add a strict independent mechanical loading allowance, per interface.
    extra_reaction=Q(2*channels+8)*field.U_BIT/8192
    total_reaction=Q(inlet['complete_joint_reaction'])+Q(parent['added_parent_gate_reaction'])+extra_reaction
    geometry_energy=record("parent_realization_results.json")["cost_bounds"]["actual_bank_capacity"]
    require(Q(geometry_energy)==p["EMAX"],"Wrong operating capacity for B contact plane")
    require(total_reaction<field.REACTION,"New disconnect load exceeds retained generator margin")
    gap=2*(28-Q(11,10)-field.REACTION)
    tv=Q(version_a['ordinary_force_variation_rate'])
    #14 maximum contaminated phase visits, two13-band fresh halves and
    # TWO distinct sampled release waits on the abort route (prepark & return).
    sample_waits=max(len(v['visits']) for v in itinerary['normal_entry_cases'])+2*13+2
    delta=sample_waits*gates.PREDICATE_PERIOD_MAX
    sequence=Q(itinerary['corrected_sequence_allocation'])+delta
    require(sequence<Q(itinerary['H']) and itinerary['raw_cover']==6,"Sample waits defeat B itinerary")
    stop_clearance=Q(p['SEGMENT'],4)-gates.PREDICATE_PERIOD_MAX
    require(p['GUARD']==p['SEGMENT']//2 and stop_clearance>0,"Sample prefix leaves its current cam band")
    require(Q(cam.DRIVER-cam.ARM,1)/cam.VMAX>cam.CONTROL_DELAY and
            Q(cam.CLAMP_END-cam.PREPARED_AT,1)/cam.VMAX>cam.CONTROL_DELAY,
            "Physical dwell fails to cover the arm or preparation path")

    geometry=record("threshold_geometry_results.json")["arithmetic"]
    earliest=Q(geometry["watchdog"]["earliest"])
    band=Q(geometry["band_travel"])/13
    short=max(Q(cost) for name,cost in geometry["phase_bounds"].items() if int(name.split("_")[0]) not in (1,8))
    require(short+band+gates.PREDICATE_PERIOD_MAX<earliest
            and Q(geometry["watchdog"]["ACT_milestone"])+gates.PREDICATE_PERIOD_MAX<earliest
            and Q(geometry["unknown_cam_probe"])+gates.PREDICATE_PERIOD_MAX<Q(geometry["recognition_allocation"]),
            "Sample time no longer fits normal stage and recognition margins")
    abort_window=Q(geometry["local_clearing"]["abort_join"])+60+2*gates.PREDICATE_PERIOD_MAX
    require(abort_window<Q(geometry["local_clearing"]["abort_stroke_min"]),
            "Full return no longer covers the sampled/energy join")
    require(28+14+10+30+28+256<=gates.PREDICATE_WORK,
            "B pre-park and cleanup folds exceed sampler price")
    naive=Q(channels*gates.UPDATE_WORK*gates.RATE)/supply
    require(naive>64 and tv/gap>0,"Missing physical comparison")
    return dict(blocks=len(blocks),poses=len(poses),driven=driven,incoming_pairs=pairs,
                actual_clamp_roots=list(MODE_ROOTS),descriptor_bits=bits,first_descriptor=offset,
                end_descriptor_exclusive=offset+bits,owner_slack=memory['old_owner_allocation']-offset-bits,
                bounded_control_entries=entries,new_recoverable_storage=additional_stock,upstream_capacity=capacity,upstream_burst_added=burst,
                upstream_rate_added=rate,minimum_U_after_additions=reserve,offered_supply=supply,
                combined_upstream_rate=old_rate+rate,remaining_old_owner_rate_slack=old_external_slack-rate,
                existing_input_combined_peak=input_peak,additional_native_service_envelope=extra_peak,
                added_quench_mode_bits=endpoint_bits,source_quench_settle=Q(1,2**20),added_joint_reaction=extra_reaction,
                combined_joint_reaction=total_reaction,ordinary_reversal_gap=gap,retained_force_TV=tv,
                direction_count_rate=tv/gap,maximum_conditional_added_sample_waits=sample_waits,
                sample_delay_addition=delta,sampler_work_count_upper=28+14+10+30+28+256,
                normal_stop_sample_to_working_edge_clearance=stop_clearance,
                full_return_join_with_energy_and_samples=abort_window,conditional_sequence=sequence,H=itinerary['H'],
                independent_per_field_override_demand_to_supply=naive,
                once_owned_reset_and_parent=True,actual_B_source_complete=False)


def couple_steady(pulses, x, dt, clamp, *, failed_contact=None):
    """Exact constant-force local subarc, with physical donor escrows consumed."""
    dt=cam.exact(dt)
    require(dt>0 and len({id(p) for p in pulses})==len(pulses),"Repeated donor or no elapsed time")
    for p in pulses:
        active=next((i for i,slot in enumerate(p.slots) if slot is not None),None)
        require(active is not None and not p.reset_motor_owner and p.force==field.U_BIT*p.selected()
                and p.energy[active].stock>=1+8*dt,"Split at material, clock or funding boundary")
    forces=[p.force for p in pulses]
    end, works=field_clutch(x,forces,Q(0),dt,clamp,native_engaged=False,failed_contact=failed_contact)
    open_=(clamp<cam.CUTOFF) if failed_contact is None else failed_contact
    velocity=(end-x)/dt if open_ else Q(0)
    for p,work in zip(pulses,works):
        old=(p.motor_input,p.motor_output,p.motor_heat)
        p.flow(dt,relative_velocity=velocity)
        require(p.motor_input-old[0]==8*dt and p.motor_output-old[1]==work and
                p.motor_heat-old[2]==8*dt-work,"Actual driver work lost at the clutch")
    return end,sum(works,Q(0))


def local_checks(p, isa, compiled, Ports):
    bankcap=int(Q(record("parent_realization_results.json")["cost_bounds"]["actual_bank_capacity"]))
    machine=retirement.RetirableParent(isa,compiled,bank=retirement.parent.BankWork(bankcap,Q(bankcap)))
    sibling=retirement.RetirableParent(isa,compiled,bank=retirement.parent.BankWork(bankcap,Q(p["EOFF"])+10240))
    payer=inputs.SourceWork(0,1<<36,1<<36)
    s=SharedContacts(p,0,payer,(machine,sibling))
    # Same E consumed by the sampler and by an actual parent transfer.
    sampler=ThresholdSampler(s)
    s.positions['cam']=Q(1)
    require(not gates.physical_contact_snapshot(s)['low-E',1],"Initial bank already low")
    sampler.flow_clock(Q(1));require(sampler.strobe()=="captured" and not s.rewind_sample[0],"High E called off")
    require(sibling.recharge(),"Actual bank transfer failed")
    s.positions['cut1']=p['CUT_LIMIT']
    sibling.inhibit()
    require(gates.physical_contact_snapshot(s)['low-E',1],"Contact reads a different bank after transfer")
    sampler.flow_clock(Q(1));sampler.strobe()
    require(s.E[1]==sibling.bank.stock and s.rewind_sample[0] and not s.cleanup_sample[0],
            "Pre-park requires an independent cam-entry fact")
    s.positions['cam']=Q(1)
    full=s.abort_carrier
    s.abort_arc(Q(1),Q(10000))
    require(full.phase=="FULL" and full.full,"Missing actual FULL stroke")
    travel=sampled_rewind(sampler,Q(-68),Q(4))
    require(travel==1 and s.positions['cam']==0,"Rewind overran keeper A entry")
    sampler.flow_clock(Q(1));sampler.strobe()
    require(s.cleanup_sample[0] and rewind_segment(s,full,Q(68),Q(4))==0,"Positive residual unparked entry")
    s.abort_arc(Q(-1),Q(1))
    require(full.phase=="RETURN" and rewind_segment(s,full,Q(-68),Q(9))==0,"Return lost its parked cam")
    s.positions['blend']=p['BLEND_LIMIT'];s.positions['cut0']=p['CUT_LIMIT'];s.positions['cam']=Q(3)
    # Local edge input with a low E0 supplied by a distinct real bank instance.
    low=retirement.RetirableParent(isa,compiled,bank=retirement.parent.BankWork(bankcap,Q(0)))
    other=SharedContacts(p,0,inputs.SourceWork(0,1<<36,1<<36),(low,sibling))
    other.positions.update({k:v for k,v in s.positions.items() if k!="abort"})
    other.blend_arc(p["BLEND_LIMIT"],0)
    other.blend_arc(p["BLEND_LIMIT"]-1,1)
    require(other.keeper==1,"Physical keeper did not retain B between endpoint contacts")
    other.blend_arc(p["BLEND_LIMIT"],1)
    sample_b=ThresholdSampler(other)
    sample_b.flow_clock(Q(1));sample_b.strobe()
    full_b=other.abort_carrier
    other.abort_arc(Q(1),Q(10000))
    before_samples=sample_b.samples
    before_work=sample_b.work
    wrapped=sampled_rewind(sample_b,Q(-68),Q(416003))
    require(sample_b.samples-before_samples==416003 and
            sample_b.work-before_work==416003*gates.PREDICATE_WORK and other.cleanup_sample[1],
            "Temporal rewind omitted actual intermediate sampler or final cleanup")
    require(wrapped==13*p["SEGMENT"]+3 and other.positions["cam"]==13*p["SEGMENT"],
            "Fixed negative winding missed B entry across zero")
    observed_E=s.E[1]
    s=SharedContacts(p,0,inputs.SourceWork(0,1<<36,1<<36),(machine,sibling))
    payer=s.source_work
    # Reach the ordinary handoff using the actual funded parent/field cam.
    episode=retirement.JoinedCam(machine)
    cam.finish(episode,cam.VMAX)
    require(episode.certificate(),"Nominal verification fixture did not reform")
    h=episode.activation_to(cam.DRIVER,cam.DRIVER/cam.VMAX)
    require(h is episode.ordinary_handoff and machine.powered,"Actual power/reformation handoff absent")
    endpoint=field.Destination(machine.setter.targets[0],1,42)
    s.positions["act0:0"]=cam.DRIVER;s.output["normal-cam"]=1
    b=LiveSourceBank(s,0,episode,endpoint,cam.ControlLine(words=[10]*8,valid=[True]*8))
    h.setter.held[endpoint]=1   # allowed existing installed command for this boundary probe
    # An already accepted setter retains the original actual CPU operand owner.
    machine.C[0]=isa.encode(isa.IO,2,3,4,isa.PRIM["set_field"])
    machine.pc=0;machine.R[3:7]=[1,0,19,1]
    require(machine.recharge() and machine.launch(),"Funded setter parent failed")
    ports=Ports(compiled)
    require(machine.complete(ports,pause_after_offer=True)=="waiting" and
            isinstance(machine.child,retirement.SetterChild),"No real SET_FIELD child")
    child=machine.child;args=child.args
    require(b.capture(endpoint,0,0)=="latched", "Ordinary source cannot emit from this state")
    pending=h.pulse.pending[0];work=h.pulse.trigger_energy[0].stock
    b.activation_arc(cam.DRIVER-Q(1,2**21),Q(1,2**21),working_contact=False)
    require(machine.powered and b.capture(endpoint,1,0)=="cut" and h.setter.cut and not b.gate,
            "Vector loss should close the next strobe while preserving CPU power")
    require(machine.child is child and child.args is args and h.pulse.pending[0] is pending and
            h.pulse.trigger_energy[0].stock==work,"Source cut erased a real old claim")
    require(b.row_quench[endpoint].busy and b.row_quench[endpoint].stock==6 and not h.pulse.cut,"Halfway quench lost paid progress")
    b.drain_source_leaves(Q(1,2**21))
    require(b.row_quench[endpoint].stock==0 and h.pulse.cut and not b.row_quench[endpoint].busy,
            "Actual final four-work strobe did not disconnect the old leaf")
    require(b.deliver(endpoint,0,Q(1,2))=="active" and h.pulse.slots[0][0]==1,
            "Previously emitted trigger lost its physical destination/outcome")
    h.control.words[:]=[10]*8;h.control.valid[:]=[True]*8
    require(b.capture(endpoint,1,1)=="cut" and h.pulse.clock_edge(0)=="active" and
            b.native_reset_request(endpoint,True)=="inhibited","Stale ARM or donor loss changed endpoint authority")
    try:
        LiveSourceBank(s,0,episode,endpoint,cam.ControlLine())
    except ValueError:
        pass
    else:
        raise AssertionError("An old handoff reinstalled an issuing gate")
    s.positions["cut0"]=p["CUT_LIMIT"]
    b.disconnect()
    require(not machine.powered and machine.child is child and machine.pending is not None
            and machine.native_inhibit and machine.return_inhibit,"CPU isolation erased unfinished settlement")
    s.positions['cam']=(13+2)*p['SEGMENT']+p['GUARD'];s.positions['clamp0']=cam.PREPARED_AT
    b.activation_arc(0,cam.DRIVER,working_contact=False)
    require(not b.arm and b.prepare_strobe(working_contact=False)=="unqualified",
            "Reverse clamp opened a rearm path")
    s.positions['cam']=(13+6)*p['SEGMENT']+p['GUARD']
    before=payer.spent
    require(b.prepare_strobe(working_contact=True)=="armed" and b.arm and payer.spent-before==32
            and b.capture(endpoint,1,2)=="cut","Stored arm cost, chronology or cut priority wrong")
    require(b.prepare_strobe(working_contact=True)=="already-armed" and payer.spent-before==32,
            "Held preparation minted a second claim")
    s.positions['cut0']=0;b.reconnect()
    require(not machine.powered and b.capture(endpoint,1,2)=="cut" and b.setter_offer((0,0,1,1))=="cut",
            "Passive supply reconnect started a new parent")
    s.positions['cam']=(13+8)*p['SEGMENT']+p['GUARD']
    # The completed POWER join is deliberately missing in this branch.
    require(b.activation_arc(cam.DRIVER,cam.DRIVER,working_contact=True)=="crossing-inhibited"
            and b.capture(endpoint,1,3)=="cut", "Unpowered driver rising manufactured source entry")
    # The conforming aperture excludes this behavior; P can bridge it with
    # a separately paid actual held-source grant retaining the same endpoint.
    paid=s.U
    require(s.held_takeover("vector-driver:0",1)=="held" and paid-s.U==2048,"Unpaid physical-site grant")
    require(h.pulse.cut and b.capture(endpoint,1,3)=="latched" and h.pulse.cut and
            b.capture(endpoint,1,3)=="pending-busy" and h.pulse.cut and
            b.capture(endpoint,-1,3)=="reject" and h.pulse.cut,
            "Physical bypass rewrote the retained aperture or lost its fixed endpoint")
    s.held_takeover("vector-driver:0",0)
    require(b.capture(endpoint,2,3)=="cut" and b.native_reset_request(endpoint,False)=="inhibited",
            "Held-zero physical grant leaked a new source or native reset strobe")
    s.check_U_balance()
    z=[Q(0)]*len(s.route)
    clamp_index=tuple(s.positions).index("clamp0")
    bad_route=gates.Captured(s.owner,"route",0,(endpoint,1),"typed-cross-class")
    require(s.physical_pose_request(bad_route)=="uninstalled","Unpriced pose-to-bit conversion")
    valid_route=gates.Captured(s.owner,"route",0,(clamp_index,1),"actual-pose")
    require(s.physical_pose_request(valid_route)=="held-pose-update","Physical pose reroute absent")
    actuator=gates.Captured(s.owner,"local-actuator",0,(clamp_index,68),"bank actuator")
    require(s.physical_pose_request(actuator)=="held-pose-update","Missing existing-E actuator")
    s.positions["clamp0"]=Q(100)
    rates=gates.actuator_rates(s,z)
    require(rates["banks"][0]["energy_derivative"]==-Q(753,5) and
            rates["banks"][0]["mechanical_power"]==Q(374,5),
            "Failed actuator lost conjugate work on the actual bank stock")
    # Incoming field cutoff and native mobility are different use sites.
    donors=[]
    for _ in range(34):
        pulse=field.PulseSelector()
        require(pulse.trigger(0,1)=="active","Missing donor initialization")
        pulse.flow(Q(1000))
        donors.append(pulse)
    x=Q(0);open_x,open_work=couple_steady(donors,x,Q(1),cam.CUTOFF-1)
    closed_x,closed_work=couple_steady(donors,open_x,Q(1),cam.CUTOFF)
    require(open_x>x and open_work>0 and closed_x==open_x and closed_work==0 and
            all(z.force==field.U_BIT for z in donors),"A closed clutch erased a retained donor or moved the bit")
    require(s.held_takeover("field-clutch:1",1)=="held","Physical clutch override lost actual work")
    held_x,held_work=couple_steady(donors,closed_x,Q(1),cam.CUTOFF,
                                   failed_contact=bool(s.output["field-clutch:1"]))
    require(held_x>closed_x and held_work>0,"Held-open physical target was credited with isolation")
    try:
        field_clutch(x,[Q(11,5)],Q(0),Q(1),0,native_engaged=False)
    except ValueError:
        pass
    else:
        raise AssertionError("Pose force silently entered high-mobility bit port")
    native_end,_=field_clutch(x,(),field.NATIVE_FORCE,Q(1,field.WORD_CLOCK),cam.CUTOFF,native_engaged=True)
    require(native_end>x,"Incoming clutch improperly suppressed a separately powered native write")
    rails={}
    for n in (0,3,4,1107,1220,1223,111110,cam.PREPARED_AT,cam.CUTOFF-1):
        a=reset_rails(p,normal=True,cam_position=(13+6)*p['SEGMENT']+p['GUARD'],side=0,clamp=n)
        rails[str(n)]=[(v.field,v.raw_input) for v in a]
        require(reset_rails(p,normal=True,cam_position=(13+2)*p['SEGMENT']+p['GUARD'],side=0,clamp=n)=={None}
                and reset_rails(p,normal=False,cam_position=19*p['SEGMENT']+p['GUARD'],side=0,clamp=n)=={None},
                "Reverse or abort traversal replayed source reset")
    return dict(B1_sample_inputs=28,B1_latched_outputs=30,prepark_distinct_from_actual_entry=True,
                actual_shared_E=observed_E,source_capture_after_loss="cut",
                accepted_trigger_after_loss="active",accepted_setter_preserved=True,
                stopped_CPU_does_not_rearm_on_supply_reconnect=True,charged_source_override_after_cut=True,
                field_parameter_cases=rails,actual_open_bit_displacement=open_x,
                independent_receiver_motor_work_open=open_work,closed_clutch_bit_work=closed_work,held_open_physical_clutch_work=held_work,
                ordinary_pose_effort_as_bit_rejected=True,
                separately_funded_native_mobility_test=native_end,keeper_A_stop_travel=travel,
                keeper_B_stop_travel=wrapped,keeper_B_elapsed_sampler_strobes=sample_b.samples-before_samples,
                keeper_B_elapsed_sampler_work=sample_b.work-before_work,closed_entry_resists_signed_force=True,
                existing_bank_actuator_energy_derivative=rates["banks"][0]["energy_derivative"],
                quench_time=Q(1,2**20),quench_midpoint_work=6,
                local_gate_payer_spent=s.gate_work,local_gate_heat=s.heat)


def reentry_checks(p, isa, compiled):
    bankcap=int(Q(record("parent_realization_results.json")["cost_bounds"]["actual_bank_capacity"]))
    m=retirement.RetirableParent(isa,compiled,bank=retirement.parent.BankWork(bankcap,Q(bankcap)))
    spare=retirement.RetirableParent(isa,compiled,bank=retirement.parent.BankWork(bankcap,Q(0)))
    payer=inputs.SourceWork(1,1<<36,1<<36)
    state=SharedContacts(p,1,payer,(m,spare))
    episode=retirement.JoinedCam(m);cam.finish(episode,cam.VMAX)
    h=episode.activation_to(cam.DRIVER,cam.DRIVER/cam.VMAX)
    target=field.Destination(m.setter.targets[2],0,21)
    state.positions["act0:0"]=cam.DRIVER;state.output["normal-cam"]=1
    setter_line=cam.ControlLine(words=[10]*8,valid=[True]*8)
    b=LiveSourceBank(state,0,episode,target,setter_line)
    state.positions["cut0"]=p["CUT_LIMIT"];b.disconnect();b.drain_source_leaves(Q(1,2**20))
    b.activation_arc(0,cam.DRIVER,working_contact=False)
    trip=gates.Trip();trip.transition(state.E[0],p["EOFF"],p["EON"],zero=True)
    work_before=m.setter.reset_reserve.stock
    # No pending child in this branch; other branches require actual closure.
    rr=retirement.ParentRetirement(m)
    require(rr.advance(Q(1,32))=="retired" and m.pending is None and m.fabric.token is None
            and not m.fabric.link_storage_busy(),"Missing paid CPU cleanup")
    state.positions["cam"]=19*p["SEGMENT"]+p["GUARD"]
    state.positions["clamp0"]=cam.PREPARED_AT
    require(b.prepare_strobe(working_contact=True)=="armed","No retained physical arm")
    # Only the actual bank-local control-line job may make the setter usable.
    events=[]
    setter_line.flow(cam.CONTROL_DELAY,9,lambda _dt:None,lambda code:events.append(
        b.setter_mode_commit(setter_line,code,working_contact=True)))
    require("released" in events and b.setter_offer((2,0,21,-1))=="cut",
            "Setter release skipped source cut or its paid endpoint action")
    state.positions["cut0"]=0;b.reconnect()
    require(b.setter_offer((2,0,21,-1))=="cut","Supply reconnect reopened a CPU")
    state.positions["cam"]=21*p["SEGMENT"]+p["GUARD"]
    b.activation_arc(cam.POWER,cam.POWER,working_contact=True)
    ok,_=trip.transition(state.E[0],p["EOFF"],p["EON"],power=True,old_done=(
        m.pending is None and m.child is None and m.native is None and
        m.fabric.token is None and not m.fabric.link_storage_busy() and not m.cell.busy))
    require(ok and rr.fresh_entry()=="fresh-entry" and m.powered,
            "Actual completed old parent, zero arm and rising POWER required")
    require(b.setter_offer((2,0,21,-1))=="latched","Prepared setter cannot capture in boot/scan window")
    for _ in range(3616):
        h.setter.step()
    require(h.setter.held[target]==-1,"Accepted setter did not reach its fixed target")
    # Receiver arming is a separate propagated input; no sampler can issue yet.
    # The receiver can be in an inhibited native mode from its earlier
    # reset. The propagated rail is driven using the very same control line.
    h.control.flow(cam.CONTROL_DELAY,9,lambda _dt:None,lambda _code:None)
    h.pulse.native_inhibit=True
    b.activation_arc(cam.ARM,cam.ARM-cam.POWER,working_contact=True)
    seen=[]
    h.control.flow(cam.CONTROL_DELAY,10,lambda _dt:None,lambda code:seen.append(
        b.receiver_arm_commit(target,h.control,code)))
    require("receiver-armed" in seen and not h.pulse.native_inhibit,
            "Actual remote copy did not arm its fixed receiver")
    require(b.capture(target,0,0)=="cut","Receiver arm manufactured a source trigger")
    require(b.activation_arc(cam.DRIVER,cam.DRIVER-cam.ARM,working_contact=True)=="gate-open"
            and b.capture(target,0,1)=="latched" and h.pulse.pending[0][0]==-1,
            "Real driver crossing lacks its actual work/captured value")
    require(not b.arm and b.gate and b.activation_arc(cam.DRIVER,0,working_contact=True)=="no-upward-crossing",
            "Held driver level repeated a positive gate grant")
    state.positions["cut0"]=p["CUT_LIMIT"];b.disconnect();b.drain_source_leaves(Q(1,2**20))
    b.activation_arc(0,cam.DRIVER,working_contact=False)
    state.positions["cam"]=19*p["SEGMENT"]+p["GUARD"]
    payer.debit(payer.stock)
    before=(b.arm,b.gate,state.gate_work,state.heat)
    require(b.prepare_strobe(working_contact=True)=="unfunded" and
            before==(b.arm,b.gate,state.gate_work,state.heat),"Empty U minted a new source grant")
    return dict(shared_setter_before=work_before,private_retirement_work=rr.spent,
                prepared_setter_before_POWER=True,actual_power_entry=True,source_setting=-1,
                ARM_before_TRIGGER=True,unfunded_arm_retains_cut=True,
                endpoint_switch_debit=b.local_switch_debit,endpoint_quench_heat_after_cut=b.local_switch_heat,
                gate_work=state.gate_work,
                gate_heat_after_quench=state.heat,recoverable_gate_stock=sum(c.stock for c in state.escrow.values()))


def interface_regressions(p,isa,compiled):
    # A labelled routed-parent subtype can resist untimed recharge or supply
    # timed shared charging elsewhere. This check reads its actual E only.
    class LabelledParent(retirement.RetirableParent):
        pass

    machine=LabelledParent(isa,compiled)
    sibling=retirement.RetirableParent(isa,compiled)
    machine.bank.owner=(9,0)
    sibling.bank.owner=(9,1)
    source=inputs.SourceWork(9,1<<36,1<<36)
    s=SharedContacts(p,9,source,(machine,sibling))
    try:
        SharedContacts(p,9,source,(sibling,machine))
    except ValueError:
        pass
    else:
        raise AssertionError("Bank-owned E could change its side")
    def pose(kind,name,v):
        return s.physical_pose_request(gates.Captured(9,kind,name,v,"material"))
    require(s.abort_arc(1,0)==[] and s.abort_carrier.normal and s.positions["abort"]==0,
            "Positive velocity at an instant bought an unjammed mechanical departure")
    for name in ("abort","blend","cam","seat0:0","act0:0"):
        require(pose("jam",name,True)=="jam","Material jam not applied")
    require(s.abort_arc(1,1)==[] and s.abort_carrier.normal and s.positions["abort"]==0,
            "Jammed abort departed normal without traveling")
    require(s.abort_arc(1,0)==[] and s.positions["abort"]==0,
            "Zero-time jammed arc generated a fresh latch")
    def must_reject(call):
        try:
            call()
        except ValueError:
            return
        raise AssertionError("Incoherent claimed material trajectory accepted")
    must_reject(lambda:s.blend_arc(1,1))
    must_reject(lambda:s.carrier_arc(0,1,1))
    s.blend_arc(0,1)
    s.carrier_arc(0,0,1)
    require(s.positions["carrier0"]==s.positions["seat0:0"]==0 and s.keeper==0,
            "A stationary rigid assembly forged displacement or changed keeper")
    # Normal cam clock progresses even while the actual cam is jammed.
    sample=ThresholdSampler(s)
    pre=s.positions["cam"]
    sample.cam_segment(68,Q(1,2))
    require(s.positions["cam"]==pre and sample.remaining==Q(1,2) and s.mechanical_input==0,
            "Jammed normal cam moved or froze unrelated clock")
    require(pose("detach","seat0:0",True)=="detached-held","Detach failed")
    s.carrier_arc(0,1,1)
    require(s.positions["carrier0"]==1 and s.positions["seat0:0"]==0 and
            pose("detach","seat0:0",False)=="misaligned/hold", "Detached jam moved or silently reattached")
    s.carrier_arc(0,0,1)
    require(pose("detach","seat0:0",False)=="reattached","Aligned reattachment failed")
    s.positions["seat0:0"]=1
    sample.flow_clock(Q(1,2))
    old=(s.U,sample.remaining,sample.samples)
    must_reject(lambda:sample.strobe())
    require((s.U,sample.remaining,sample.samples)==old,"Malformed rigid state caused a paid partial sample")
    s.positions["seat0:0"]=0
    sample.strobe()
    # The existing JoinedCam/ParentRetirement supplier on this frozen branch
    # accepts an exact RetirableParent. The subclass case above tests the
    # sampler/fixture boundary only; the joint timed parent requires its own
    # closure and lawful subtype admission.
    machine=retirement.RetirableParent(isa,compiled)
    s=SharedContacts(p,9,source,(machine,sibling))
    s.jammed.add("act0:0")
    episode=retirement.JoinedCam(machine)
    cam.finish(episode,cam.VMAX)
    h=episode.activation_to(cam.DRIVER,cam.DRIVER/cam.VMAX)
    ep=field.Destination(machine.setter.targets[0],0,0)
    s.positions["act0:0"]=cam.DRIVER
    b=LiveSourceBank(s,0,episode,ep,cam.ControlLine())
    a0=b.activation
    must_reject(lambda:b.activation_arc(a0-1,1,working_contact=False))
    b.activation_arc(a0,1,working_contact=False)
    require(b.activation==a0 and b.gate,"Jammed ACT fabricated driver loss")
    pose("jam","act0:0",False)
    s.positions["cut0"]=p["CUT_LIMIT"]
    before=(h.pulse.reset_source_reserve.stock,h.pulse.reset_reserve.stock,h.pulse.reset_motor_owner,
            h.setter.reset_reserve.stock)
    require(b.native_reset_request(ep,True)=="inhibited" and b.capture(ep,0,0)=="cut"
            and b.setter_offer((0,0,0,1))=="cut" and b.setter_reset_request()=="inhibited",
            "Physical bank cut before local dispatch leaked an issue")
    require(before==(h.pulse.reset_source_reserve.stock,h.pulse.reset_reserve.stock,h.pulse.reset_motor_owner,
                     h.setter.reset_reserve.stock),"Blocked strobe moved work or selector")
    s.positions["cut0"]=0
    machine.inhibit()
    require(b.native_reset_request(ep,True)=="inhibited" and b.capture(ep,0,0)=="cut"
            and b.setter_offer((0,0,0,1))=="cut" and b.setter_reset_request()=="inhibited",
            "Power cut before aperture dispatch leaked an issue")
    # One operator input at a paid positive-arm boundary with an older
    # actual quench still moving. Its joint initialized reachability is
    # separate. Compare one crossing interval with the exact prescribed split.
    def crossing_case(split):
        mt=retirement.RetirableParent(isa,compiled)
        target=SharedContacts(p,0,inputs.SourceWork(0,1<<36,1<<36),
                              (mt,retirement.RetirableParent(isa,compiled)))
        d=retirement.JoinedCam(mt)
        cam.finish(d,cam.VMAX)
        d.activation_to(cam.DRIVER,cam.DRIVER/cam.VMAX)
        target.positions["act0:0"]=cam.DRIVER
        e=field.Destination(mt.setter.targets[0],0,0)
        bank=LiveSourceBank(target,0,d,e,cam.ControlLine())
        bank._break()
        require(bank._grant("arm") and bank.row_quench[e].busy,"Required charged entry unavailable")
        target.positions["cam"]=21*p["SEGMENT"]+p["GUARD"]
        tick=Q(1,2**20)
        target.positions["act0:0"]=cam.DRIVER-tick/4
        if split:
            out=bank.activation_arc(cam.DRIVER,tick/4,working_contact=True)
            require(bank.row_quench[e].stock==7 and bank.row_quench[e].busy,
                    "Quarter-quench grant skipped at the actual crossing")
            bank.activation_arc(cam.DRIVER+3*tick/4,3*tick/4,working_contact=True)
        else:
            out=bank.activation_arc(cam.DRIVER+3*tick/4,tick,working_contact=True)
        require(out=="gate-open" and bank.gate and not bank.arm and
                bank.row_quench[e].stock==0 and bank.rows[e].pulse.cut and
                bank.capture(e,0,0)=="cut","Later drain retroactively funded endpoint release")
        return (bank.rows[e].pulse.reset_source_reserve.stock,target.U,target.heat,
                bank.local_switch_debit,bank.local_switch_heat,bank.rows[e].pulse.cut)
    require(crossing_case(False)==crossing_case(True),"Timed aperture state differs under split")
    return dict(jammed_sites=5,rigid_jam_holds=True,detached_jam_holds=True,
                upward_crossing_checks_eligibility_before_suffix=True,busy_endpoint_stays_cut_after_missed_grant=True,
                zero_elapsed_force_cannot_depart=True,
                stationary_jammed_arc_advances_time=True,actual_bank_pre_dispatch_guards=True,
                physical_bypass_preserves_pole=True,labelled_parent_subtype_and_wrong_bank_checked=True)


def normalize(value):
    if isinstance(value,Q):
        return str(value)
    if isinstance(value,dict):
        return {k:normalize(v) for k,v in value.items()}
    if isinstance(value,(tuple,list)):
        return [normalize(v) for v in value]
    return value


def generate():
    require(sys.version_info[:2]==(3,12) and not sys.flags.optimize, "Unoptimized Python 3.12 required")
    isa,c,Ports=retirement.source_inputs();p=parameters(c)
    names=("gate_source_completion.py","gate_source_completion_results.json","GATE-SOURCE-COMPLETION.md",
           "cam_reformation.py","cam_reformation_results.json","threshold_field_source.py",
           "threshold_field_source_results.json","threshold_design.py","parent_retirement.py",
           "parent_retirement_results.json","input_lifecycle.py","input_lifecycle_results.json",
           "interrupted_renewal_results.json","threshold_geometry_results.json",
           "parent_realization_results.json","legacy_realization_results.json",
           "threshold_program_model.py","threshold_program_source.py","parent_realization.py","legacy_realization.py",
           "fixed_island_model.py","threshold_incidence_model.py","threshold_publication_model.py","constructors.py")
    hashes={}
    for name in names:
        supplier = INPUT_BASE if name in ("input_lifecycle.py", "input_lifecycle_results.json") else BASE
        text=subprocess.check_output(["git","show",supplier+":"+PREFIX+name],cwd=REPO).decode("utf-8-sig")
        digest=gates.digest(text)
        require(digest==gates.digest((HERE/name).read_text(encoding="utf-8-sig")), "Changed supplier "+name)
        hashes[name]=digest
    costs=joins(p)
    return normalize(dict(scope="threshold fixed-contact and post-handoff local operation adapter",base=BASE,input_base=INPUT_BASE,
        image_sha256=gates.digest(json.dumps(c.image)),costs=costs,
        checked=local_checks(p,isa,c,Ports),reentry=reentry_checks(p,isa,c),
        interface_repairs=interface_regressions(p,isa,c),immutable_inputs_sha256_lf=hashes,
        sources_sha256_lf={n:gates.digest((HERE/n).read_text(encoding="utf-8-sig"))
                           for n in ("THRESHOLD-GATE-SOURCE.md","threshold_gate_source.py")},
        full_B_source_admission=False,global_progress_proved=False,program_completion=False))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    group=parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--check",action="store_true");group.add_argument("--write",action="store_true")
    args=parser.parse_args()
    evidence=generate();dest=HERE/"threshold_gate_source_results.json"
    if args.write:
        dest.write_text(json.dumps(evidence,indent=2,sort_keys=True)+"\n",encoding="utf-8",newline="\n")
    else:
        require(json.loads(dest.read_text(encoding="utf-8"))==evidence,"Evidence differs")
    print("PASS threshold contact/retained-grant adapter; complete source and mission remain open")


if __name__=="__main__":
    main()

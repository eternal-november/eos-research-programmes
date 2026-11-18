"""Finite ordinary SEND, local renewable command hold, and earlier donor duties for B."""
import argparse
import ast
from dataclasses import dataclass
from fractions import Fraction as Q
from hashlib import sha256
import json
from pathlib import Path

import receiver_lease as previous

HERE = Path(__file__).resolve().parent
PIN = "8f53d2983a9b6e3f9ff3a636c716de97f5c90050"
BASE = "bc87afecc034d83dd26fdd922c132523110bfdd7"
need = previous.need
SIGMA = Q(1, 4096)
C = Q(1, 1024)
TOP, THRESHOLD = Q(240), Q(110)
BLEED, FAST_BLEED = Q(10), Q(101, 10)
CURRENT = Q(11, 5)
NEUTRAL = 32 * 64 + 32 * 4096 + (32 << 40)
D = Q(1, 2**30)


def text_at(name):
    return previous.legacy.text_at(PIN, "portability/" + name)


def load_modules():
    names = ("projected_work_flow", "a_prime_source_assembly", "abort_protocol_alternative",
             "return_seat", "private_comparison", "world_channel", "quiet_window")
    modules = {}
    for name in names:
        modules[name], _ = previous.legacy.module_at(PIN, "portability/" + name + ".py", name)
    return modules["world_channel"], modules["quiet_window"]


def fields(word, target):
    # Validity and all three fields use the original fixed-width B ABI.
    if not 0 <= word < 2**46:
        return {}
    side = (word >> 5) & 1
    def amplitude(shift):
        return max(-22, min(22, ((word >> shift) & 63)-32))
    output = {(target,1,side,0): amplitude(6), (target,0,side,0): amplitude(12)}
    action, index = (word >> 18) & 15, (word >> 22) & (2**18-1)
    if 2 <= action < 11 and index == 0:
        output[target,action,side,index] = amplitude(40)
    return output


def decoder_checks(isa, image):
    reference=isa.RawPorts(image)
    target=17
    total=0
    for side in range(2):
        for action in range(16):
            for index in (0,1,2**18-1):
                for raw_amp in (0,9,10,11,32,53,54,55,63):
                    word=26+(side<<5)+(raw_amp<<6)+((63-raw_amp)<<12)+(action<<18)+(index<<22)+(raw_amp<<40)
                    reference.perform("send_command",(target,word),None)
                    need(reference.fields==fields(word,target),"Physical projection differs from the B field ABI")
                    total+=1
    need(fields(1<<46,target)=={},"Malformed incoming level obtained ordinary reach")
    # Physical fanout wiring and bit clamping are combinational at the
    # receiver. Keep the activation bit as an electrical level. This avoids
    # work on a separate digital timer or a target-paid endpoint callback.
    bound=64+46+3*(6*8+6*4)+18+18+2*16+17*(6*3+4)+41
    need(bound <= 960,"Unpriced bounded decode and commit")
    return dict(matched_valid_tuples=total,full_width_output_decode_bound=bound)


def certify_flush(isa, image):
    # Summary facts for calls are verified on the actual linked image. Count
    # exported SENDs on every returning control-flow path of the helper.
    entries = {image.labels[name]: name for name in image.functions}
    ends = sorted(entries) + [len(image.nodes)]
    send = isa.PRIM["send_command"]
    for pc in range(len(image.nodes)):
        op, a, b, c, imm = isa.decode(image.image[pc])
        if op == isa.IO and imm == send:
            proc = entries[max(start for start in entries if start <= pc)]
            need(proc in ("boot", "flush") and c == 2, "New physical SEND site")
    summary = {}
    def traverse(name):
        if name in summary:
            return summary[name]
        start = image.labels[name]
        stop = ends[ends.index(start)+1]
        stack, seen, returns = [(start, 0)], set(), set()
        while stack:
            pc, count = stack.pop()
            if (pc, count) in seen:
                continue
            seen.add((pc, count))
            need(start <= pc < stop, "Unscoped compiler jump")
            op, a, b, c, imm = isa.decode(image.image[pc])
            if op == isa.RET:
                returns.add(count)
                continue
            if op == isa.CALL:
                added = traverse(entries[imm])
                stack.extend((pc+1, min(2, count+n)) for n in added)
            elif op in (isa.JMP, isa.JZ):
                stack.append((imm, count))
                if op == isa.JZ:
                    stack.append((pc+1, count))
            else:
                need(op != isa.HALT, "Healthy helper halts")
                increment = int(op == isa.IO and imm == send)
                stack.append((pc+1, min(2, count+increment)))
        summary[name] = returns
        return returns
    need(traverse("helper") == {1} and summary["flush"] == {1}, "Some returning helper skips or doubles SEND")
    frame = ast.unparse(image.functions["frame"])
    boot = ast.unparse(image.functions["boot"])
    fragments = ("if w[ENTRY] > 0:", "while visits < MAINT_BATCH:", "target = w[MAINT_CURSOR]",
                 "helper(target)", "w[MAINT_CURSOR] = (target + 1) % DEGREE", "visits += 1")
    need(all(row in frame for row in fragments) and frame.count("helper(") == 1
         and "send_command(t, NEUTRAL_COMMAND)" in boot and image.constants["NEUTRAL_COMMAND"] == NEUTRAL,
         "Scheduler/commissioning projection changed")
    k = image.constants
    traces = []
    for start in range(k["DEGREE"]):
        visits = [((start+j) % k["DEGREE"], j//k["MAINT_BATCH"]) for j in range(2*k["DEGREE"])]
        for target in range(k["DEGREE"]):
            pairs = [frame_index for t, frame_index in visits if t == target]
            need(len(pairs) == 2 and pairs[1]-pairs[0] == 10, "Wrong physical target visit cadence")
        traces.append(start)
    return dict(checked_helper_procedures=len(summary), returning_SEND_counts=sorted(summary["helper"]),
                all_entry_cursors=len(traces), nominal_between_visits_frames=10, neutral=NEUTRAL,
                commissioning_no_maintenance_frames=k["ENTRY_FRAMES"])


@dataclass
class Hold:
    voltage: Q
    word: int
    last_issue: object = None  # retrospective provenance, never read by the physical gate
    heat: Q = Q(0)
    input: Q = Q(0)

    def __post_init__(self):
        need(0 <= self.voltage <= TOP and 0 <= self.word < 2**64, "Uninstalled receiver state")
        self.entry = self.energy

    @property
    def energy(self):
        return C*self.voltage**2/2

    def drive(self, connected=True):
        return self.word if connected and self.voltage > THRESHOLD else NEUTRAL

    def flow(self, dt, bleed, filling=False):
        dt, bleed = Q(dt), Q(bleed)
        need(dt >= 0 and BLEED <= bleed <= FAST_BLEED, "Illegal charged subarc")
        refill = TOP/(SIGMA/2)+FAST_BLEED if filling else Q(0)
        before = self.energy
        self.voltage = min(TOP, max(Q(0), self.voltage+(refill-bleed)*dt))
        # The far-end pulse brings 64 units during its final half-window.
        # Source regulation dumps surplus at the actual receiver.
        incoming = 64*dt/(SIGMA/2) if filling else Q(0)
        dissipation = incoming + before-self.energy
        need(dissipation >= 0, "Missing local far-end work")
        self.input += incoming
        self.heat += dissipation
        need(self.entry+self.input == self.energy+self.heat, "Receiver energy balance")


@dataclass(frozen=True)
class Flight:
    launched: Q
    due: Q
    owner: tuple
    word: int


class CommandLane:
    """One trigger per actual ordinary offer, a real prepaid cell and a separate load bond."""
    def __init__(self, bus, ordinal, destination, hold):
        need(0 <= ordinal < len(bus.source.receivers) and destination == bus.source.receivers[ordinal]
             and bus.bank is bus.parent.bank and bus.source.operating_bank is bus.bank, "Foreign SEND lead")
        self.bus, self.ordinal, self.destination, self.hold = bus, ordinal, destination, hold
        self.owner = (*bus.bank.owner, destination)
        self.index = ordinal*128
        self.now, self.mail, self.live = Q(0), NEUTRAL, None
        self.source_connected = self.receiver_connected = self.decoder_operating = True
        self.capture_open = False
        self.tx_heat = self.rx_heat = self.in_line = Q(0)
        self.issued = self.changes = 0
        self.delay = Q(1,2)

    def accept(self, args, cpu):
        need(cpu is self.bus.parent and cpu.pending is not None and cpu.io_paid and cpu.committing
             and cpu._io_info()[0] == "send_command" and cpu.fabric.token is not None
             and cpu.fabric.token.issued and cpu.io_args is args, "Unbound ordinary command offer")
        ordinal, value = args
        if ordinal != self.ordinal or not 0 <= value < 2**46:
            return 0
        self.mail = value
        if (not self.source_connected or self.live is not None or self.index in self.bus.blocked
                or self.bus.cells[self.index].stock < 4096):
            return 0
        need(Q(1,2) <= self.delay <= 1, "Unrated command lead")
        self.live = Flight(self.now, self.now+self.delay, self.owner, self.mail)
        self.bus.blocked.add(self.index)
        self.bus.dirty.add(self.index)
        self.issued += 1
        return 0

    def flow(self, end, bleed=BLEED):
        end = Q(end)
        need(end >= self.now, "Command time decreased")
        p = self.live
        if p is None:
            self.hold.flow(end-self.now, bleed)
            self.now = end
            return
        # Traversal permits cuts, scarcity and source clock silence after issue.
        bounds = (p.launched, p.launched+SIGMA, p.due-SIGMA, p.due-SIGMA/2, p.due)
        need(end <= p.due, "Missed physical command completion")
        for left, right in zip(bounds, bounds[1:]):
            a, b = max(left, self.now), min(right, end)
            if b <= a:
                continue
            dt = b-a
            if left == p.launched:
                fraction = dt/SIGMA
                need(self.bus.cells[self.index].debit(4096*fraction), "Reservation already spent")
                self.tx_heat += 3072*fraction
                self.in_line += 1024*fraction
            if left == p.due-SIGMA:
                amount = 960*dt/(SIGMA/2)
                self.in_line -= amount
                self.rx_heat += amount
            last = left == p.due-SIGMA/2
            if last:
                need(self.in_line >= 64*dt/(SIGMA/2), "Receiver created energy")
                self.in_line -= 64*dt/(SIGMA/2)
                if not self.capture_open:
                    self.rx_heat += 64*dt/(SIGMA/2)
            self.hold.flow(dt, bleed, filling=last and self.capture_open)
            if b == p.due-SIGMA/2 and self.now < b:
                # Common physical last decoder edge, before any recharge of
                # the old holding capacitor by this pulse.
                self.capture_open = self.decoder_operating and self.receiver_connected
                if self.capture_open:
                    self.hold.word, self.hold.last_issue = p.word, p.launched
                    self.changes += 1
        if end == p.due:
            self.live = None
            self.bus.blocked.remove(self.index)
            self.capture_open = False
        self.now = end
        self.check()

    def check(self):
        need(self.bus.cells[self.index].spent == self.tx_heat+self.rx_heat+self.in_line+self.hold.input
             and self.in_line >= 0, "Unbalanced command work")


def paid_trial(world, isa, image):
    cap = int(Q(json.loads(text_at("parent_realization_results.json"))["cost_bounds"]["actual_bank_capacity"]))
    e = world.charging.OperatingBank((2,1),cap,Q(cap))
    cpu = world.compare.ComparedParent(isa,image,bank=e)
    ucap = Q(json.loads(text_at("world_channel_results.json"))["source"]["reduced_U_capacity"])-2**24
    payer = world.raw.SourceWork(2,ucap,ucap/2)
    s = world.paced.TimedSource(e,payer)
    need(s.reform() == "formed-unpowered" and s.begin_entry(e)
         and s.entry_flow(Q(s.ENTRY_WORK,world.raw.CLEAR_RATE)), "No paid source entry")
    bus = world.WorkBank(cpu,s)
    bus.world_gate = lambda: s.powered and cpu.powered and not cpu.recharge_inhibit
    clock = world.paced.NativeClock(cpu,s,external_receivers=True,existing_bus=bus,adc_first=SIGMA,tx_first=SIGMA)
    slot = 1
    installed = tuple(s.receivers)
    need(len(installed) == 40, "Wrong physical target order")
    route = CommandLane(bus,slot,installed[slot],Hold(Q(0),NEUTRAL))
    base = world.paced.timed_ports(isa)(image,s)

    class Ports:
        source = s
        def perform(self,name,args,actor):
            return route.accept(args,actor) if name == "send_command" else base.perform(name,args,actor)
        def advance(self,actor):
            base.advance(actor)

    class Cycle(world.paced.OrdinaryCycle):
        IO = world.paced.OrdinaryCycle.IO | {"send_command"}

    pc = next(i for i in range(image.labels["flush"],len(image.nodes)) if isa.decode(image.image[i])[0]==isa.IO
              and isa.decode(image.image[i])[4]==isa.PRIM["send_command"])
    _,_,reg,arity,_=isa.decode(image.image[pc])
    need(arity==2, "Wrong actual SEND signature")
    W = NEUTRAL + 20*4096
    cpu.pc=pc
    cpu.R[reg:reg+2]=[slot,W]
    cycle=Cycle(clock,Ports(),16*D)
    for phase,proc in ((Q(1,4),cycle.capture),(Q(1,2),cycle.offer),(Q(1),cycle.retire)):
        t=cycle.time(phase.numerator,phase.denominator)
        clock.advance_to(t)
        route.flow(t)
        if proc == cycle.retire:
            cpu.R[reg+1] = NEUTRAL
        proc()
    p = route.live
    need(p is not None and p.word == W and p.owner == (2,1,installed[slot]) and cpu.retired==1
         and route.hold.drive()==NEUTRAL and bus.cells[route.index].spent>0, "No actual independent child")
    # This suffix projects away subsequent native clock events. The CPU,
    # source and recharge path are cut; independent paid pulse and local
    # bleed continue. No post-cut private/raw service is inferred.
    cpu.inhibit(); s.cold_cut(); route.source_connected=False
    route.flow(p.due)
    need(route.hold.drive()==W and route.live is None and route.hold.voltage==TOP, "Cut erased the paid child")
    route.receiver_connected=False
    route.flow(p.due+7)
    need(route.hold.drive(False)==NEUTRAL and route.hold.drive(True)==W, "Unexpired reopening lost")
    route.flow(p.due+13)
    need(route.hold.drive(True)==NEUTRAL and route.hold.word==W and route.mail==W,
         "A reconnect revived a retained old level")
    bus.audit(); route.check()
    return dict(actual_SEND_pc=pc, owner=p.owner, source_slot=route.index, cpu_retired=cpu.retired,
                snapshot=p.word, target_ordinal=slot, issued=route.issued, receiver_commits=route.changes,
                far_end_debit=route.rx_heat+route.hold.input, receiver_held_energy=route.hold.energy,
                postcut_source_heat=route.tx_heat, stored_word_after_expiry=route.hold.word, after_expiry=route.hold.drive())


def physical_bounds():
    F = Q(1163265,1048576)
    J = 11*F
    rec_gap = J + Q(1,2)
    shortest_hold = (TOP-THRESHOLD)/FAST_BLEED
    max_hold = (TOP-THRESHOLD)/BLEED
    need(9*Q(100,101)>1+D and rec_gap < shortest_hold, "Real refresh spacing fails")
    converter_current = C*(TOP/(SIGMA/2)+FAST_BLEED)
    fill_budget = TOP*converter_current*(SIGMA/2)
    need(fill_budget<=64 and TOP*converter_current<=64/(SIGMA/2), "Far-end current or work outside packet")
    # Active bridge V=v+Ri+L dI/dt; passive, locally clamped winding when
    # refused or disconnected. At zero the ordinary diode can stick.
    velocity, resistance, slew, flyback = Q(11,10), Q(1,4), Q(5,2), Q(4)
    off_slope = flyback-velocity
    limit = velocity+resistance*CURRENT+slew
    old_sign = CURRENT/min(slew,off_slope)
    per_change = 2*CURRENT/slew
    stale = 1+max_hold+old_sign
    need(limit <= 5 and limit*CURRENT < 16 and off_slope>0 and stale<15
         and 1+per_change<3 and 1+CURRENT/off_slope<3, "Physical field or retirement budget fails")
    need(1+max_hold+old_sign < J+2*3+6+3, "Uncovered positive CUT after genuine issue")
    # Establish both electromechanical port identities on signed corners;
    # the affine equations and bounds extend to every allowed v,i.
    for i in (-CURRENT,-1,1,CURRENT):
        for v in (-velocity,0,velocity):
            for direction in (-1,1):
                d=slew*direction
                volts=v+resistance*i+d
                need(volts*i == i*d+resistance*i*i+v*i, "Active work identity")
            diode=-flyback*(1 if i>0 else -1)
            d=diode-v-resistance*i
            need((1 if i>0 else -1)*d<=-off_slope
                 and i*d+resistance*i*i+flyback*abs(i)+v*i==0, "Missing passive brake work")
    return dict(Fmax=F,J=J,lower_SEND_spacing=9*Q(100,101),max_delay=1,
                max_receiver_gap=rec_gap,shortest_hold=shortest_hold,longest_hold=max_hold,
                silent_old_sign_after_SEND=stale,initial_unfinished_offer_allowance=3,
                common_left_hull=3+stale,qualified_SEND_to_settled=1+per_change,
                old_sign_current_tail=old_sign,hard_voltage=limit,hard_positive_power=limit*CURRENT,
                circuit_heat_off_peak=resistance*CURRENT**2+flyback*CURRENT,
                decoder_work=960,far_end_fill_work_upper=fill_budget,far_end_peak_current=converter_current,
                receiver_cap=C*TOP**2/2,receiver_hold_work_source=64,
                direct_cut_horizon_previous=J+15)


def repeated_receipts(physical):
    gap = physical["max_receiver_gap"]
    data = Hold(TOP,NEUTRAL+20*4096)
    minimum = TOP
    for j in range(12):
        # The previous decoder finished filling at its actual local due time.
        # In the latest next receipt the committed level can change half a
        # sigma before the next due time. Use the larger full gap here.
        data.flow(gap,FAST_BLEED)
        minimum=min(minimum,data.voltage)
        need(data.drive()==data.word,"Actual charge falls through the healthy inter-arrival gap")
        data.word = NEUTRAL+(-20 if j%2 else 20)*4096
        data.flow(SIGMA/2,FAST_BLEED,True)
        need(data.voltage==TOP,"A full paid receiver parcel did not restore the same cell")
    for v in (0,50,THRESHOLD,TOP-1,TOP):
        h=Hold(Q(v),NEUTRAL)
        h.flow(SIGMA/2,FAST_BLEED,True)
        need(h.voltage==TOP and h.input==64,"Full and partial entries require the actual same parcel")
    return dict(late_receipts=12,minimum_prechange_voltage=minimum,
                partial_and_full_initial_voltages=5,net_fresh_stock_at_top=C*TOP**2/2)


def donor_rows(quiet, physical):
    base=json.loads(text_at("return_itinerary_results.json"))["budget"]
    point={k:Q(base[v]) for k,v in (("q","quiet_gap"),("spacing","same_bank_power_separation"),
          ("previous","guaranteed_quiet_gap_search_span"),("old_total","candidate_entry_to_ready_and_outgoing_retirement"),
          ("H","H"))}
    hosts=40; banks=2*hosts
    rho=banks/point["spacing"]
    fast_profile=quiet.Profile(1,0,physical["common_left_hull"],0).plus(quiet.Profile(banks,rho,0,0))
    fast_minimum=fast_profile.first_sufficient_integer(point["q"])
    profile=quiet.Profile(1,0,physical["silent_old_sign_after_SEND"],0).plus(quiet.Profile(banks,rho,0,0))
    profile=profile.plus(quiet.Profile.episodes(banks,0,physical["silent_old_sign_after_SEND"]))
    minimum=profile.first_sufficient_integer(point["q"])
    need(profile.verify(minimum,point["q"]) and not profile.verify(minimum-1,point["q"]), "Missed strict quiet threshold")
    total=point["old_total"]-point["previous"]+minimum
    need(total<point["H"], "Quiet replacement exceeds H")
    tolerance=[]
    for unknown in range(35):
        for dark in range(35-unknown):
            force=2*(34-unknown-dark)-Q(22,5)*(6+unknown)-Q(11,10)-Q(324,1000)
            if force>=31:
                tolerance.append([unknown,dark,force])
    need({tuple(x[:2]) for x in tolerance}=={(0,z) for z in range(5)}|{(1,z) for z in range(2)},
         "Wrong reach-dependent force allowance")
    # Given verified full warm old/current ports the ACT speed floor need
    # not be used to obtain this *lower* separation from one threshold to another.
    gap=(Q(6800000000)-Q(750000000))/Q(11,10)
    boot=Q(268456453,2**26)
    F,J=physical["Fmax"],physical["J"]
    first_ordinary=boot+4097*F+2*J+3
    input_prime=Q(66569369,262144)
    # Max applies when the input path starts its own real producer job at
    # POWER in parallel. Starting after a separate grant costs its elapsed delay.
    join=boot+4097*F+2*J+2101*F+2*J+15+60+Q(101,100)+input_prime
    need(join<100000/Q(11) and first_ordinary<gap and join<gap, "No chronological overlap")
    return dict(quiet_job=point["q"],common_initial_packet_hull=physical["silent_old_sign_after_SEND"],
                individually_delayed_preexisting_parents=banks,fast_search_if_3q_prior_offer=fast_minimum,
                count_burst=banks,count_slope=rho,search=minimum,conditional_itinerary=total,
                H=point["H"],deadline_slack=point["H"]-total,force_rows=tolerance,
                physically_qualified_POWER_to_WARM_lower=gap,first_ordinary_upper=first_ordinary,
                full_return_join_upper_including_parallel_input_prime_charged_serially=join,
                real_full_return_minimum=100000/Q(11),continuous_input_prime=input_prime)


def prices(physical):
    previous_point=json.loads(text_at("world_channel_results.json"))["source"]
    channels=17*40*2
    lanes=80; inherited=lanes*128
    # Two-ended powers count both directions in every one of the 41 zones.
    # One fixed rate stream from U travels through the existing maintenance
    # contact and retains its finite transit stock on a cut. 16 is the
    # receiver rating; positive source cost is at most twice that rating.
    stream=Q(16); feed_peak=2*channels*stream
    local_capacity=lanes*physical["receiver_cap"]+inherited*1024+channels*(stream+CURRENT**2/2)
    sender_peak=inherited*4096/SIGMA
    far_peak=inherited*max(960,64)/(SIGMA/2)
    added_heat=4*41*(2*sender_peak+2*far_peak+4*feed_peak+channels*16+1000)
    additional_burst=2*inherited*4096
    added_rate=feed_peak+2*inherited*4096
    reserve_reduction=local_capacity+additional_burst+2*added_rate
    old_floor=Q(previous_point["qualified_voltage_floor_slack"])
    floor=old_floor-reserve_reduction+local_capacity/4
    cap=Q(previous_point["reduced_U_capacity"])-local_capacity
    supply=Q(previous_point["remaining_supply_rate"])-added_rate
    bath=Q(previous_point["combined_bath_margin"])-added_heat
    # Only added electronic/cable mounting and pilot components. The
    # useful signed full actuator and reaction are an existing allocation.
    extra_force=4*41*(channels+inherited)*Q(1,2**48)
    reaction=Q(previous_point["remaining_reaction"])-extra_force
    need(min(floor,supply,bath,reaction)>0 and cap>0, "Source budget exhausted")
    return dict(installed_signed_channels_per_host=channels,ordinary_lanes_per_host=lanes,
                ordinary_ready_word_rate=2*lanes,hard_independent_slot_rate=2*inherited,
                old_slot_capacity_counted=inherited,launch_charge=4096,source_heat_per_captured_word=3072,
                physical_far_energy=1024,far_decode_and_pilot_ceiling=960+64,
                additional_storage_reservation=local_capacity,source_U_maintenance_peak=feed_peak,
                additional_rate=added_rate,additional_burst=additional_burst,
                peak_transmitter=sender_peak,peak_receiver=far_peak,
                revised_U_capacity=cap,remaining_U_floor_above_quarter=floor,remaining_supply=supply,
                remaining_bath=bath,added_pilot_reaction=extra_force,remaining_reaction=reaction)


def contrasts():
    # Real possible initial/failed output enable at a charged receiver is
    # separate from the mathematical law of its intact local bleed.
    initial=Hold(TOP,NEUTRAL+20*4096)
    outcomes=[]
    for elapsed in (Q(1),Q(25,2),Q(13),Q(14),Q(100)):
        initial.flow(elapsed-(outcomes[-1][0] if outcomes else 0),BLEED)
        outcomes.append((elapsed,initial.drive()))
    need(outcomes[0][1]!=NEUTRAL and outcomes[2][1]==NEUTRAL, "Passive expiry boundary")
    # Different banks' individual bona fide 10-frame calendars may both miss
    # an arbitrarily short common egress aperture. No controller schedules it.
    # Repeat over 10q, A sends at 1 and B at 7. Egress A is open on [3,9],
    # B on [8,10] plus [0,4]. At EVERY time one egress is open (including
    # overlap), but neither opens on its bank's word.
    qualified=lambda bank,t: (3<=t%10<=9) if bank==0 else (t%10>=8 or t%10<=4)
    for j in range(101):
        t=Q(j,10)
        need(qualified(0,t) or qualified(1,t),"A physical gap was meant to be excluded")
    need(not qualified(0,1) and not qualified(1,7),"Uncovered positive-demand cut disappeared")
    return dict(single_hold_and_unchanged_data=outcomes,pointwise_cover_has_no_accepted_offers=True,
                fixed_input_is_finite_renewal=False)


def generate():
    world,quiet=load_modules()
    isa,image,_=previous.compiled()
    physical=physical_bounds()
    imports=("world_channel.py","world_channel_results.json","private_comparison.py","quiet_window.py",
             "return_itinerary_results.json","return_seat.py")
    return previous.rx.gates.normalize(dict(base=BASE,external_point=PIN,program=previous.evidence("image_transport_results.json")["new_image"],
                program_paths=certify_flush(isa,image),decoder=decoder_checks(isa,image),actual=paid_trial(world,isa,image),physical=physical,
                receipt_reentry=repeated_receipts(physical),donor=donor_rows(quiet,physical),prices=prices(physical),separating=contrasts(),
                imported_LF={name:sha256(text_at(name).encode()).hexdigest() for name in imports},
                source=sha256(Path(__file__).read_text(encoding="utf8").encode()).hexdigest(),
                receiver_source=sha256((HERE/"receiver_lease.py").read_text(encoding="utf8").encode()).hexdigest(),
                proved_whole_B=False))


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    action=parser.add_mutually_exclusive_group()
    action.add_argument("--write",action="store_true")
    action.add_argument("--check",action="store_true")
    args=parser.parse_args()
    result=generate()
    path=HERE/"sender_eligibility_results.json"
    if args.write:
        path.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n",encoding="utf8")
    elif args.check:
        need(result==json.loads(path.read_text(encoding="utf8")),"Sender eligibility evidence changed")
    else:
        print(json.dumps(result,indent=2,sort_keys=True))

"""Join the finite SEND, source-I clock, handoff and electrical reference of B."""

from fractions import Fraction as Q
from hashlib import sha256
from pathlib import Path
import argparse
import io
from itertools import product
import b_reference_return as reference
import json
import os
import subprocess
import sys
import tarfile
import tempfile

HERE = Path(__file__).resolve().parent
BASE = "d26dc729f8fd12ec2b751f79f853076c32c8c711"
PREFIX = "theories-and-designs/byzantine-control/portability/"


def need(ok, msg):
    if not ok:
        raise ValueError(msg)


def raw(name):
    return subprocess.check_output(["git", "show", BASE+":"+PREFIX+name], cwd=HERE).decode("utf-8-sig").replace("\r\n","\n")


def local(name):
    return json.loads((HERE/name).read_text(encoding="utf-8"))


def values(z):
    return {k:str(v) if isinstance(v,Q) else v for k,v in z.items()}


def join_price():
    b = json.loads(raw("b_handoff_results.json"))["quantitative"]
    se = json.loads(raw("sender_eligibility_results.json"))
    pr = se["prices"]
    scratch = json.loads(raw("frame_pacing_results.json"))["certificate"]
    ref = local("b_reference_return_results.json")
    host = local("b_host_flow_results.json")
    old = local("world_channel_results.json")["source"]
    original = json.loads(raw("world_channel_results.json"))["source"]
    consumed = ("remaining_supply_rate","remaining_reaction","combined_bath_margin","reduced_U_capacity",
                "qualified_voltage_floor_slack")
    need(all(old[k]==original[k] for k in consumed), "Changed shared upstream point")
    vector = host["paid_trigger"]
    refp = ref["retirement"]
    slots, lanes, holds = pr["old_slot_capacity_counted"], pr["installed_signed_channels_per_host"], pr["ordinary_lanes_per_host"]
    need((slots,lanes,holds)==(10240,1360,80) and Q(pr["source_U_maintenance_peak"])==32*lanes,
         "Wrong installed command multiplicity")
    rootrate, rootburst = Q(scratch["extra_U_rate"]), Q(scratch["extra_U_burst"])
    need(Q(b["common_U_capacity"]) == Q(old["reduced_U_capacity"])-Q(pr["additional_storage_reservation"])-Q(vector["additional_capacity"])
         and Q(b["free_U_above_pressure_floor"]) == Q(pr["remaining_U_floor_above_quarter"])-Q(3,4)*Q(vector["additional_capacity"])-rootburst-2*rootrate
         and Q(b["supply_slack"]) == Q(pr["remaining_supply"])-rootrate,
         "Two previous join routes disagree")
    # Active electrical storage/phase/gate support for the finite winding feeder described in the note.
    # Everything recoverable except <1 unit of explicitly newly bounded flexure storage fits the earlier 16/channel.
    bits = 128*lanes
    ctrlburst = 2*bits
    ctrlrate = Q(2*bits*2**31)+Q(bits,1024)
    extra_stock = 1
    reference_rate = Q(refp["continuous_reference_allowance_per_bank"])
    refstock = Q(refp["added_capacity"])
    cap = Q(b["common_U_capacity"])-refstock-extra_stock
    floor = Q(b["free_U_above_pressure_floor"])-Q(3,4)*(refstock+extra_stock)-4*reference_rate-ctrlburst-2*ctrlrate
    supply = Q(b["supply_slack"])-2*reference_rate-ctrlrate
    ref_heat = Q(vector["all_mode_bath_margin_after_slot_terminals"])-Q(refp["remaining_zone_work_margin"])
    heat = Q(b["bath_slack"])-ref_heat-4*41*(2*ctrlrate+4*lanes*32+Q(flexure_checks()["worst_host_follower_heat_q"]))
    ref_force = Q(vector["remaining_reaction"])-Q(refp["remaining_mechanical_reaction"])
    mount = 41*bits*Q(1,2**62)
    left = Q(b["paid_reaction_slack"])-ref_force-mount
    need(min(cap, floor, supply, heat, left)>0 and b["planned_trip_work_upper"] == 526,
         "Complete revised point exceeded material resources")
    # Protected connectors do not acquire another set of individually energized ordinary return poles at U.
    # Reserve the actual *two* purposes of the 40x2 signal leads even if every eligible current is outward.
    jac = Q(ref["working_cut"]["other_absolute_current"])
    feeder_both = 2*lanes*Q(32,256)
    # Source-I is local, but its possible low-level exterior signal pins receive the existing weak sleeve price.
    tap_bound = Q(2*2048+2*bits+4*lanes,2**24)
    actual = jac+feeder_both+tap_bound
    need(actual<2**45 and 2*slots*Q(4096,1)/Q(1,4096) < Q(31138)*2**27,
         "Full-port current or external ordinary peak exceeded")
    full_current=actual+Q(ref["working_cut"]["private_absolute_current"])
    need(2**45 < full_current < 2**48,"Full and non-private current rows conflated")
    charge=reference.charge_point(full_current)
    resources=local("../local-control/port_resource_results.json")["transit"]
    tcap=Q(local("threshold_field_source_results.json")["point"]["resources"]["new_bank_rate"])/2
    off, on, em=map(Q,(resources["actual_Eoff"],resources["actual_Eon"],resources["actual_Emax"]))
    # Separate accounting projection: these already installed stocks are not subtracted from U a second time.
    refundable=2**52+Q(pr["additional_storage_reservation"])+extra_stock
    ret=Q(resources["residual_input_power"])+reference_rate+1360*32+refundable/10
    need(40*ret<off and em+tcap+refundable<4*off and off+tcap+refundable<on,"Lead rearm/decay lost")
    warm_v=Q(2**44)
    warm_e=(warm_v**2-2**60)/2**28
    warm_z=Q(1,2**64)*warm_v
    need(on < warm_e < em and warm_z == Q(1,2**20), "Warm keeper has no physical energy/charge witness")
    need(Q(charge["recovery_exponent_lower"])>49 and Q(6)>Q(1,16), "Cold pre-POWER reference corridor lost")
    return values(dict(warm_keeper_energy=warm_e,warm_pad_Q_at_r_zero=warm_z,cold_working_window=Q(6),
                       working_reference=Q(charge["working_r_upper"]),
                       recovered_reference=Q(charge["after_one_sixteenth"]),
                       low_sample_to_rearm=on-off-tcap-refundable,
                       fourfold_rho_over_kEoff=40*ret/off,retirement_stock_ratio=(em+tcap+refundable)/off,
                       Ucap=cap,source_C=2*cap/2**128,pressure_floor_slack=floor,
                       supply_slack=supply,bath_slack=heat,force_slack=left,
                       nonprivate_current_upper=actual,nonprivate_slack_to_2_to_45=2**45-actual,
                       total_current_including_private=full_current,full_slack_to_2_to_48=2**48-full_current,
                       new_bits=bits,new_rate=ctrlrate,new_burst=ctrlburst,new_recoverable_stock=extra_stock,
                       six_stage_counted_once=vector["additional_capacity"],signed_windings=lanes,
                       send_capacitors=holds,send_slots=slots,working_frame=scratch["qualified_frame_q"]))



def flexure_checks():
    """Exercise both stop orientations, heat from slip, and retention under changes of route."""
    span = Q(2**18)
    kappa = Q(1, 2**49)
    small = Q(1, 2**63)
    def sat(x):
        return max(Q(-1), min(x, Q(1)))
    def potential(x, anchor, k=kappa):
        e = abs(x-anchor)
        return k*(e*e/2 if e <= 1 else e-Q(1,2))
    def flow(x, anchor, input_velocity, k=kappa):
        w = input_velocity
        if (x == span and w > 0) or (x == 0 and w < 0):
            w = Q(0)
        elastic = k*sat(x-anchor)
        damping = k*input_velocity/(1+abs(input_velocity))
        heat = damping*input_velocity + elastic*(input_velocity-w)
        need(heat>=0 and abs(elastic+damping)<=2*k, "Unbacked follower effort or negative dissipation")
        need((elastic+damping)*input_velocity == elastic*w+heat, "Follower lost conjugate work")
        return w,heat
    positions=(Q(0), Q(1,2), Q(2), span-Q(1,2), span)
    checked=0
    for x,anchor,u in product(positions,(Q(0),span/2,span),(-Q(11,10),Q(0),Q(11,10))):
        w,_=flow(x,anchor,u)
        need(not (x==0 and w<0 or x==span and w>0), "Absolute guide escaped")
        need(0 <= potential(x,anchor) <= kappa*(span-Q(1,2)), "Spring store over capacity")
        checked += 1
    anchor=span/2
    x=span
    stored=potential(x,anchor)
    stopped,slip_heat=flow(x,anchor,Q(1))
    need(stopped==0 and slip_heat==3*kappa/2 and flow(x,anchor,Q(0))==(0,0),
         "Stationary detachment or outward slip injected work")
    # Detach, reverse and attach to a different shaft: the dog engages velocity only.
    # The installed rest and the follower position at the cut remain the same.
    for route,velocity in (("detached",0),("reversed",-1),("different-positive",1)):
        need(potential(x,anchor)==stored and (route!="detached" or flow(x,anchor,Q(velocity))==(0,0)),
             "A changed route reset accumulated strain")
    entered,_=flow(x,anchor,-Q(1))
    need(entered==-1 and potential(x-1,anchor)<stored, "Reverse motion could not release work")
    # Repeated outward periods cannot accumulate an extra lap of extension/rest offset.
    for _ in range(16):
        w,_=flow(x,anchor,Q(1))
        x+=w
    need(x==span and potential(x,anchor)==stored, "Exited guide by repeated reattachment")
    def advance(x, anchor, u, dt):
        # The same installed rest and absolute stops are used for every routed stroke.
        next_x = max(Q(0), min(span, x+u*dt))
        slip = u*dt-(next_x-x)
        slip_work = kappa*sat(next_x-anchor)*slip
        damper_work = kappa*u*u*dt/(1+abs(u))
        heat = damper_work+slip_work
        port_work = potential(next_x,anchor)-potential(x,anchor)+heat
        need(heat >= 0 and slip_work >= 0, "Overrunning clutch is active at an end")
        return next_x, port_work, heat

    initial = span-Q(1,4)
    retained = initial
    total_work = Q(0)
    total_heat = Q(0)
    # Cross the upper guide while connected; disconnect; engage a reverse route across the
    # whole stroke and slip at the lower guide; engage a new positive route without taking its position.
    for velocity,duration in ((Q(1),Q(1)),(Q(0),Q(3)),(-Q(1),span+1),(Q(1,2),Q(1))):
        end,work,heat = advance(retained,anchor,velocity,duration)
        middle,w1,h1 = advance(retained,anchor,velocity,duration/2)
        other,w2,h2 = advance(middle,anchor,velocity,duration/2)
        need((end,work,heat) == (other,w1+w2,h1+h2), "Changing the observer cut changed paid work")
        retained=end
        total_work+=work
        total_heat+=heat
    need(retained==Q(1,2) and total_work==potential(retained,anchor)-potential(initial,anchor)+total_heat,
         "Detached/rerouted material history gained spring energy")
    need(potential(span,anchor) != potential(anchor,anchor), "A spurious rest reset is undetectable")
    upstream=4*(1360+10240)+4
    fee=128*1360
    total=upstream*potential(span,0)+fee*potential(span,0,small)
    heat=Q(11,10)*(upstream*2*kappa+fee*2*small)
    need(total<1 and heat<1, "The already priced one-unit store or housing heat is exceeded")
    return {"tested_guide_states":checked, "immutable_span":str(span), "total_host_elastic_store":str(total),
            "worst_host_follower_heat_q":str(heat), "upper_slip_heat_at_unit_speed":str(slip_heat),
            "retained_upper_store_after_reroutes":str(stored),
            "completed_route_final_coordinate":str(retained),"completed_route_work":str(total_work),
            "completed_route_heat":str(total_heat)}


def root_and_factual(price):
    f = local("threshold_field_source_results.json")["point"]["mechanics"]
    seat = local("return_seat_results.json")["resources"]
    pr = json.loads(raw("sender_eligibility_results.json"))["prices"]
    tail=Q(372,25)
    # Earlier factual interval included 15 q, and the new physical hull is shorter.
    A=Q(seat["factual_horizon"])
    drift=Q(f["load_drift"])
    hardware = Q(pr["added_pilot_reaction"]) + Q(4*41,2**48) + Q(41*128*1360,2**62)
    # Even the entire .324 emerging as instrumented-sleeve force would have this bounded surcharge.
    hard_react=Q(81,250)
    need(hardware < hard_react and 0 < Q(price["force_slack"]) < hard_react,"Mount reaction")
    spring=Q(3,2)*Q(51,100)+drift*A
    total=spring+hardware/128
    deficit=Q(1,10)+Q(11,400000)*A+Q(1,100) # load and gap have independent raw-head errors
    # Existing isolation comparison consumes the 0.18 threshold with .01 sensor error:
    # evaluate it using the actual source's continued-error entry, not a new inferred convention.
    existing_deficit=Q(seat["clearance_deficit_upper"])
    need(total<1 and existing_deficit<Q(1,5) and tail<15 and A>500 and deficit<Q(1,5),
         "Existing guard cannot cover the added physical force or gap")
    # Each of the 1360 actual winding currents is continuous through a change of command.
    slope=max(Q(5,2),Q(4)+Q(11,10)+Q(11,5)/4)
    need(1360*slope<Q(8313448,225),
         "The known pose variation/root inventory is no longer sufficient")
    hardpoint=Q(311296891,2000)
    need(drift==(2**20+22*hardpoint)/(128*2**29),"Publication drift not on the actual mech point")
    # Static force even when there is no work at the stationary contact.
    counter=80*Q(11,5)/128
    need(counter>1 and counter==Q(11,8),"Lost the genuinely unsafe alternate contact mounting")
    return values(dict(parallel_coil_mount_countercase=counter, effect_age=A,original_seat_load=Q(seat["load_upper"]),
                       mechanical_drift=drift,known_parallel_force=hardware,
                       inspected_spring_upper=spring,full_contact_upper=total,
                       all_324_parallel_upper=spring+hard_react/128,nominal_clearance_deficit=existing_deficit,
                       all_route_current_variation=1360*slope,old_sign_after_issue=tail,
                       post_cut_supplied_work_tail=Q(1,4),post_cut_off_force_upper=Q(1,4)+Q(22,25),
                       failed_housing=1360*Q(11,5)+2*68+Q(11,10)+hard_react))


class Feeder:
    """Alternating local prepaid cups and fixed-delay rectangular work profiles."""
    h = Q(1,8)
    def __init__(self):
        self.cups=[Q(2),Q(0)]
        self.parcels=[]
        self.now=Q(0)
        self.owner=0
        self.source=Q(0)
        self.converter_heat=Q(0)
        self.pilot=Q(1)
        self.pilot_heat=Q(0)
        self.local_dump=Q(0)
        self.remote=Q(0)

    def launch(self, connected):
        if self.pilot < 1:
            return "unfunded-clock"
        self.pilot -= 1
        self.pilot_heat += 1
        k=self.owner
        self.owner=1-k
        if not connected or self.cups[k]<2:
            return "refused"
        # Ownership changes, not physical location: this exact containing cup discharges over h.
        self.cups[k]-=2
        self.parcels.append(self.now)
        return "launched"

    @staticmethod
    def clipped(t):
        return max(Q(0),min(t,Feeder.h))

    def coast(self,dt,supply=True):
        t,end=self.now,self.now+dt
        need(dt>=0 and dt<=self.h,"Split at local work clock")
        if supply:
            gross=32*dt
            q=min(2-self.cups[self.owner],16*dt)
            p=min(1-self.pilot,8*dt)
            self.cups[self.owner]+=q
            self.pilot+=p
            self.source+=gross
            self.converter_heat+=gross-q-p
        self.remote+=16*sum(self.clipped(end-s-self.h)-self.clipped(t-s-self.h) for s in self.parcels)
        self.now=end
        self.parcels=[s for s in self.parcels if end<s+2*self.h]
        remain=sum(2-16*self.clipped(end-s-self.h) for s in self.parcels)
        need(3+self.source==sum(self.cups)+self.pilot+self.converter_heat+self.pilot_heat+self.remote+remain,
             "Shared winding stream created work")
        need(len(self.parcels)<=2 and remain<=4, "Unbounded physical transit")
        return remain


def feed_cut():
    stream=Feeder()
    need(stream.launch(True)=="launched","No first actual winding grant")
    stream.coast(stream.h)
    need(stream.launch(True)=="launched","No continuous powered pipeline")
    stream.coast(stream.h/2)
    before=stream.remote
    stream.coast(stream.h/2,False)
    need(stream.remote-before==1 and stream.launch(False)!="launched","Source cut recalled prior work")
    stream.coast(stream.h,False)
    after=stream.remote
    stream.coast(stream.h,False)
    need(after==4 and stream.remote==after,"Material cutoff/settlement incorrect")
    i,v=Q(11,5),Q(11,10)
    drive=v+i/4+Q(5,2)
    need(drive*i==Q(913,100) and drive*i<16 and drive< Q(33,8)+Q(1,10),
         "Winding joined to an underpowered end")
    off=-4-v-i/4
    need(i*off+i*i/4+4*abs(i)+i*v==0 and i*(drive-v-i/4)+i*i/4+i*v==drive*i,
         "Wrong shared shaft force, flyback or heat")
    return values(dict(transmitted_after_cut=stream.remote-before,final_received=stream.remote,
                       maximum_constant_drive_work=drive*i,registered_local_energy_per_lane=9,
                       hard_all_lane_input=1360*32,source_heat=stream.converter_heat+stream.pilot_heat))



def raw_placement():
    import fixed_island_model as domain
    import rx_restoration as marker
    classes=marker.power.catalogue()
    exterior_w = Q(4096,2**16)
    exterior_i = Q(4096,2**24)
    # Allow 4096 receiving bit shunts on this one raw circuit as well as its exterior sleeve noise.
    local_shunt = Q(4096,2**17)
    exterior_w += local_shunt
    exterior_i += local_shunt/99
    high=min(100*s.current-200**2*s.bleed-2*marker.power.MARKERS[k]*marker.HOLD-s.gain
             for k,s in classes.items())
    low=min(s.current-200*s.bleed-2*marker.power.MARKERS[k]*marker.HOLD/99-s.gain/100
            for k,s in classes.items())
    need(high>exterior_w and low>exterior_i, "Return coupling defeated a good raw rail")
    n=12*(6+2**98)+2
    groups=0
    for receiver in (2,100,n-2):
        near=set(domain.neighbors(n,receiver))
        paired=set(domain.installed_pair(n,receiver))
        for group in [domain.Group(n,receiver,"plant",k) for k in (0,1)]+[
                domain.Group(n,receiver,"maintenance",t) for t in range(40)]:
            providers=domain.group_providers(group)
            physical=[("primary" if not k else "auxiliary",j) for k,j in enumerate(providers)]
            weld={("primary",j) for j in near}
            main={k for k,v in enumerate(physical) if v in weld}
            pair={k for k,(kind,j) in enumerate(physical) if kind=="auxiliary" and j in paired}
            need(main=={0} and len(pair)<=2, "Main current weld was identified with auxiliary records")
            groups+=1
    # If three aux enable wires can be held inactive together, the same intact reader
    # can still see their previous three positive snapshots, plus five independent bad words.
    expanded=set(range(1,4))|set(range(4,9))
    need(len(expanded)==8, "Broader raw footprint countercase disappeared")
    return values(dict(checked_group_placements=groups,initial_high_work_margin=high,additional_terminal_shunt_load=local_shunt,
                       initial_cold_current_margin=low,remaining_high_work_margin=high-exterior_w,
                       remaining_cold_current_margin=low-exterior_i,
                       primary_fronts_in_current_weld=40,primary_slots_per_selected_group=1,
                       expanded_three_origin_six_incident_reach=len(expanded)))


def source_trials(path,cap):
    sys.path.insert(0,str(path))
    import b_handoff as hand
    import frame_pacing as fr
    import sender_eligibility as sender
    import world_channel as world
    seat=hand.seat; gate=hand.gate; rawsrc=hand.raw
    isa=seat.program.load_isa(); c,_=seat.candidate(isa)
    sites=fr.boundaries(isa,c)
    results=[]
    for old,adc_first,trip_first in product((0,1),(False,True),(False,True)):
        owner=2; other=1-old
        ecap=int(Q(json.loads((path/"parent_realization_results.json").read_text())["cost_bounds"]["actual_bank_capacity"]))
        U=rawsrc.SourceWork(owner,cap,cap/2)
        pop=12*(6+2**98)+2
        targets=tuple("region0/host"+str(n) for n in hand.wiring.incidence.neighbors(pop,owner))
        cpus=[fr.SourceParent(isa,c,bank=seat.charging.OperatingBank((owner,b),ecap,Q(ecap if b==old else 0)),targets=targets) for b in (0,1)]
        cpu=cpus[old]
        st=seat.SeatState(gate.parameters(c),owner,U,cpus,initial_driver=old)
        cpus[other].inhibit()
        st.positions[f"act{old}:0"]=hand.cam.WARM
        st.positions[f"cut{other}"]=st.p["CUT_LIMIT"]
        st.positions["cam"]=(13*old+9)*st.p["SEGMENT"]+st.p["SEGMENT"]//2
        st.positions["blend"]=other*st.p["BLEND_LIMIT"]
        source=fr.paced.TimedSource(cpu.bank,U)
        need(source.reform()=="formed-unpowered" and source.begin_entry(cpu.bank)
             and source.entry_flow(Q(source.ENTRY_WORK,rawsrc.CLEAR_RATE)),"No funded origin")
        bus=world.WorkBank(cpu,source)
        bus.world_gate=lambda:source.powered and cpu.powered and not cpu.recharge_inhibit
        clock=fr.paced.NativeClock(cpu,source,external_receivers=True,existing_bus=bus,adc_first=Q(1,4096),tx_first=Q(1,4096))
        line=lambda:hand.cam.ControlLine(words=[10]*8,valid=[True]*8)
        dest=gate.field.Destination(targets[0],other,11)
        bank=seat.SeatLiveBank.at_initial(st,old,source,line(),((dest,gate.InitialPulseRow(gate.field.PulseSelector(),line())),))
        trips=[seat.gates.Trip(b==old,False) for b in (0,1)]
        sam=hand.Handoff(st,{old:bank},trips)
        sam.remaining=Q(63,4096)+Q(4096)/fr.RATE
        route=sender.CommandLane(bus,1,tuple(source.receivers)[1],sender.Hold(Q(0),sender.NEUTRAL))
        drivers=fr.paced.timed_ports(isa)(c,source)
        class Ports(fr.SourcePorts):
            def perform(self,name,args,actor):
                if name=="send_command":
                    route.source_connected=trips[old].enabled and actor.powered and source.admission
                    return route.accept(args,actor)
                return super().perform(name,args,actor)
        ports=Ports(clock,drivers)
        class Cycle(fr.Cycle):
            IO=fr.Cycle.IO|{"send_command","world"}
        period=16*fr.D
        def visit(t):
            old_time=clock.now
            clock.run_before(t,lambda due:due[0])
            route.flow(t)
            need(sam.remaining>=t-old_time,"Source skipped an earlier handoff contact")
            sam.remaining-=t-old_time
            # Intact, fully formed maintenance streams; their 1360 full source draws use the same U.
            need(U.debit(1360*32*(t-old_time)), "Working maintenance feed starved")
        def finish_other_roots():
            while clock.due():
                clock.edge(clock.due()[0])
        pc,_,reg=sites["send_command"][-1]
        cpu.pc=pc
        cpu.R[reg:reg+2]=[1,sender.NEUTRAL+20*4096]
        cyc=Cycle(clock,ports,period)
        visit(cyc.time(1,4));need(cyc.capture()=="bound","No real SEND")
        visit(cyc.time(1,2));need(cyc.offer()=="issued","SEND not offered")
        visit(cyc.time(1));need(cyc.retire()=="retired" and route.live is not None,"No paid SEND child")
        packet=route.live
        source.raw_heads[0]=73
        source.I[1]=11
        source.I[6]=0
        pc,_,reg=sites["source_start_fast"][0]
        cpu.pc=pc;cpu.R[reg]=0
        cyc=Cycle(clock,ports,period)
        visit(cyc.time(1,4));need(cyc.capture()=="bound","No paid ADC parent")
        visit(cyc.time(1,2));need(cyc.offer()=="issued","No ADC child")
        visit(cyc.time(1));need(cyc.retire()=="retired" and source.job.live,"ADC did not survive")
        count=source.adc_bits.get(2052,6)
        last=clock.clocks["ADC"].due+(count-1)*clock.clocks["ADC"].period
        visit(last-period/2)
        pc,_,reg=sites["source_iadd_constant"][0]
        cpu.pc=pc;cpu.R[reg:reg+3]=[6,1,0]
        cyc=Cycle(clock,ports,period)
        visit(cyc.time(1,4));need(cyc.capture()=="bound","Scratch not captured")
        visit(cyc.time(1,2));need("ADC" in clock.due() and clock.now==last,"Lost true ADC edge")
        if adc_first: clock.edge("ADC")
        need(cyc.offer()=="issued","No shared scratch offer")
        if not adc_first: clock.edge("ADC")
        finish_other_roots()
        job=ports.scratch
        capture=cpu.pending
        visit(job.due)
        # This receiver's initial sampler offset is job.due on the working U > 1 prefix.
        # Its physical integrated remaining phase has just reached zero; there was no earlier sampler edge.
        need(sam.remaining==0,"Initial physical sampler phase did not reach the tied cut")
        before=U.stock
        if not trip_first: settled=job.settle(clock.now)
        need(sam.strobe(0)=="planned-trip" and before-U.stock==2048,"No paid zero-weight trip")
        if trip_first: settled=job.settle(clock.now)
        expected=0 if trip_first else (73 if adc_first else 11)
        need(source.I[1]==73 and source.I[6]==expected and cpu.pending is capture
             and not cpu.powered and not source.admission and not bank._vector_grant(dest),
             "Lost ADC, scratch, parent or trip identity")
        need(cpu.complete(ports)=="waiting" and st.positions[f"cut{old}"]==0 and route.live is packet,
             "Trip fabricated a retirement, physical CUT or packet cancellation")
        # The complete audited send suffix now has its own stock, apart from any cold CPU.
        route.flow(packet.due)
        need(route.hold.drive()==packet.word and route.live is None,"Previously paid SEND lost at phase nine")
        route.flow(packet.due+13)
        need(route.hold.drive()==sender.NEUTRAL and route.hold.word==packet.word,"Old level restarted")
        bus.audit();st.check_U_balance()
        results.append(values(dict(old_bank=old,adc_first=adc_first,trip_before_settle=trip_first,
                                   seed_adc_true_edges=count,tied_at=last,scratch_settlement=settled,
                                   final_source_I1=source.I[1],final_source_I6=source.I[6],
                                   cpu_retired=cpu.retired,trip_work=2048,finalized_send=packet.word,
                                   committed_to=tuple(packet.owner),true_old_world_weight=0)))
    return results


def replay(cap):
    # Numeric leaves and literal state machines come from exactly the pinned tree, including dynamic git imports.
    env=dict(os.environ)
    env["GIT_DIR"]=subprocess.check_output(["git","rev-parse","--absolute-git-dir"],cwd=HERE,text=True).strip()
    data=subprocess.check_output(["git","archive","--format=tar",BASE,"theories-and-designs/byzantine-control"],cwd=HERE.parents[2])
    with tempfile.TemporaryDirectory(prefix="b-lead-material-") as tmp:
        with tarfile.open(fileobj=io.BytesIO(data)) as archive:
            archive.extractall(tmp,filter="data")
        result=subprocess.run([sys.executable,"-B",str(Path(__file__).resolve()),"--source-slice",
                               str(Path(tmp)/PREFIX),str(cap)],env=env,capture_output=True,text=True,check=False)
        need(result.returncode==0,result.stderr)
        return json.loads(result.stdout)


def record():
    price=join_price()
    facts=root_and_factual(price)
    names=("SENDER-ELIGIBILITY.md","sender_eligibility.py","sender_eligibility_results.json","FRAME-PACING.md","frame_pacing.py",
           "frame_pacing_results.json","B-HANDOFF-TRIP.md","b_handoff.py","b_handoff_results.json")
    own=("B-LEAD-INSTALLATION.md","b_lead_installation.py","B-REFERENCE-RETURN.md","b_reference_return_results.json",
         "B-HOST-FLOW.md","b_host_flow_results.json","threshold_field_source_results.json","return_seat_results.json")
    return {"source_base":BASE,"source_sha256_lf":{f:sha256(raw(f).encode()).hexdigest() for f in names},
            "join_sha256_lf":{f:sha256((HERE/f).read_text(encoding="utf-8").encode()).hexdigest() for f in own},
            "budget":price,"contact":facts,"winding":feed_cut(),"flexures":flexure_checks(),"raw_paths":raw_placement(),"hardware":replay(Q(price["Ucap"]))}


if __name__=="__main__":
    if len(sys.argv)==4 and sys.argv[1]=="--source-slice":
        print(json.dumps(source_trials(Path(sys.argv[2]),Q(sys.argv[3]))))
    else:
        parser=argparse.ArgumentParser(description=__doc__)
        parser.add_argument("--write",action="store_true")
        args=parser.parse_args()
        result=record()
        out=HERE/"b_lead_installation_results.json"
        if args.write:
            out.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n",encoding="utf-8")
        else:
            need(result==json.loads(out.read_text(encoding="utf-8")),"B lead receipt changed")
        print("Checked same-bank SEND, ADC, scratch, phase-nine trip, contact load and closed reference.")

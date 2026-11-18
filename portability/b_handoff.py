"""Local zero-old-weight handoff in B with a fixed earlier bank interval."""
import argparse
from fractions import Fraction as Q
from hashlib import sha256
from pathlib import Path
import json

import a80_handoff_trip as A
import handoff_contact
import return_seat as seat
import source_clock_wiring as wiring

HERE=Path(__file__).resolve().parent
need=seat.checks
gate=seat.incumbent
raw=seat.raw
cam=gate.cam


class Handoff(seat.StopSampler):
    def __init__(self,state,banks,trips):
        super().__init__(state)
        self.banks=dict(banks)
        self.trips=trips
        need(len(trips)==2 and all(b.side==i and b.fixture is state and
             b.native_input is not None and b.native_input.payer is state.source_work
             and b.machine is state.machines[i] and b.native_input.operating_bank is b.machine.bank
             for i,b in self.banks.items()),"Foreign material handoff")
    def strobe(self,force,threshold=Q(29)):
        s=self.state
        old=handoff_contact.retiring_side(s.abort_carrier.normal,s.abort_carrier.phase,
                    s.positions["cam"],s.positions["blend"],s.p["SEGMENT"],s.p["BLEND_LIMIT"])
        funded=not s.held_plane and s.U>=seat.gates.PREDICATE_WORK
        out=super().strobe(force,threshold)
        if not funded or old is None:return out
        # This local probe requires the old pole to be explicitly installed.
        bank=self.banks[old]
        trip=self.trips[old]
        was=trip.enabled
        trip.enabled=False
        if not s.output[f"cam-stop:{13*(1-old)+1}"]:
            trip.armed=False
        s.output[f"trip{old}"]=0
        if was:
            # The physical nonbulk launch breaker and its existing prepaid
            # quench contacts. Do not move the bulk CUT, any pose or any old
            # receiving terminal, and do not clear physical C or a pending head.
            bank.machine.inhibit()
            bank.native_input.cold_cut()
            bank._break()
        return "planned-trip" if was else "already-off"


def local_fixture(isa,c,old,*,U,regular=True):
    limits=gate.parameters(c)
    owner=2
    cap=int(Q(json.loads((HERE/"parent_realization_results.json").read_text())["cost_bounds"]["actual_bank_capacity"]))
    prices=json.loads((HERE/"sender_eligibility_results.json").read_text())["prices"]
    ucap=(Q(prices["revised_U_capacity"])-Q(json.loads(
        (HERE/"b_host_flow_results.json").read_text())["paid_trigger"]["additional_capacity"]))
    store=raw.SourceWork(owner,ucap,Q(U))
    pop=12*(6+2**98)+2
    targets=tuple("region0/host"+str(t) for t in wiring.incidence.neighbors(pop,owner))
    cpu=[seat.charging.FramedParent(isa,c,bank=seat.charging.OperatingBank((owner,b),cap,Q(cap if b==old else 0)),
                                 targets=targets) for b in (0,1)]
    subset=seat.SeatState(limits,owner,store,cpu,initial_driver=old)
    other=1-old
    cpu[other].inhibit()
    subset.positions[f"act{old}:0"]=cam.WARM
    subset.positions[f"cut{other}"]=limits["CUT_LIMIT"]
    source=wiring.initial.local_source_at_initial_entry(store,cpu[old].bank,True,False,pop)
    lane=raw.RawLane(pop,raw.LaneId(owner,old,0,0),store)
    source.attach(lane)
    bus=seat.charging.JointCharge(cpu[old].bank,cpu[old],(*source.slots,source.adc),wiring.paced.DELTA)
    line=lambda:cam.ControlLine(words=[10]*8,valid=[True]*8)
    dest=gate.field.Destination(targets[0],other,11)
    installed=seat.SeatLiveBank.at_initial(subset,old,source,line(),
                ((dest,gate.InitialPulseRow(gate.field.PulseSelector(),line())),))
    # Take a local challenge cut with the physical recipient at its opposite
    # blend stop. This is not evidence of reachable positive successor C/P.
    subset.positions["cam"]=(13*old+9)*limits["SEGMENT"]+limits["SEGMENT"]//2
    subset.positions["blend"]=other*limits["BLEND_LIMIT"] if regular else Q(limits["BLEND_LIMIT"],2)
    trips=[seat.gates.Trip(i==old,False) for i in (0,1)]
    pulses=Handoff(subset,{old:installed},trips)
    return installed,dest,lane,bus,pulses


def tests(isa,c,old):
    bank,dest,lane,bus,pulse=local_fixture(isa,c,old,U=2**34)
    s=bank.fixture;src=bank.native_input;cpu=bank.machine
    other=1-old
    bus.flow_full_delivery(2*wiring.paced.DELTA,source_powered=True)
    pc=c.labels["publish_plant"]+6
    code=c.image[pc];op,_,r,n,ix=isa.decode(code)
    need(op==isa.IO and n==1 and isa.PRIMITIVES[ix]=="source_start_fast","Wrong paid source code")
    cpu.pc=pc;cpu.R[r]=0
    src.raw_heads[0]=917
    ports=wiring.paced.timed_ports(isa)(c,src)
    need(cpu.recharge() and cpu.launch() and cpu.complete(ports,pause_after_offer=True)=="waiting"
         and cpu.io_paid and src.job.live,"No real issued source child")
    child=src.job
    capture=cpu.pending
    trip=pulse.trips[old]
    trip.armed=True
    before=(tuple(s.E),tuple(s.positions.items()),tuple(s.machines[other].C),s.machines[other].powered)
    oldU=s.U
    pulse.remaining=Q(0)
    need(pulse.strobe(0)=="planned-trip" and s.U==oldU-2048 and s.positions[f"cut{old}"]==0
         and not trip.enabled and not trip.armed and not cpu.powered and not src.admission,
         "Unpaid or destructive action at the old donor")
    need((tuple(s.E),tuple(s.positions.items()),tuple(s.machines[other].C),s.machines[other].powered)==before
         and cpu.pending is capture and src.job is child and not bank._vector_grant(dest),
         "The handoff erased storage or granted readiness at its sibling")
    # Independent previously funded raw conversion still has its own clock.
    count=src.adc_bits.get(2052,6)
    for _ in range(count):src.adc_tick()
    need(src.valid and src.I[1]==917 and not child.live and cpu.complete(ports)=="waiting"
         and not trip.transition(s.E[old],s.p["EOFF"],s.p["EON"],power=True)[0],
         "Earlier physical source incarnation or spent CPU grant was replayed")
    # Quenching >1 aperture occurs using its actual nonrefundable old parcel.
    bank.drain_source_leaves(Q(1))
    need(not bank._vector_grant(dest) and bank.rows[dest].pulse.cut,"Prepaid local apertures stayed live")
    s.check_U_balance();bus.balance()
    return dict(old=old,source_U_spent=oldU-s.U,bulk_cut=s.positions[f"cut{old}"],
                old_CPU_can_issue=cpu.powered,retained_ADC=src.I[1],
                retained_same_parent=cpu.pending is capture,unformed_sibling_made_ready=s.machines[other].powered)


def boundaries(isa,c):
    out=[]
    for options in (dict(U=2047),dict(U=4096,regular=False),dict(U=4096)):
        bank,_,_,_,pulse=local_fixture(isa,c,0,**options)
        if options==dict(U=4096):bank.fixture.held_plane=True
        pulse.remaining=0
        state=pulse.strobe(0)
        need(bank.machine.powered and pulse.trips[0].enabled,"Failed/held clock granted a planned break")
        out.append(state)
    seg=c.constants["SEGMENT"];blend=c.constants["BLEND_LIMIT"]
    for i in range(2):
        pos=(13*i+9)*seg
        for rawpos in (pos+Q(seg,4),pos+Q(3*seg,4),26*seg):
            need(handoff_contact.retiring_side(True,"NORMAL",rawpos,(1-i)*blend,seg,blend) is None,
                 "Open contact cannot include the next material band")
    return out


def bounds(c):
    k=c.constants
    orbit=json.loads((HERE/"normal_orbit_results.json").read_text())["B_sampled_candidate"]["timer"]
    source=json.loads((HERE/"receiver_lease_results.json").read_text())["interval"]
    sender=json.loads((HERE/"sender_eligibility_results.json").read_text())
    stage=json.loads((HERE/"threshold_geometry_results.json").read_text())["arithmetic"]
    H=Q(2*10**13);rate=Q(stage["raw_rate"])
    watch=Q(orbit["private_job_window"])
    D=Q(1,2**30)
    sample=Q(101,100)
    approach=Q(k["SEGMENT"],4)/Q(11,10)-sample
    tail=Q(sender["physical"]["max_delay"])+Q(sender["physical"]["longest_hold"])+Q(sender["physical"]["old_sign_current_tail"])
    need(approach>tail and approach>Q(source["delivery"])+1023+2*D,
         "Observed cleanup tails can survive into the retired data interval")
    region=(Q(k["WARM_AT"])-Q(stage["physical_inputs"]["vector_driver_at"]))/Q(11,10)
    setup=Q(stage["vectors"]["first_after_route_engagement"])
    spare=region-setup-watch
    earlier=2*H+2*watch
    p,sigma,occupied=1,3,2
    full=p+occupied+int(sigma+rate*earlier)
    need(spare>146000000 and full==6 and rate*earlier<1,
         "Source donor cannot cover a full earlier watchdog horizon")
    ph=sender["prices"]
    common=json.loads((HERE/"world_channel_results.json").read_text())["source"]
    vector=json.loads((HERE/"b_host_flow_results.json").read_text())["paid_trigger"]
    scratch=json.loads((HERE/"frame_pacing_results.json").read_text())["certificate"]
    charge=2*2*41*Q(1,2**48)
    physical=Q(ph["remaining_reaction"])+Q(vector["remaining_reaction"])-Q(common["remaining_reaction"])
    Ucap=Q(ph["revised_U_capacity"])-Q(vector["additional_capacity"])
    pressure=(Q(ph["remaining_U_floor_above_quarter"])-Q(3,4)*Q(vector["additional_capacity"])
              -Q(scratch["extra_U_burst"])-2*Q(scratch["extra_U_rate"]))
    supply=Q(ph["remaining_supply"])-Q(scratch["extra_U_rate"])
    bath=(Q(ph["remaining_bath"])+Q(vector["all_mode_bath_margin_after_slot_terminals"])
          -Q(common["combined_bath_margin"])-4*41*2*Q(scratch["extra_U_rate"]))
    need(physical>charge and 494+32==526<=2048 and min(pressure,supply,bath,Ucap)>0,
         "Co-installed material/operating point is underfunded")
    return dict(planned_trip_work_upper=526,existing_paid_strobe=2048,
                old_SEND_tail=tail,strict_shutdown_margin_before_shunt=approach,
                full_watchdog=watch,formation_after_driver=setup,available_driver_approach=region,
                strict_bank_sponsorship_slack=spare,paid_reaction_slack=physical-charge,
                common_U_capacity=Ucap,free_U_above_pressure_floor=pressure,supply_slack=supply,bath_slack=bath,
                retrospective_planning_width=earlier,extra_raw_accrual=rate*earlier,
                retrospective_count=full,mission_H=H,relative_cover_must_be_query_specific=True)


def main():
    isa=seat.program.load_isa();c,_=seat.candidate(isa)
    need(A.retiring_side is handoff_contact.retiring_side,"Different physical predicate in A80 and B")
    x=dict(native=[tests(isa,c,side) for side in (0,1)],boundaries=boundaries(isa,c),quantitative=bounds(c),
           source_files={n:sha256((HERE/n).read_bytes().replace(b"\r\n",b"\n")).hexdigest() for n in
                ("B-HANDOFF-TRIP.md","b_handoff.py","handoff_contact.py","a80_handoff_trip.py",
                 "return_seat.py","return_seat_results.json","receiver_lease_results.json",
                 "sender_eligibility_results.json","normal_orbit_results.json","threshold_geometry_results.json",
                 "b_host_flow_results.json","frame_pacing_results.json","world_channel_results.json")})
    return gate.normalize(x)


if __name__=="__main__":
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument("--write",action="store_true");args=ap.parse_args()
    result=json.dumps(main(),sort_keys=True,indent=2)+"\n";path=HERE/"b_handoff_results.json"
    if args.write:path.write_text(result,encoding="utf8",newline="\n")
    else:need(path.read_text(encoding="utf8")==result,"Different B handoff receipt")
    print("Verified both physical donor orientations, finite cutoff and strictly earlier bank formation")

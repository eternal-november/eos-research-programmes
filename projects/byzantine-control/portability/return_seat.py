"""Candidate paid RETURN seat and directional coupling; the installed source is untouched."""
import argparse
from fractions import Fraction as Q
import json
from pathlib import Path

import abort_protocol_alternative as old
import gate_source_completion as gates
import input_lifecycle as raw
import legacy_realization as legacy
import parent_realization as parent
import parent_retirement as retirement
import shared_bank_charging as charging
import threshold_design as design
import threshold_gate_source as incumbent
import threshold_initialization as initialization
import threshold_program_model as program


HERE=Path(__file__).resolve().parent
PIN="07f29286fcfd570299c7610bf9f9acd6267f2852"
checks=old.need


def record(name):
    return json.loads(legacy.text_at(PIN,"portability/"+name))


def candidate(isa):
    src=isa.SOURCE
    base=src.read_text(encoding="utf-8-sig")
    checks(base==legacy.text_at(PIN,"portability/threshold_program_source.py"),"Source program changed")
    code=old.edited(base)
    # Exact raw zero comparisons. An unavailable source word is not zero.
    template=code[code.index("def contact(t, relative):"):code.index("def progress(")]
    zero=template.replace("def contact(","def contact_zero(").replace("key, 1)","key, 0)")
    wrong="""def geometry_wrong(t):
    if contact(t, ANCHOR_IS_A):
        a = 0
    elif contact(t, ANCHOR_IS_B):
        a = 1
    else:
        return 0
    b = 1 - a
    return contact_zero(t, BLEND_AT_A + a) or contact_zero(t, ISO_SEATED_A + b) or contact_zero(t, SHUNT_SEATED_A + b) or contact_zero(t, CUT_OPEN_A + b) or contact_zero(t, ACT_ZERO_A + b * BAYS) or contact_zero(t, CLAMP_OPEN_A + b) or contact_zero(t, RESET_OPEN_A + b) or contact_zero(t, CAM_ENTRY_A + a)

"""
    code=old.replace_once(code,"def progress(",zero+wrong+"def progress(")
    code=old.replace_once(code,"    if ready and contact(t, CAM_ENTRY_A + anchor):",
                          "    if ready and contact(t, ISO_SEATED_A + cold) and contact(t, SHUNT_SEATED_A + cold) and contact(t, CAM_ENTRY_A + anchor):")
    code=old.replace_once(code,"""        if old_exit:
            emit(t, MODE_PORT, cold, 0, -FORCE)
        if w[base + EXITING_ABORT]:""","""        if old_exit:
            if geometry_wrong(t):
                emit(t, MODE_PORT, cold, 0, FORCE)
            else:
                emit(t, MODE_PORT, cold, 0, -FORCE)
        if w[base + EXITING_ABORT]:""")
    bounds_base=isa.WorkBound
    class Bounds(bounds_base):
        def limit(self,fn,node):
            return super().limit("contact" if fn=="contact_zero" else fn,node)
    try:
        isa.SOURCE=old.Text(code)
        isa.WorkBound=Bounds
        c=program.compile_program(isa,design.design(isa))
        b=program.bounds(isa,c)
    finally:
        isa.SOURCE=src
        isa.WorkBound=bounds_base
    return c,b


class SeatState(incumbent.SharedContacts):
    def check_cleanup_motion(self,name,new):
        checks(self.held_plane or self.abort_carrier.phase!="RETURN" or new==self.positions[name],
               "No ordinary cleanup motion through the interior RETURN manifold")

    def blend_arc(self,position,duration):
        self.check_cleanup_motion("blend",position)
        return super().blend_arc(position,duration)

    def carrier_arc(self,side,position,duration):
        self.check_cleanup_motion(f"carrier{side}",position)
        return super().carrier_arc(side,position,duration)

    def enter_held_plane(self,previous):
        sampler=getattr(self,"return_sampler",None)
        if not previous and self.held_plane and sampler is not None:
            sampler.held_positive=not sampler.key[self.keeper]
            sampler.held_negative=sampler.key[self.keeper]

    def held_takeover(self,block,value):
        previous=self.held_plane
        status=super().held_takeover(block,value)
        self.enter_held_plane(previous)
        return status

    def physical_pose_request(self,request):
        previous=self.held_plane
        status=super().physical_pose_request(request)
        self.enter_held_plane(previous)
        return status

    def abort_arc(self,velocity,duration):
        # Old velocity-only RETURN calls could seat by reaching zero.
        checks(self.abort_carrier.phase in ("NORMAL","ENTERING"),"FULL/RETURN use actual shaft and funded stop")
        return super().abort_arc(velocity,duration)


class SeatLiveBank(incumbent.LiveSourceBank):
    def activation_arc(self,new,dt,*,working_contact):
        self.fixture.check_cleanup_motion(f"act{self.side}:0",new)
        return super().activation_arc(new,dt,working_contact=working_contact)


class StopSampler(gates.PredecessorSampler):
    """One actual target U, coherent pose/E strobe, two held directional levels."""
    def __init__(self,state):
        super().__init__(state)
        self.key=(False,False)
        state.return_sampler=self
        self.held_positive=self.held_negative=False
        self.seated=self.rebounded=self.released=0

    def held_request(self,request,force=Q(0)):
        """A fixed local physical-site request; no permission from current C."""
        s=self.state
        checks(isinstance(request,gates.Captured) and request.owner==s.owner,"Foreign physical request")
        valid=(request.kind=="return-pole" and request.target in ("out","in","seat")
               and type(request.value) is int and request.value in (0,1))
        checks(abs(force)<=176+Q(11,10)+design.EXTRA_REACTION,"Unrated held pressure")
        before=s.held_plane
        price=gates.UPDATE_WORK*(1+int(valid and not before))
        work=Q(price) if s.U>=price else min(s.U,Q(gates.UPDATE_WORK))
        s.U-=work
        s.heat+=work
        s.check_U_balance()
        if work!=price:
            return "partial/no-change"
        if not valid:
            return "uninstalled"
        s.held_plane=True
        s.enter_held_plane(before)
        if request.target in ("out","in"):
            if request.target=="out":self.held_positive=bool(request.value)
            else:self.held_negative=bool(request.value)
            return "held-direction"
        car=s.abort_carrier
        # Charged direct failing pole can bypass the geometric interlock.
        # It never supplies displacement to the actual carriage.
        if request.value and car.phase=="RETURN" and car.position==0 and force < -29 and "abort" not in s.jammed:
            car.phase="NORMAL";car.normal=True;car.active=car.full=False
            s.output["abort"]=car.raw();s.output["normal-cam"]=1
            return "held-false-seat"
        return "held-no-engagement"

    def strobe(self,force,threshold=Q(29)):
        s=self.state
        checks(abs(force)<=Q(11,5)*80+Q(11,10)+design.EXTRA_REACTION and 28<=threshold<=29,
               "Unrated actual seating pressure")
        if s.held_plane:
            return "held/no-nominal-strobe"
        checks(self.remaining==0,"No clock edge")
        car=s.abort_carrier
        checks(s.positions["abort"]==car.position,"Carriage alias lost")
        s.check_rigid_seats()
        # One indivisible capture at the physical edge. No previously stored
        # key/low-E value can be used to open the NORMAL terminal.
        self.remaining=self.period
        self.samples+=1
        paid=min(s.U,Q(gates.PREDICATE_WORK))
        s.U-=paid
        s.heat+=paid
        self.work+=paid
        s.check_U_balance()
        if paid!=gates.PREDICATE_WORK:
            return "partial/still-held"
        r=gates.physical_contact_snapshot(s)
        predecessors,_=gates.fold_contact_snapshot(r,1)
        for j,bit in enumerate(predecessors):
            s.output[f"cam-stop:{j}"]=int(bit)
        keys=[]
        prepark=[]
        strong=[]
        for a in (0,1):
            b=1-a
            geometry=(r["blend",a] and s.positions[f"iso{b}"]==s.limits[f"iso{b}"]
                      and s.positions[f"shunt{b}"]==s.limits[f"shunt{b}"] and r["cut-end",b]
                      and r["zero",b,0] and r["clamp-zero",b] and r["reset-zero",b])
            keys.append(geometry and r["cam-entry",a])
            prepark.append(geometry and r["low-E",b])
            strong.append(keys[-1] and r["low-E",b])
        self.key=tuple(keys)
        s.rewind_sample=tuple(prepark)
        s.cleanup_sample=tuple(strong)
        a=s.keeper=gates.keeper(s.keeper,s.positions["blend"],s.p["BLEND_LIMIT"])
        if "abort" in s.jammed:
            return "jam/observed"
        if car.phase=="RETURN" and car.position==0 and strong[a] and force < -threshold:
            car.phase="NORMAL"
            car.normal=True
            car.active=car.full=False
            self.seated+=1
            result="normal-seat"
        elif car.phase=="RETURN" and car.position==car.length and not keys[a] and force>threshold:
            car.phase="FULL"
            car.full=True
            car.active=True
            self.rebounded+=1
            result="full-stop"
        elif car.phase=="FULL" and car.position==car.length and strong[a] and force < -threshold:
            car.phase="RETURN"
            self.released+=1
            result="return-release"
        else:
            result="observed/held"
        s.output["abort"]=car.raw()
        s.output["normal-cam"]=int(car.normal)
        return result

    def velocity(self,force,threshold=Q(29),mobility=Q(2)):
        s=self.state
        car=s.abort_carrier
        checks(car.phase in ("FULL","RETURN") and 28<=threshold<=29
               and 0<mobility<=2 and abs(force)<=176+Q(11,10)+design.EXTRA_REACTION,"Incorrect physical chart")
        if "abort" in s.jammed or car.phase=="FULL":
            return Q(0)
        speed=min(incumbent.cam.VMAX,max(Q(0),(abs(force)-threshold)/mobility))
        out_open=self.held_positive if s.held_plane else not self.key[s.keeper]
        in_open=self.held_negative if s.held_plane else self.key[s.keeper]
        if force>0 and out_open and car.position<car.length:
            return speed
        if force<0 and in_open and car.position>0:
            return -speed
        return Q(0)

    def constant_arc(self,efforts,duration):
        """Rated externally supplied fixed efforts, exact local work before next strobe."""
        s=self.state
        checks(len(efforts)<=80 and all(abs(f)<=Q(11,5) for f in efforts),"Ordinary fixed winding limit")
        duration=Q(duration)
        checks(0<=duration and self.clock_rate()*duration<=self.remaining,"Split at the paid sampling edge")
        car=s.abort_carrier
        start=car.position
        v=self.velocity(sum(efforts,Q(0)))
        car.position=max(Q(0),min(car.length,start+duration*v))
        s.positions["abort"]=car.position
        works=[f*(car.position-start) for f in efforts]
        checks(sum(works,Q(0))>=0,"Directional pawl generated work")
        s.mechanical_input+=sum(works,Q(0))
        s.mechanical_heat+=sum(works,Q(0))
        self.flow_clock(duration)
        return works


def fixture(isa,c,*,a=0,x=Q(1,10),wrong="cam",U=1<<42):
    p=incumbent.parameters(c)
    cap=int(p["EMAX"])
    banks=[charging.OperatingBank((100,b),cap,cap if b==a else Q(0)) for b in (0,1)]
    cpus=[charging.FramedParent(isa,c,bank=bank) for bank in banks]
    Ucap=Q(record("threshold_gate_source_results.json")["costs"]["upstream_capacity"])
    purse=raw.SourceWork(100,Ucap,U)
    s=SeatState(p,100,purse,cpus)
    s.keeper=a
    b=1-a
    for axis,value in (("blend",a*p["BLEND_LIMIT"]),("cam",a*13*p["SEGMENT"]),
                       (f"iso{b}",p["ISO_LIMIT"]),(f"shunt{b}",p["ISO_LIMIT"]),(f"cut{b}",p["CUT_LIMIT"])):
        s.positions[axis]=Q(value)
    if wrong=="cam":
        s.positions["cam"]+=1
    elif wrong in ("iso","shunt","cut"):
        s.positions[wrong+str(b)]-=1
    elif wrong=="act":
        s.positions[f"act{b}:0"]=Q(1)
    elif wrong in ("clamp","reset"):
        s.positions[wrong+str(b)]=Q(1)
    elif wrong=="blend":
        s.positions["blend"]+=1 if a==0 else -1
    else:
        checks(wrong is None,"Unknown physical initialization")
    car=s.abort_carrier
    car.phase="RETURN";car.normal=False;car.active=car.full=True;car.position=Q(x)
    s.positions["abort"]=car.position
    s.output["normal-cam"]=0;s.output["abort"]=car.raw()
    return s,StopSampler(s)


def native_helpers(isa,c,b):
    full={"ABORT_FULL":1,"NORMAL_STOP":0,"MODE":0,"CAM_ENTRY_A":1}
    observations={}
    tests={"good-park":({},None),"off-cam":({"CAM_ENTRY_A":0},"REWIND_PORT"),
           "iso-not-seated":({"ISO_SEATED_B":0},"ISO_PORT"),"shunt-not-seated":({"SHUNT_SEATED_B":0},"SHUNT_PORT"),
           "wrong-cut":({"CUT_OPEN_B":0},"CUT_PORT"),"energy-high":({"POWER_OFF_B":0},None)}
    for name,(changes,action) in tests.items():
        arms=[]
        for x in (0,1):
            row=dict(view=full|changes,private={"EXITING_ABORT":x})
            if action:
                row["armed"]=action
            ans=old.execute(isa,c,b,row)
            arms.append(ans["packet"])
            if name=="good-park":
                checks(ans["packet"][3:5]==[-20,0],"Parked sign diverged")
            elif action:
                checks(ans["packet"][3]==20 and ans["packet"][4]==c.constants[action],"Wrong-key cleanup sign/action")
        observations[name]=arms
    # A missing value is different from the positive physical zero used above.
    p=program.ports_class(isa)(c);m,v=program.helper_fixture(isa,c,p,0,0)
    k=c.constants;v[k["ABORT_FULL"]]=1;v[k["NORMAL_STOP"]]=0;v[k["CAM_ENTRY_A"]]=isa.WORD_MASK
    p.set_view(0,v);m.W[k["TARGET_BASE"]+k["EXITING_ABORT"]]=1
    m.W[k["TARGET_BASE"]+k["STAGE_ID"]]=27
    program.call(isa,c,p,"helper",(0,),b["instruction_upper_bounds"]["helper"]+64,m)
    word=list(next(z for z in reversed(p.events) if z[0]=="command")[2:])
    checks(word[3]==-20,"Unavailable CAM key fabricated strict wrong-key evidence")
    observations["unavailable-cam-old-X"]=word
    return observations

def reach_edge(sampler):
    checks(sampler.clock_rate()==1,"This chart assumes full sampler power")
    sampler.flow_clock(sampler.remaining)


def check_activation_entry(isa,c):
    existing,_=fixture(isa,c)
    s=SeatState(existing.p,100,existing.source_work,existing.machines,initial_driver=0)
    s.positions["cut1"]=s.p["CUT_LIMIT"]
    m=s.machines[1]
    m.inhibit()
    m.setter.reset_control_inhibit=True  # Actual initial cold-side reset pole.
    native=initialization.local_source_at_initial_entry(s.source_work,m.bank,False,False,12*(6+2**98)+2)
    control=lambda:incumbent.cam.ControlLine(words=[0]*8,valid=[True]*8)
    target=incumbent.field.Destination(m.setter.targets[0],0,10)
    pulse=incumbent.field.PulseSelector(cut=True,reset_control_inhibit=True)
    live=SeatLiveBank.at_initial(s,1,native,control(),[(target,incumbent.InitialPulseRow(pulse,control()))])
    checks(live.activation_arc(0,Q(1),working_contact=False)=="no-upward-crossing","Lost the normal calling interface")
    # Enter an independent, specified gate-method test cut with the actual
    # bank/row, rather than claiming this trace commissioned a whole return.
    s.abort_carrier.phase="RETURN"
    s.abort_carrier.full=True
    s.abort_carrier.normal=False
    s.abort_carrier.position=s.positions["abort"]=Q(1)
    try:
        live.activation_arc(1,1,working_contact=False)
    except ValueError:
        pass
    else:
        raise ValueError("Live receiver ACT crossed a closed interior gate")
    checks(live.activation_arc(0,1,working_contact=False)=="no-upward-crossing" and live.activation==0,
           "Stationary RETURN starved the old receiver continuation")
    return True


def challenge(isa,c):
    s0,test=fixture(isa,c,U=2047)
    c0=s0.abort_carrier
    test.key=(True,True)
    # A preloaded open direction lets the actual inward drive reach the stop.
    works=test.constant_arc([Q(-2)]*34,1)
    checks(c0.position==0 and c0.phase=="RETURN" and sum(works)==Q(34,5),"Old direction skipped the real stop")
    checks(test.strobe(-68)=="partial/still-held" and s0.U==0 and c0.phase=="RETURN"
           and test.key==(True,True),"An unfunded edge seated or erased old levels")
    test.flow_clock(5)
    checks(test.remaining==test.period,"An empty clock accumulated credit")
    results=[]
    for a in (0,1):
        for bad in ("blend","iso","shunt","cut","act","clamp","reset","cam",None):
            s,t=fixture(isa,c,a=a,x=0,wrong=bad)
            s.cleanup_sample=(True,True)
            t.key=(True,True)
            reach_edge(t)
            outcome=t.strobe(-68)
            checks((outcome=="normal-seat")== (bad is None) and s.U==2**42-2048,"Missed a physical key or its price")
            results.append([a,bad,outcome])
    s,t=fixture(isa,c,x=0,wrong=None)
    for fn in (lambda:s.blend_arc(Q(1),Q(1)),lambda:s.carrier_arc(1,Q(1),Q(1)),lambda:s.abort_arc(Q(-1),Q(1))):
        try:
            fn()
        except ValueError:
            pass
        else:
            raise ValueError("Old ordinary pose entry point bypassed the directional RETURN chart")
    s.blend_arc(s.positions["blend"],1)
    s.carrier_arc(1,s.positions["carrier1"],1)
    # A different admitted initial bank stock on the actual operating cell.
    s.machines[1].bank.stock=s.p["EOFF"]
    s.cleanup_sample=(True,True)
    reach_edge(t)
    checks(t.strobe(-68)=="observed/held" and t.key[0] and not s.cleanup_sample[0],"Old low-E level released at equality")
    s,t=fixture(isa,c,x=0,wrong=None)
    reach_edge(t)
    checks(t.strobe(0)=="observed/held" and s.abort_carrier.phase=="RETURN","Status alone supplied seating pressure")
    s.jammed.add("abort")
    reach_edge(t)
    checks(t.strobe(-68)=="jam/observed" and s.abort_carrier.phase=="RETURN","Jammed carriage seated")
    ties=[]
    for failed_first in (True,False):
        s,t=fixture(isa,c,x=0,wrong=None)
        reach_edge(t)
        if failed_first:
            s.held_takeover("vector-driver:0",0)
        answer=t.strobe(-68)
        if not failed_first:
            s.held_takeover("vector-driver:0",0)
        ties.append([answer,s.abort_carrier.phase,str(s.source_work.spent)])
    checks(ties[0][:2]==["held/no-nominal-strobe","RETURN"] and ties[1][:2]==["normal-seat","NORMAL"],
           "Collapsed a real possible ordering at the seat")
    s,h=fixture(isa,c,x=0,wrong="shunt")
    event=gates.Captured(s.owner,"return-pole","seat",1,"fixed-seat")
    checks(h.held_request(event,-68)=="held-false-seat" and s.U==2**42-2048,
           "Charged failure no longer has its specified independent physical effect")
    s,h=fixture(isa,c,x=5,wrong="cam")
    held=gates.Captured(s.owner,"return-pole","in",1,"fixed-inward-pole")
    checks(h.held_request(held)=="held-direction" and h.constant_arc([Q(-2)]*34,Q(1))[0]>0
           and h.clock_rate()==0 and h.remaining==h.period,"Held physical motion was falsely stopped with its sampler")
    return dict(checked_actual_ACT_entry=check_activation_entry(isa,c),
                charged_false_seat_with_wrong_shunt=True,held_drive_moves_with_sampler_stopped=True,
                actual_physical_keys=results,partial_pulse_paid=2047,preloaded_direction_to_stop_work=str(sum(works)),
                strict_energy_equality_holds=True,zero_pressure_holds=True,jam_holds=True,ordered_capture_and_takeover=ties)


class IsolatedDecay:
    """The same bank's exact E(t)=E0 exp(-t/10); only a strict comparator is used."""
    def __init__(self,initial):
        self.initial=initial
        self.elapsed=Q(0)
    def __lt__(self,value):
        checks(value>0,"Positive physical threshold required")
        if self.elapsed==0:
            return self.initial<value
        x=self.elapsed/10
        ratio=self.initial/value
        term=total=Q(1)
        for n in range(1,257):
            term*=x/n
            total+=term
            if total>ratio:
                return True
            if x<n+2 and total+(term*x/(n+1))/(1-x/(n+2))<ratio:
                return False
        raise ValueError("Threshold not separated at this resolution")


def energy_wait(isa,c):
    s,t=fixture(isa,c,x=0,wrong=None)
    E=IsolatedDecay(2*s.p["EOFF"])
    checks(E.initial<=s.machines[1].bank.capacity,"High initial E escaped physical capacity")
    s.machines[1].bank.stock=E
    s.cleanup_sample=(True,True)
    seq=[]
    for _ in range(7):
        # Cut connected, no external inflow, T=0 and no other draw on
        # this inactive bank. The energy loss flows into its local bleed.
        E.elapsed+=t.remaining
        reach_edge(t)
        seq.append(t.strobe(-68))
    checks(seq==["observed/held"]*6+["normal-seat"] and t.samples==7
           and s.machines[1].bank.stock is E and s.U==2**42-7*2048,
           "Current E, elapsed bleed or seat billing was bypassed")
    return dict(initial_E=str(E.initial),clocked_outcomes=seq,actual_fixture_U=str(t.work),
                retained_E="E0 exp(-7/10)",local_bleed_heat="E0 (1-exp(-7/10))",
                scope="Isolated inactive, cut, T=0 chart; symbolic stock comparisons are exact.")


def mechanical_trace(isa,c,*,near_zero=False):
    # A fully transported, unmodified paired-winding law from the plant.
    trans,_=legacy.module_at(PIN,"local-control/transducer_model.py","_return_seat_windings")
    if near_zero:
        s,t=fixture(isa,c,x=Q(1,10),wrong="shunt")
        t.key=(True,True)
        mode=trans.Pair(trans.Channel(1,0.0),trans.Channel(-1,2.8))
        rewind=trans.Pair()
    else:
        s,t=fixture(isa,c,x=Q(10000)-Q(11,10000))
        t.remaining=Q(1,1000)
        mode=trans.Pair(trans.Channel(1,2.8),trans.Channel(-1,0.0))
        rewind=trans.Pair(trans.Channel(1,0.0),trans.Channel(-1,2.8))
    number=34
    energy_capacity=int(s.p["EMAX"])
    # Equal physical fields on distinct donors are computed once by symmetry.
    # Each electrical feed below has its own installed, finite operating stock.
    feeds=[charging.OperatingBank((origin,0),energy_capacity,1<<54) for origin in range(number)]
    elapsed=Q(0)
    total_work=0.0
    events=[]
    def force(p):
        return Q(str(number*p.force))
    def interval(dt,am,ac,vcam=Q(0)):
        nonlocal elapsed,total_work
        checks(dt>0 and dt<=t.remaining,"Split the sampled trace")
        car=s.abort_carrier
        v=t.velocity(force(mode))
        checks(v in (0,Q(11,10),Q(-11,10)),"Variable-speed ramp needs its own ODE segment")
        next_p=car.position+v*dt
        checks(0<=next_p<=car.length,"Split at the actual carriage stop")
        if vcam:
            a=s.keeper
            gap=(s.positions["cam"]-a*13*s.p["SEGMENT"])%s.limits["cam"]
            checks(vcam==-1 and gap>=dt and car.phase=="FULL" and s.rewind_sample[a]
                   and force(rewind)<-31 and "cam" not in s.jammed,"Unqualified cam displacement")
        # While the carriage is inside RETURN the cam electrical request
        # receives zero. Any previously charged winding remains an actual coil.
        mp=mode.advance(float(dt),trans.drive_for(am),float(v))
        cp=rewind.advance(float(dt),trans.drive_for(ac),float(vcam))
        if v:
            checks(t.velocity(force(mode))==v,"Winding crossed a nonsaturated boundary")
        if vcam:
            checks(force(rewind)<-31,"Cam winding lost its saturation regime")
        # On these chosen arcs each driven channel stays in its proved high
        # current range or the corresponding velocity is identically zero.
        dxw=sum(z["mechanical"] for z in (*mp,*cp))
        rail=sum(z["supplied"] for z in (*mp,*cp))
        checks(dxw>=-1e-8 and rail>=0,"Work sign changed")
        # A zero-other-draw electrical-port chart; source-wise cumulative
        # debit is applied below. No other consumer borrows these transfers.
        total_work+=number*dxw
        car.position=next_p
        s.positions["abort"]=next_p
        s.positions["cam"]=(s.positions["cam"]+vcam*dt)%s.limits["cam"]
        s.mechanical_input+=Q(str(number*dxw))
        s.mechanical_heat+=Q(str(number*dxw))
        t.flow_clock(dt)
        elapsed+=dt

    def sample():
        before=s.abort_carrier.phase
        e=t.strobe(force(mode))
        if before!=s.abort_carrier.phase:
            events.append([str(elapsed),e])
        return e

    if near_zero:
        # The old inward direction moves to zero under a real negative
        # current. Both directions are blocked there while that old level is
        # held. The actual old winding reverses BEFORE the next direction pulse.
        interval(Q(1,11),-20,0)
        checks(s.abort_carrier.position==0 and s.abort_carrier.phase=="RETURN","Premature seat")
        interval(t.remaining,20,0)
        checks(force(mode)>31 and sample()=="observed/held","Wrong geometry seated")
        while s.abort_carrier.position<s.abort_carrier.length:
            dt=min(t.remaining,(s.abort_carrier.length-s.abort_carrier.position)/Q(11,10))
            interval(dt,20,0)
            if t.remaining==0:sample()
        if s.abort_carrier.phase=="RETURN":
            interval(t.remaining,20,0)
            sample()
        checks(s.abort_carrier.phase=="FULL" and t.seated==0 and t.rebounded==1,"Near-seat rebound failed")
    else:
        # Arbitrary small distance below M, cam one unit away, genuine old cam
        # current. No geometry coordinate is rewritten between the following legs.
        interval(Q(1,1000),20,0)
        checks(sample()=="full-stop","Outward actual work did not reacquire M")
        interval(Q(1),20,-20,Q(-1))
        checks(sample()=="observed/held" and s.positions["cam"]==0,"Rewind did not park the actual cam")
        # MODE changes sign at stationary M. The old positive winding is not
        # erased. The actual next strobe occurs only after the field reversal.
        interval(Q(1),-20,0)
        checks(sample()=="return-release" and force(mode)<-31,"Unfunded or unsigned return initiation")
        while s.abort_carrier.position:
            dt=min(t.remaining,s.abort_carrier.position/Q(11,10))
            interval(dt,-20,0)
            if t.remaining==0:sample()
        if s.abort_carrier.phase=="RETURN":
            interval(t.remaining,-20,0)
            sample()
        checks(s.abort_carrier.phase=="NORMAL" and t.seated==t.rebounded==t.released==1,
               "Isolated displaced-cam cycle failed")
    channels=(mode.positive,mode.negative,rewind.positive,rewind.negative)
    per_rail=sum(z.supplied for z in channels)
    per_heat=sum(z.heat for z in channels)
    per_initial=sum(z.initial for z in channels)
    per_final=sum(z.x*z.x for z in channels)
    # Rail supply is nonnegative on every prefix. With zero external
    # inflow and ample stock, integrating its debit at the endpoints is exact
    # for this port, up to transducer_model's numerical integration tolerance.
    for feed in feeds:
        charge=Q(str(per_rail))
        checks(feed.stock>charge+1,"Borrowed an unprovided drive stock")
        feed.stock-=charge
    residual=number*(per_rail+per_initial-per_final-per_heat)-total_work
    checks(abs(residual)<0.02 and s.source_work.spent==t.work==2048*t.samples,"Missing a winding or sampler debit")
    return dict(full_motion_sequence=events,elapsed_q=str(elapsed),sampler_strobes=t.samples,
                actual_fixture_U=str(t.work),distinct_donor_banks=len({id(b) for b in feeds}),
                total_electrical_supply=round(number*per_rail,5),total_winding_heat=round(number*per_heat,5),
                total_mechanical_work=round(total_work,5),energy_balance_residual=round(residual,7),
                populated_exterior_chart="Held commands/rails and pre-existing physical winding currents; no closed donor mission embedding.")


def pricing(c,b):
    old_gate=record("threshold_gate_source_results.json")["costs"]
    inv=json.loads(legacy.text_at(PIN,"local-control/port_resource_results.json"))
    trans=inv["transit"]
    Emax=Q(trans["actual_Emax"]); Eoff=Q(trans["actual_Eoff"]); Eon=Q(trans["actual_Eon"])
    B_inventory=record("legacy_realization_results.json")["inventory"]
    Tcap=Q(B_inventory["retained_downrated_bank_allowance"])/2
    checks(Tcap <= Q(inv["point"]["per_bank_transit_capacity"]),"B transit exceeds the inherited bound")
    rho=Q(trans["residual_input_power"])
    checks(Emax+Tcap<4*Eoff and Eoff+Tcap<Eon and 10*rho<Eoff/4,"Half-off or no-rearm proof lost")
    # Reserve sixteen fixed descriptors, including their independently
    # rated held-fault/update paths. Four new iso/shunt-seated taps, switching
    # and pressure/endpoint wires all remain at this one fixture.
    bits=16*1024
    rate=2*bits*gates.RATE+Q(bits,1024)
    burst=2*bits
    extra_reaction=Q(16)*incumbent.field.U_BIT/1000
    reaction=Q(old_gate["combined_joint_reaction"])+extra_reaction
    reserve=Q(old_gate["minimum_U_after_additions"])-burst-2*rate
    rate_margin=Q(old_gate["offered_supply"])-Q(old_gate["combined_upstream_rate"])-rate
    peak=Q(old_gate["existing_input_combined_peak"])+Q(old_gate["additional_native_service_envelope"])+rate
    checks(366+128<=gates.PREDICATE_WORK and reaction<design.EXTRA_REACTION and reserve>2048 and rate_margin>0
           and 41*peak<2**93 and 4*41*peak<2**94,"Gate and pilot envelope fails")
    checks(old_gate["end_descriptor_exclusive"]+bits<=184315392,
           "New direction descriptors overlap the matched publisher")
    # The base gate predates these receiver clocks and the optional publisher.
    # Count each distinct incremental debit once on the shared host supply.
    nc=record("native_clock_source_results.json")["rates"]
    mp=record("matched_publication_results.json")["common_envelope"]
    rx=record("rx_product_results.json")["joined_charge"]
    rate_extra=Q(nc["additional_RX_U_rate"])+Q(mp["common_added_storage_rate"])+Q(rx["per_host_divider_rate"])
    burst_extra=Q(nc["additional_RX_U_burst"])+Q(mp["added_burst"])+Q(rx["per_host_divider_burst"])
    reserve-=burst_extra+2*rate_extra
    rate_margin-=rate_extra
    peak+=rate_extra+2*parent.NATIVE_RATE+rx["per_host_lanes"]*raw.RX_POWER
    checks(reserve==Q(rx["minimum_joined_U"])-burst-2*rate-Q(mp["added_burst"])-2*Q(mp["common_added_storage_rate"]),
           "Mismatched accounting for the seat, independently paced receivers and publisher")
    checks(reserve>2048 and rate_margin>0 and 4*41*peak<2**94,"Changed clock and publisher are not jointly funded")
    f=Q(b["padded_frame_upper"],2**26)+Q(c.constants["VECTOR_UPDATES"],64)
    J=11*f
    original=record("publication_timing_results.json")["functional"]
    compare=Q(b["instruction_upper_bounds"]["helper"]+64,2**26)+Q(1,64)
    horizon=Q(original["full_horizon"])-Q(original["helper_compare_to_emit"])+compare
    load=Q(3,2)*(1-Q(c.constants["LOAD_MARGIN"],1000)+Q(1,100))+horizon/10000
    gap=Q(1,5)-Q(c.constants["ISOLATION_MARGIN"],1000)+Q(1,100)+Q(1,10)+Q(11,400000)*horizon
    checks(load<1 and gap<Q(1,5),"Conditional factual pressure bounds fail")
    R=Q(2748532811,524288)
    # Includes phase27 qualification, action/signature waits and ordinary
    # settling; donating a correct source observation is still an obligation.
    wash=517+2*J+f+15+1
    return dict(actual_B_transit_capacity=str(Tcap),physical_receiver_feeder_included=False,descriptor_interval=[old_gate["end_descriptor_exclusive"],old_gate["end_descriptor_exclusive"]+bits],
                added_rate=str(rate),added_burst=burst,remaining_U=str(reserve),rate_margin=str(rate_margin),
                previous_extra_rate=str(rate_extra),previous_extra_burst=str(burst_extra),combined_peak=str(peak),
                stated_extra_pilot_reaction=str(extra_reaction),complete_reaction=str(reaction),
                shaft_housing_effort_min_rating=str(176+Q(11,10)+design.EXTRA_REACTION),
                full_stroke_min=str(Q(100000,11)),wrong_pose_to_full_conditional=str(wash+R+10000+Q(101,100)),
                nominal_stage_Fmax=str(f),J=str(J),factual_horizon=str(horizon),load_upper=str(load),
                clearance_deficit_upper=str(gap),Eoff_plus_Tcap_over_Eon=str((Eoff+Tcap)/Eon),
                max_Z_over_Eoff=str((Emax+Tcap)/Eoff),clock_price=gates.PREDICATE_WORK)


def produce():
    isa=program.load_isa()
    c,b=candidate(isa)
    print("checking compiled return helper",flush=True)
    outputs=native_helpers(isa,c,b)
    bound={}
    for name in ("abort_protocol_alternative.py","threshold_gate_source.py","gate_source_completion.py",
                 "threshold_gate_source_results.json","threshold_program_model.py","threshold_program_source.py",
                 "parent_retirement.py","parent_realization.py","shared_bank_charging.py","threshold_field_source.py",
                 "native_clock_source_results.json","rx_product_results.json","legacy_realization_results.json",
                 "matched_publication_results.json","publication_timing_results.json"):
        text=(HERE/name).read_text(encoding="utf-8-sig")
        checks(text==legacy.text_at(PIN,"portability/"+name),"Immutable source binding changed: "+name)
        bound[name]=program.hash_text(text)
    bound["local-control/transducer_model.py"]=program.hash_text(legacy.text_at(PIN,"local-control/transducer_model.py"))
    print("checking paid terminal and winding arcs",flush=True)
    return dict(base=PIN,immutable_sources_sha256_lf=bound,candidate_image=program.hash_text(json.dumps(c.image)),occupied_C=len(c.nodes),
                registers=c.next_register,helper_upper=b["instruction_upper_bounds"]["helper"],
                active_frame_upper=b["active_frame_upper"],padded_frame_upper=b["padded_frame_upper"],
                compiled_outputs=outputs,boundary=challenge(isa,c),high_E_wait=energy_wait(isa,c),near_zero=mechanical_trace(isa,c,near_zero=True),
                complete_example=mechanical_trace(isa,c),resources=pricing(c,b),full_source_admitted=False)


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--write",action="store_true")
    args=parser.parse_args()
    out=json.dumps(produce(),indent=2,sort_keys=True)+"\n"
    path=HERE/"return_seat_results.json"
    if args.write:
        path.write_text(out,encoding="utf8",newline="\n")
    else:
        checks(path.read_text(encoding="utf8")==out,"RETURN seat record differs")
    print("fresh funded terminal and directional RETURN reproduced")


if __name__=="__main__":
    main()

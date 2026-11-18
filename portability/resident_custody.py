"""Physical incoming threshold fields on the ordinary processor's own C leaves."""
import argparse
import hashlib
import importlib.util
import json
from dataclasses import dataclass
from fractions import Fraction as Q
from pathlib import Path
import subprocess
import sys

import cam_reformation as cam
import input_lifecycle as inputs
import parent_realization as machine
import parent_retirement as retirement
import shared_bank_charging as charging
import threshold_design as design
import threshold_field_source as field
import threshold_gate_source as gates
import threshold_incidence_model as incidence
import threshold_program_model as program

HERE = Path(__file__).resolve().parent
BASE = "097cf8fe26c4f4d2c78bde58473a88051f12e945"
DELTA = inputs.LocalSourceBank.DELTA


def need(condition, why):
    if not condition:
        raise ValueError(why)


def label(region, host):
    return f"region{region}/host{host}"


@dataclass(frozen=True)
class FixedInput:
    source: object
    destination: field.Destination

    @property
    def pulse(self):
        return self.source.rows[self.destination].pulse


class Region:
    """Sparse installation of one finite region. Identity checks precede flow."""
    def __init__(self, index, population):
        incidence.check_population(population)
        need(type(index) is int and index >= 0, "Uninstalled region")
        self.index, self.population = index, population
        self.hosts = {}
        self.leaves = {}
        self.uses = {}

    def install(self, fixture):
        host = fixture.owner
        need(isinstance(fixture, gates.SharedContacts) and host not in self.hosts,
             "Fixture has no unique regional identity")
        targets = tuple(label(self.index, t) for t in incidence.neighbors(self.population, host))
        for bank, cpu in enumerate(fixture.machines):
            need(isinstance(cpu, charging.FramedParent) and cpu.bank.owner == (host, bank)
                 and tuple(cpu.setter.targets) == targets,
                 "Wrong CPU, bank owner, or physical target map")
        need(all(fixture is not previous and fixture.source_work is not previous.source_work
                 and all(a._body is not b._body and a.bank is not b.bank and a.setter is not b.setter
                         for a in fixture.machines for b in previous.machines)
                 for previous in self.hosts.values()), "Different hosts share a physical owner")
        need(fixture.machines[0]._body is not fixture.machines[1]._body, "Bank bodies alias")
        self.hosts[host] = fixture

    def leaf(self, host, side, address, bit):
        need(host in self.hosts and type(side) is int and side in (0, 1)
             and type(bit) is int and 0 <= bit < 192
             and type(address) is int and 0 <= address < 8192, "No installed resident bit")
        key = (host, side, address, bit)
        if key not in self.leaves:
            self.leaves[key] = ResidentBit(self, *key)
        return self.leaves[key]


class ResidentBit:
    def __init__(self, region, host, side, address, bit):
        self.region = region
        self.host, self.side, self.address, self.bit = host, side, address, bit
        self.fixture = region.hosts[host]
        self.cpu = self.fixture.machines[side]
        # Installation of an existing physical leaf, not a CPU read transaction.
        self.coordinates = machine.Body.coordinates(self.cpu._body, address)
        self.destination = field.Destination(label(region.index, host), side, 192 * address + bit)
        self.inputs = {}

    def accept_input(self, source):
        origin = source.fixture.owner
        key = (origin, source.side)
        need(self.region.hosts.get(origin) is source.fixture
             and source.fixture.installed_source_ports.get(source.side) is source
             and source.machine is source.fixture.machines[source.side]
             and origin in incidence.neighbors(self.region.population, self.host)
             and self.destination in source.rows and key not in self.inputs,
             "No such fixed source bank and destination or repeated contribution")
        port = FixedInput(source, self.destination)
        need(id(port.pulse) not in self.region.uses,
             "One receiving motor was attached twice")
        self.region.uses[id(port.pulse)] = (key, self.destination)
        self.inputs[key] = port

    @property
    def x(self):
        return self.coordinates[self.bit]

    def native(self):
        n = self.cpu.native
        if n is None or n.binding is None or n.drive_bit != self.bit:
            return None
        b = n.binding
        if b.address != self.address:
            return None
        need(isinstance(n, retirement.GuardedNative) and n.machine is self.cpu and
             n.parent is self.cpu.cell and self.cpu.pending is not None and
             n.token is self.cpu.fabric.token and b.body is self.cpu._body and b.coordinates is self.coordinates,
             "Native operation addresses a different owner or physical word")
        return n

    def coupled(self, duration, *, disturbance=Q(0)):
        """A steady source-force chart strictly between material, controller and pulse events."""
        dt, disturbance = Q(duration), Q(disturbance)
        need(dt > 0 and abs(disturbance) <= field.U_BIT/4, "Unrated disturbance or nonpositive interval")
        pos = self.fixture.positions[f"clamp{self.side}"]
        held = bool(self.fixture.output[f"field-clutch:{self.side}"]) if self.fixture.held_plane else None
        open_ = pos < cam.CUTOFF if held is None else held
        pulses = [port.pulse for port in self.inputs.values()]
        active = []
        for p in pulses:
            slot = next((i for i,s in enumerate(p.slots) if s is not None), None)
            # A settled zero motor, including a formed idle row, has zero output
            # and no drive work. Other installed costs remain on their own ports.
            if p.force==0 and (p.reset_motor_owner or p.selected()==0):
                continue
            need(slot is not None and not p.reset_motor_owner and p.force == field.U_BIT*p.selected()
                 and p.energy[slot].stock >= 1 + 8*dt, "Split at a pulse, effort or stock event")
            active.append(p)
        n = self.native()
        enabled = (n is not None and not n.retired and n.token.live and
                   not self.cpu.native_inhibit and n.parent.stock > 1)
        powered = min(dt, (n.parent.stock-1)/retirement.NATIVE_POWER) if enabled else Q(0)
        native_sign = (2*n.operand_bits[self.bit]-1) if powered else 0
        native_work = native_heat = native_output = donor_output = disturbance_output = Q(0)
        for length, engaged in ((powered, True), (dt-powered, False)):
            if not length:
                continue
            old = self.x
            force = native_sign * field.NATIVE_FORCE if engaged else Q(0)
            if disturbance:
                external = sum((p.force for p in pulses), disturbance)
                end = field.bit_flow(old, external, force, length, open_contact=open_, native_engaged=engaged)
                works = [p.force*(end-old) if open_ else Q(0) for p in pulses]
            else:
                end, works = gates.field_clutch(old, [p.force for p in pulses], force, length, pos,
                                               native_engaged=engaged, failed_contact=held)
            disturbance_output += disturbance*(end-old) if open_ else Q(0)
            drive = retirement.NATIVE_POWER*length if engaged else Q(0)
            mechanical = force*(end-old)
            need(drive >= mechanical, "Unfunded resident mechanical work")
            if engaged:
                need(n.parent.debit(drive), "Unfunded native drive")
                n.drive_work += drive
            self.coordinates[self.bit] = end
            self.cpu._body.sync_word(self.address)
            velocity = (end-old)/length if open_ else Q(0)
            for p, work in zip(pulses, works):
                before = p.motor_input, p.motor_output, p.motor_heat
                charge = 8*length if p.force else Q(0)
                p.flow(length, relative_velocity=velocity)
                need((p.motor_input-before[0],p.motor_output-before[1],p.motor_heat-before[2])
                     == (charge,work,charge-work), "Donor work detached from the resident displacement")
            native_work += drive
            native_output += mechanical
            native_heat += drive - mechanical
            donor_output += sum(works,Q(0))
        return dict(x=self.x,native_work=native_work,native_output=native_output,native_heat=native_heat,
                    donor_work=8*dt*len(active),donor_output=donor_output,
                    disturbance_work=disturbance_output,fast_duration=powered)

    def withdraw_at_closed_clutch(self, duration):
        """A previously expired receiver's signed force decays behind the real closed clutch."""
        n = self.native()
        need(not self.fixture.held_plane and self.fixture.positions[f"clamp{self.side}"] >= cam.CUTOFF
             and (n is None or self.cpu.native_inhibit or n.retired or not n.token.live),
             "Withdrawal chart needs the closed ordinary clutch and no native drive")
        t = Q(duration)
        need(t > 0, "Withdrawal needs positive time")
        before = self.x
        work = Q(0)
        for port in self.inputs.values():
            p = port.pulse
            need(p.withdrawal_owner is not None and all(s is None for s in p.slots)
                 and not p.reset_motor_owner, "Unexpired or differently owned motor")
        for port in self.inputs.values():
            p = port.pulse
            prior = p.motor_input,p.motor_output,p.motor_heat
            p.flow(t, relative_velocity=0)
            work += p.motor_input-prior[0]
            need(p.motor_output==prior[1] and p.motor_heat-prior[2]==p.motor_input-prior[0],
                 "Closed leaf received work from its withdrawn branch")
        need(before == self.x, "Closed leaf moved without a native driver")
        return work


def assembly(i,c,region,host):
    capacity=int(Q(gates.record("parent_realization_results.json")["cost_bounds"]["actual_bank_capacity"]))
    targets=tuple(label(region.index,t) for t in incidence.neighbors(region.population,host))
    cpus=[]
    for side in (0,1):
        e=charging.OperatingBank((host,side),capacity,Q(capacity))
        cpu=charging.FramedParent(i,c,bank=e,targets=targets)
        charging.JointCharge(e,cpu,(),DELTA)  # idle native inputs exert zero draw on this chart
        cpus.append(cpu)
    U=Q(gates.record("threshold_gate_source_results.json")["costs"]["upstream_capacity"])
    # The external U value is an already funded local point below the final capacity.
    u=inputs.SourceWork(host,U,2**30)
    fx=gates.SharedContacts(gates.parameters(c),host,u,tuple(cpus))
    region.install(fx)
    return fx


def connect_source(i,c,region,host,side,leaf):
    s=assembly(i,c,region,host)
    cpu=s.machines[side]
    pulse=field.PulseSelector()
    # Outgoing reformation retains its legacy diagnostic word unchanged. It
    # never supplies the incoming receiving leaf or modifies that leaf.
    frame=cam.ResidentWord(label(region.index,host),side,0,[Q(-1)]*192,("source-frame",))
    episode=cam.CamBank(pulse,cpu.setter,frame)
    cam.finish(episode,cam.VMAX)
    handoff=episode.activation_to(cam.DRIVER,cam.DRIVER/cam.VMAX)
    s.positions[f"act{side}:0"]=cam.DRIVER
    gate=gates.LiveSourceBank(s,side,episode,leaf.destination,cam.ControlLine(words=[10]*8,valid=[True]*8))
    need(handoff.pulse is pulse and gate.machine is cpu, "Receiving channel was cloned")
    leaf.accept_input(gate)
    return gate


def ready(cpu):
    cpu.charging.flow_full_delivery(2*DELTA,source_powered=True)
    need(cpu.recharge(), "Parent has no actual timed charge")


def rejects(call):
    try:
        call()
    except ValueError:
        return True
    raise AssertionError("Invalid participant accepted")


def run():
    i=program.load_isa()
    c=program.compile_program(i,design.design(i))
    ports=program.ports_class(i)(c)
    population=gates.record("regional_coupling_results.json")["world"]["m"]
    r=Region(3,population)
    target=40
    f=assembly(i,c,r,target)
    cpu=f.machines[1]
    addr=100
    image_bit=1
    mask=1<<image_bit
    need(c.image[addr]&mask,"Probe requires a positive rail in the actual donor image")
    leaf=r.leaf(target,1,addr,image_bit)
    need(leaf is r.leaf(target,1,addr,image_bit),"Duplicated physical bit")
    wrong=r.leaf(target,0,addr,image_bit)
    other=r.leaf(target,1,addr+1,image_bit)
    other_x,wrong_x=other.x,wrong.x
    providers=incidence.neighbors(population,target)[:34]
    for j,h in enumerate(providers):
        source=connect_source(i,c,r,h,j%2,leaf)
        need(rejects(lambda: wrong.accept_input(source)), "Wrong bank accepted")
        rejects(lambda: leaf.accept_input(source))
        p=source.rows[leaf.destination].pulse
        # A retained genuine positive source setting used by the sampler.
        source.setter.held[leaf.destination]=1
        need(source.capture(leaf.destination,0,Q(0))=="latched"
             and source.deliver(leaf.destination,0,Q(1,4))=="active","Actual fixed trigger failed")
        # Isolated closed-clutch setup, with 500 actual paid edges and a
        # funded constant-clock ramp. Opening/power chronology is separate.
        for _ in range(500):
            p.flow(Q(1000,1001),relative_velocity=0)
            need(p.clock_edge(0)=="active","Pulse exhausted during setup")
        need(p.force==field.U_BIT,"Paid receiver motor not settled")
    idle=connect_source(i,c,r,incidence.neighbors(population,target)[34],0,leaf)
    neutral=idle.rows[leaf.destination].pulse
    need(neutral.force==0 and neutral.selected()==0 and len(leaf.inputs)==35,"Active/idle input multiplicity")
    def put_x(x):
        leaf.coordinates[leaf.bit]=x
        cpu._body.sync_word(addr)
    # Independent proof cut near one threshold crossing. Charge the fixed
    # physical motion once. The lower full-rail dwell remains a theorem.
    f.positions["clamp1"]=cam.CUTOFF-1
    put_x(-field.U_BIT)
    need(cpu.C[addr]==c.image[addr]^mask,"Wrong initial physical bit was hidden by the word cache")
    open_result=leaf.coupled(Q(1,10))
    need(leaf.x==Q(11,10)*field.U_BIT and cpu.C[addr]==c.image[addr],"Signed C transition missing")
    disturbed=leaf.coupled(Q(1,10),disturbance=-field.U_BIT/4)
    need(disturbed["x"]-open_result["x"] == Q(83,40)*field.U_BIT
         and disturbed["disturbance_work"]<0,"Opposing bounded external work vanished")
    f.positions["clamp1"]=cam.CUTOFF
    immobile=leaf.coupled(Q(1,10),disturbance=field.U_BIT/4)
    need(immobile["x"]==disturbed["x"] and immobile["donor_output"]==immobile["disturbance_work"]==0 and neutral.motor_input==0,
         "Closing the incoming clutch moved the stored bit or supplied work")
    # Use source operations at a separately funded/powered retired-parent
    # boundary. Instruction fetch and LOADC both observe the transferred leaf.
    reads=[j for j,v in enumerate(c.image) if i.decode(v)[0]==i.LOADC]
    need(len(reads)==1 and reads[0]>=c.labels["refresh_fields"],"Unexpected scanner instruction")
    pc=reads[0]
    _,dst,src,_,_=i.decode(c.image[pc])
    cpu.pc=pc
    cpu.R[src]=addr
    ready(cpu)
    need(cpu.launch() and cpu.pending.cell==c.image[pc] and cpu.complete(ports)
         and cpu.R[dst]==cpu.C[addr]==c.image[addr],"Production scanner LOADC did not see the formed word")
    cpu.pc=addr
    ready(cpu)
    need(cpu.launch() and cpu.pending.cell==cpu.R[dst],"Actual fetched word differed from the physical read")
    fixed_fetch=cpu.pending.cell
    before=cpu.C[addr]
    # Direct C intervention after capture changes that same leaf, not the
    # already latched instruction or another bank/address.
    cpu.C[addr]=before^mask
    need(cpu.pending.cell==fixed_fetch and leaf.x==-1 and other.x==other_x and wrong.x==wrong_x,
         "A captured parent was rebound or the bit escaped its target")
    # The following observation ends this local branch.
    # The cut at the issued fetch deliberately retains its outstanding parent.
    # The independent native example exercises the other bank.
    return dict(open_sign_crossing=open_result,opposing_disturbance=disturbed,
                closed_clutch=immobile,active_donors=len(providers),idle_rows=1,
                region=r.index,target=target,bank=1,address=addr,bit=image_bit,
                production_LOADC_PC=pc,compiled_word=c.image[addr],
                instruction_fetch=fixed_fetch,LOADC_result=cpu.R[dst],captured_word_retained=True,
                wrong_bank_and_address_framed=True), (i,c,ports,r,f,leaf)


def native_case(i,c,ports,r,f,leaf):
    # Independent source cut on another fixed coordinate of the same target.
    # Bank 0 has its own CPU, C, parent and operating stock.
    cpu=f.machines[0]
    addr=80
    bit=r.leaf(f.owner,0,addr,0)
    h=incidence.neighbors(r.population,f.owner)[-1]
    source=connect_source(i,c,r,h,1,bit)
    p=source.rows[bit.destination].pulse
    source.setter.held[bit.destination]=-1
    need(source.capture(bit.destination,0,0)=="latched" and source.deliver(bit.destination,0,0)=="active",
         "Native-case receiving pulse missing")
    # Start this representative after its funded slew at a closed clutch.
    for _ in range(500):
        p.flow(Q(1000,1001),relative_velocity=0)
        need(p.clock_edge(0)=="active","Nominal active slot lost")
    need(p.force==-field.U_BIT,"Opposing field missing")
    cpu.C[0]=i.encode(i.STOREC,3,4)
    cpu.C[addr]=0
    cpu.R[3],cpu.R[4]=1,addr
    ready(cpu)
    need(cpu.launch() and cpu.complete(ports,native_ticks=705)=="waiting","Missing physical native selection")
    n=cpu.native
    need(n.binding.coordinates is bit.coordinates and n.drive_bit==0 and cpu.pending is not None,
         "Retained native selection differs from the fixed receiver")
    n.target_address=addr+1
    f.positions["clamp0"]=cam.CUTOFF-1
    dt=Q(1,4*2**30)
    prior=bit.x
    a=bit.coupled(dt)
    need(bit.x==0 and cpu.C[addr]&1 and a["native_work"]==retirement.NATIVE_POWER*dt
         and a["donor_output"]==-field.U_BIT*(bit.x-prior) and a["native_work"]==a["native_output"]+a["native_heat"],
         "Conjugate work, tie convention, or native target changed")
    # A cut inhibits new CPU/native use, while already delivered force belongs
    # to the receiver and persists. One subthreshold donor cannot move it.
    retained=n.binding;before_stock=n.parent.stock
    cpu.inhibit()
    b=bit.coupled(dt)
    need(b["x"]==a["x"] and b["native_work"]==0 and n.parent.stock==before_stock
         and n.binding is retained and p.force==-field.U_BIT, "Cut erased the wrong effect")
    # Conditional sustained-cut chart. No new driver or competing job. The
    # count-to-one fold is the exact composition of ordinary 15-work edges
    # (positive counts >1), with constant fully funded 8-work motor holding.
    f.positions["clamp0"]=cam.CUTOFF
    source.fixture.positions["cut1"]=source.fixture.p["CUT_LIMIT"]
    source.disconnect()
    need(source.capture(bit.destination,1,1)=="cut" and not p.native_inhibit,
         "Disabling the source erased or reissued the receiver's own job")
    count=p.slots[0][1]-1
    dwell=count*Q(1000,1001)
    hold=8*dwell
    need(p.energy[0].stock>=1+15*count+hold+47 and p.force==-field.U_BIT,
         "Full paid counter suffix cannot use this constant regime")
    before=p.motor_input
    p.flow(dwell,relative_velocity=0)
    need(p.motor_input-before==hold and p.energy[0].debit(15*count), "Missed holding or countdown work")
    p.slots[0][1]-=count
    previous=p.motor_input
    p.flow(Q(1000,1001),relative_velocity=0)
    final_hold=p.motor_input-previous
    need(final_hold==Q(8000,1001),"Missing time and motor work before last expiry")
    stock=p.energy[0].stock
    need(p.clock_edge(0)=="expired" and p.energy[0].stock==stock-47 and p.withdrawal_owner==0,
         "Last clock edge did not transfer withdrawal ownership")
    f.positions["clamp0"]=cam.CUTOFF
    # Native still owns a *disconnected* captured drive. Withdrawal itself
    # makes no motion at the closed clutch. Keep its retained identity.
    need(n.drive_bit==0 and cpu.native_inhibit, "The stopped controller lost its held physical drive selector")
    withdrawn=bit.withdraw_at_closed_clutch(1000)
    need(p.force==0 and p.withdrawal_owner is None and withdrawn==8*field.U_BIT/(field.FORCE/1000)
         and n.binding is retained and bit.x==0,"Receiver withdrawal or native custody changed")
    return dict(overlap=a,after_native_cut=b,withdrawal=withdrawn,remaining_ordinary_edges=count,
                held_work=hold,final_interval_holding=final_hold,countdown_work=15*count,last_edge=47,source_capture_after_cut="cut",
                retained_drive_selector=n.drive_bit,binding_retained_after_cut=True)


def detached(c,i):
    e=charging.OperatingBank((2,1),1000000,1000000)
    cpu=retirement.RetirableParent(i,c,bank=e)
    cm=retirement.JoinedCam(cpu)
    actual=machine.Body.coordinates(cpu._body,0)
    old=machine.Body.observe_word(cpu._body,0)
    x0=actual[0]
    disp,_=gates.field_clutch(x0,[-x0*field.FORCE]*34,0,2/(34*field.FORCE-field.THETA),0,
                              native_engaged=False)
    cm.resident.coordinates[0]=disp
    need(cm.resident.bank!=e.owner[1] and cm.resident.coordinates is not actual and actual[0]==x0
         and disp==-x0 and machine.Body.observe_word(cpu._body,0)==old,"Detached resident discriminator vanished")
    return dict(actual_owner=e.owner,diagnostic_bank=cm.resident.bank,diagnostic_bit=disp,
                processor_bit=actual[0],unchanged_fetched_word=old)


def primary():
    directory=HERE.parent/"local-control"
    spec=importlib.util.spec_from_file_location("_custody_primary",directory/"program_model.py")
    isa=importlib.util.module_from_spec(spec);sys.modules[spec.name]=isa;spec.loader.exec_module(isa)
    geometry=json.loads((directory/"geometry_results.json").read_text())
    data=geometry["design"]
    data["physical_parameters"]=tuple(map(tuple,data["physical_parameters"]))
    c=isa.compile_check(isa.Design(**data))
    k=c.constants;key=k["BAYS"]*k["IMAGE_CELLS"]+17;encoded=(key<<k["SYMBOL_BITS"])+c.image[17]
    out={}
    for n in (6,7,13):
        m,p=isa.Machine(c),isa.RawPorts(c)
        b=k["TARGET_BASE"]
        for cell,value in (("PENDING",1),("CELL_WAIT",0),("CELL_KEY",key)):
            m.W[b+k[cell]]=value
        for j in range(n):
            p.replies[j,j%2,0]=encoded
        m.enter("cell_result",(0,1,0,17))
        need(m.run(p,budget=100000,until_yield=False)=="halt" and m.result()==(2 if n>=7 else 1),
             "Changed mature A-prime observation")
        out[n]=m.result()
    digest=hashlib.sha256(b"".join(x.to_bytes(24,"little") for x in c.image)).hexdigest()
    need(digest==geometry["compiler"]["encoded_image_sha256"],"Wrong primary controller")
    return dict(image=digest,exact_matching_origins_to_literal_return=out,
                minimum_wait=Q(94900,101),wait_margin=Q(94900,101)-874-6-Q(1,64)-Q(1,2**26))


def signed_dwell():
    # Piecewise-constant examples in the rail proof's scalar normal form.
    def inspect(xs):
        total=sum(xs,Q(0))
        suffix=Q(0)
        lowest=Q(0)
        for step in reversed(xs):
            suffix+=step
            lowest=min(lowest,suffix)
        x=Q(-1)
        for step in xs:
            x=max(-1,min(1,x+step))
        return total,lowest,x
    # A negative interval can follow an earlier arrival at the rail if enough
    # subsequent positive progress is made. A trailing loss cannot be hidden.
    admitted=inspect([Q(3),Q(-1,4),Q(1,4)])
    late_loss=inspect([Q(3),Q(-1,4)])
    need(admitted==(3,0,1) and late_loss==(Q(11,4),Q(-1,4),Q(3,4)),
         "Total directed dwell alone was incorrectly sufficient at cutoff")
    velocity=Q(829,100)*field.U_BIT
    full_rail=2/velocity
    geometry=gates.record("threshold_geometry_results.json")["arithmetic"]["geometry"]
    spare=Q(geometry["cutoff_slack"])
    # One contiguous no-write interval, followed by positive progress. Its
    # late face still has to satisfy every terminal suffix inequality.
    worst_reverse=field.Z_MAX-field.THETA
    debt_cap=spare*velocity/(velocity+worst_reverse)
    need(full_rail==Q(314572800000,829) and worst_reverse>0 and 0<debt_cap<spare,
         "The rebased time-loss allowance is not positive")
    return dict(positive_velocity=velocity,reverse_velocity_upper=worst_reverse,
                full_rail_work_time=full_rail,old_startup_plus_write_slack=spare,
                charged_bad_time_for_total_dwell_only=debt_cap,
                suffix_preserved=admitted,terminal_suffix_fails=late_loss)


def generate():
    evidence,context=run()
    i,c,ports,r,f,leaf=context
    paths=("parent_realization.py","parent_retirement.py","shared_bank_charging.py","input_lifecycle.py",
           "threshold_gate_source.py","threshold_field_source.py","threshold_program_model.py",
           "threshold_program_source.py","threshold_design.py","regional_coupling_results.json",
           "threshold_gate_source_results.json","threshold_geometry_results.json","cam_reformation.py",
           "threshold_incidence_model.py","../local-control/program_source.py","../local-control/program_model.py",
           "../local-control/geometry_results.json")
    immutable={}
    for name in paths:
        file=(HERE/name).resolve()
        rel=file.relative_to(HERE.parents[2]).as_posix()
        old=subprocess.check_output(["git","show",f"{BASE}:{rel}"],cwd=HERE).replace(b"\r\n",b"\n")
        current=file.read_bytes().replace(b"\r\n",b"\n")
        need(old==current,"Changed source evidence "+name)
        immutable[name]=hashlib.sha256(old).hexdigest()
    return gates.normalize(dict(base=BASE,active_coordinates=evidence,native=native_case(i,c,ports,r,f,leaf),
                                detached=detached(c,i),primary=primary(),signed_dwell=signed_dwell(),source_arity=40,
                                full_orbit_proved=False,unbounded_service=False,
                                immutable_sources=immutable,own={n:program.digest(HERE/n)
                                for n in ("resident_custody.py","RESIDENT-CUSTODY.md")}))


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    g=parser.add_mutually_exclusive_group(required=True)
    for key in ("--write","--check"):
        g.add_argument(key,action="store_true")
    args=parser.parse_args()
    text=json.dumps(generate(),indent=2,sort_keys=True)+"\n"
    output=HERE/"resident_custody_results.json"
    if args.write:
        output.write_text(text,encoding="utf-8",newline="\n")
    else:
        need(output.read_text(encoding="utf-8")==text,"Resident custody record differs")
    print("PASS fixed resident coordinate, paid conditional flow and actual instruction/data reads; full orbit remains open")

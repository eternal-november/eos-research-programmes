"""Constructive initial native state and split bootstrap for the threshold source.

This checks a finite initial relation and conditional timing suppliers, not
source admission, a full hybrid trace, or recurrent restoration after release.
"""
from fractions import Fraction as Q
import argparse
import json
import sys
import threshold_program_model as program
import threshold_design as design
import threshold_incidence_model as incidence
import legacy_realization as legacy
import cam_reformation as cam
import parent_realization as parent
import parent_retirement as retirement
import input_lifecycle as raw
import shared_bank_charging as charging

HERE=program.HERE
BASE='6a5f8aad0f0e5156edb21a054f8c72adcbf7120e'
FIELD='215ecb755312f580cbd8c283b419f0958518766f'
CAM_BASE='36d69bce7a4705fd54a915beb7c00cea55cce063'
INPUT_BASE='186b0b922011239ea2ee46b5918790259de578cc'
CHARGING_BASE='331698b578e3349de729857dd98378976e44ad88'
GATE_BASE='bb3c68feb4777b1f98ae9e1056176c4525d5be43'
PARENT_BASE='4672827a2717816ccc2d4ebbcee88a58c063c8b4'
ITINERARY_BASE='bdeb1d2fd16c3ffbcd6b58f9d8431b3616cf8f2b'
need=program.need
need(sys.version_info[:2]==(3,12) and not sys.flags.optimize,'Unoptimized Python3.12 required')


def frozen(name):
    return legacy.text_at(BASE,'portability/'+name)


def native_initial_points(field,population,dispatch_bits,isa,c,bank_capacity,source_capacity):
    need(type(dispatch_bits) is int and 0<dispatch_bits<=64,
         'Initial dispatch state exceeds its existing reset allocation')
    cam.fixture(controller_residue=(1<<dispatch_bits)-1)
    try:cam.fixture(controller_residue=1<<dispatch_bits)
    except ValueError:pass
    else:raise ValueError('Initial dispatch width omits actual cam bits')
    targets=tuple('region0/host'+str(x) for x in incidence.neighbors(population,0))
    capacity=Q(bank_capacity)
    need(capacity.denominator==1 and capacity>0,'Initial operating capacity is not a physical integer')
    owners={full:raw.SourceWork(0,source_capacity,source_capacity) for full in (False,True)}
    cases=[]
    for active in (False,True):
        for funded_reset in (False,True):
            pulse=field.PulseSelector(cut=not active,native_inhibit=not active,
                initial_reset_energy=(field.RESET_SOURCE_ENERGY,field.RESET_RECEIVER_ENERGY)
                                    if funded_reset else (Q(0),Q(0)))
            setter=field.SettingWriter(targets,cut=not active,native_inhibit=not active,
                reset_stock=field.SETTER_RESET_ENERGY if funded_reset else Q(0))
            operating=charging.OperatingBank((0,0 if active else 1),int(capacity),capacity if active else Q(0))
            cpu=charging.FramedParent(isa,c,bank=operating,targets=targets)
            source=local_source_at_initial_entry(owners[funded_reset],operating,active,funded_reset,population)
            joint=charging.JointCharge(operating,cpu,source.slots+[source.adc],source.DELTA)
            need(cpu.bank is source.energy is joint.bank and len(joint.slots)==10321,
                 'The actual source and parent must share the same input/operating owners')
            joint.balance()
            # This is the same physical setter, not an extra installed store.
            cpu.setter=setter
            if not active:
                cpu.C[:]=[(1<<192)-1]*len(cpu.C)
                cpu.inhibit()
            need(cpu.pending is None and cpu.native is None and cpu.fabric.token is None
                 and not cpu.fabric.links and cpu.cell.stock==0 and cpu.setter is setter,
                 'Initial CPU has hidden route/native/child authority or a duplicate setter')
            need(cpu.fabric.cut==cpu.fabric.return_cut==cpu.native_inhibit==(not active),
                 'Initial actual route cutset disagrees with the selected bank')
            if not active:
                pre=(operating.stock,cpu.cell.stock,source.reset_work.stock)
                joint.flow_full_delivery(1,source_powered=source.powered)
                need((operating.stock,cpu.cell.stock,source.reset_work.stock)==pre and
                     source.source_start('fast',(0,))=='cut' and source.branches[0].offer(0,42)=='cut',
                     'An initially cold ordinary source drew power or accepted new work')
                before=tuple(cpu.C)
                need(not cpu.recharge() and not cpu.launch() and tuple(cpu.C)==before,
                     'The cold initial CPU can rearm or rewrite without its physical entry')
            need(pulse.slots==[None]*3 and pulse.pending==[None]*3 and pulse.force==0,
                 'Initial native row has retained pulse debt')
            need(pulse.counter_bound_holds() and not pulse.reset_motor_owner,
                 'Initial native state is not the stated idle physical point')
            need(len({id(x) for x in pulse.energy})==3 and
                 len({id(x) for x in pulse.trigger_energy})==3,
                 'Initial energy cells alias')
            need(all(x.stock==field.PULSE_ENERGY for x in pulse.energy) and
                 all(x.stock==field.TRIGGER_ENERGY for x in pulse.trigger_energy),
                 'Initial charge was inferred from capacity')
            need(setter.phase=='ready' and setter.energy==field.SET_ENERGY and
                 not setter.parent_live and setter.parent_record is None and not setter.held,
                 'Initial setter has an unfunded or old parent')
            mode=10 if active else 0
            line=cam.ControlLine(words=[mode]*8,valid=[True]*8)
            line.phases=[Q(i+1,64) for i in range(8)]
            need(all(x is None for x in line.snapshots) and all(x==0 for x in line.remaining),
                 'Initial control has an old pending snapshot')
            initial_control=dict(committed_modes=list(line.words),valid=list(line.valid),
                pending_snapshots=[None]*8,dispatch_bits=[0]*dispatch_bits,
                receiver_armed=active,source_trigger_open=active,
                ownership='ordinary pulse supplier' if active else 'actual cut; no reset episode inferred')
            arrivals=[]
            line.flow(2*cam.CONTROL_DELAY,mode,lambda dt:None,arrivals.append)
            need(all(x==mode for x in line.words) and all(x==mode for x in arrivals),
                 'Conforming initial control mode changed before any new request')
            # Clock-state preservation only; actual control work is charged by
            # the joined cam U envelope, not by this no-op observer callback.
            if not active:
                need(setter.issue((0,0,0,1))=='cut' and pulse.capture(0,1)=='cut',
                     'Inactive initial row is not actually inhibited')
            cases.append(dict(source_bank_active=active,reset_stores_initially_full=funded_reset,
                actual_pulse_work=sum(x.stock for x in pulse.energy),
                actual_trigger_work=sum(x.stock for x in pulse.trigger_energy),
                actual_source_reset_work=pulse.reset_source_reserve.stock,
                actual_receiver_reset_work=pulse.reset_reserve.stock,
                actual_setter_work=setter.energy,actual_setter_reset_work=setter.reset_reserve.stock,
                actual_control_state=initial_control,control_offered_work_upper=line.offered_work_upper,
                actual_parent_state=dict(operating_stock=cpu.bank.stock,parent_stock=cpu.cell.stock,
                    root_cut=cpu.fabric.cut,return_cut=cpu.fabric.return_cut,native_inhibit=cpu.native_inhibit,
                    powered=cpu.powered,no_live_token=True,no_pending_child=True,
                    shared_ordinary_E_owner=operating.owner,source_energy_is_CPU_bank=True,
                    input_charger_cells=len(joint.slots),source_reset_stock=source.reset_work.stock,
                    source_native_mode=source.native_mode,source_admission=source.admission,
                    native_entry_request=source.engine.get(94),source_reset_spent=source.reset_work.spent,
                    shared_setter_object=True,cold_arbitrary_code_inhibited=not active),
                no_old_pulse_or_setter_or_cpu_parent=True,held_setting_default=0,force=0))
    a=field.PulseSelector();b=field.PulseSelector()
    need(all(x is not y for x in a.energy for y in b.energy),'Two installed channels share a stock')
    # The initial relation is not a reset method. Release does not turn a
    # corrupted counter/force/parent state into any of the above constructors.
    retained=field.PulseSelector(slots=[[1,field.PULSE_COUNTER_CAP],None,None],force=field.FORCE)
    before=(retained.slots[0][:],retained.force,retained.energy[0].stock)
    retained.cut=True
    need((retained.slots[0],retained.force,retained.energy[0].stock)==before and
         not retained.counter_bound_holds(),'Cut relabelled old native debt as initialized')
    return dict(representative_role_cases=cases,distinct_channel_stores=True,
        product_index='(region,source host,source bank,target ordinal,target bank,bit,slot)',
        release_or_cut_is_not_initialization=True,
        retained_after_cut=dict(counter=retained.slots[0][1],force=retained.force,
                                actual_work=retained.energy[0].stock))


def local_source_at_initial_entry(payer, operating, active, funded_reset, population):
    """One-time native controls; queued payloads and old reservations are separate."""
    origin, side = operating.owner
    source = raw.LocalSourceBank(origin, side, payer, population)
    source.control[:] = [0] * source.BITS
    for slot in source.slots + [source.adc]:
        slot.admission = active
        slot.output = active
        slot.reset = not active
    for branch in source.branches:
        branch.bits.put(27, 1, int(active))
        branch.bits.put(28, 1, int(active))
    source.adc_bits.put(2050, 1, int(active))
    source.dispatch.put(1, 1, int(active))
    source.engine.store[:] = [0] * 96
    source.engine.put(89, 4, 4 if active else 0)
    source.engine.put(93, 1, 1)
    source.powered = source.admission = source.emit_gate = active
    source.energy = operating
    source.reset_work.stock = Q(raw.RESET_CAP if funded_reset else 0)
    for j in range(8):
        source.I[j] = raw.MASK if j % 2 else 0
    need(source.job is None and not source.engine.get(94) and source.reset_work.spent == 0,
         "One-time native entry minted a reset request or spent unavailable reset work")
    need(all(s.cell.capacity == 4096 and s.cell.stock == 4096 for s in source.slots+[source.adc]),
         "Boundary representative did not initially hold the stated slot work")
    return source


def old_native_claims(payer, lanes, population, isa, compiled, capacity, funded_reset):
    """An actual old paid queue and in-flight parcel with the local CPU present."""
    operating = charging.OperatingBank((2,0), capacity, Q(capacity))
    cpu = charging.FramedParent(isa,compiled,bank=operating)
    source = local_source_at_initial_entry(payer, operating, True, funded_reset, population)
    for lane in lanes:
        if lane.identity.source_bank == 0:
            source.attach(lane)
    joint = charging.JointCharge(operating,cpu,source.slots+[source.adc],raw.LocalSourceBank.DELTA)
    need(source.energy is cpu.bank is joint.bank and source.payer is payer,
         "CPU, source slots or raw rows use a duplicated owner")

    # Construct a possible coherent initial queue by actual funded offers.
    # The preparation is a witness for stored state, not 129 new simultaneous
    # physical CPU offers at initialization.
    j = 2*source.receivers.index(0)+1
    branch = source.branches[j]
    need(branch.offer(1, raw.MASK) == "accepted" and branch.tick() == "symbol",
         "Paid source slot did not emit its first actual symbol")
    first = branch.slots[0]
    child = branch.flights[0]
    destination = raw.LaneId(2,0,0,1)
    need(child.claim.destination == destination and branch.flight_cells[child.physical_slot] is child,
         "Old symbol changed its fixed receiver or physical slot")
    need(first.cell.stock == 2304 and first.cell.spent == 1792
         and source.local_heat == 1664 and child.stock == 128
         and first.cell.stock+source.local_heat+child.stock == 4096,
         "Parent DATA parcel, dissipation and flight do not partition its 4096 work")
    for i in range(128):
        value = 0 if i % 2 else raw.MASK
        need(branch.offer(1, value) == "accepted", "A legal old queue was excluded")
    need(branch.bits.get(7,8)==128 and branch.bits.get(26) and
         sum(s.claim is not None and s.claim.live for s in branch.slots)==129
         and branch.offer(1, 1)=="full", "Full plus serializing native claim bound failed")

    source.raw_heads[0] = raw.MASK
    need(source.source_start("fast",(0,))=="accepted", "Old paid ADC claim missing")
    old_adc = source.job
    need(source.adc.cell.stock==2816 and old_adc.payload is source.adc_bits,
         "Old ADC reservation and descriptor differ")
    need(source.reset_work.spent==0 and not source.engine.get(94),
         "Initial active source was secretly rearmed by spending reset stock")
    # Idle source cells are full; busy source cells cannot be refilled.
    elapsed=joint.flow_full_delivery(raw.LocalSourceBank.DELTA,source_powered=source.powered)
    need(elapsed==charging.Clock(raw.LocalSourceBank.DELTA,()) and cpu.cell.stock==10240
         and sum(joint.input_received)==0 and operating.stock==capacity-10240,
         "CPU half-charge funded or duplicated an already reserved input")
    source.cold_cut()
    seen=[]
    def receive(d,payload):
        seen.append((d,payload))
        source.deliver_symbol(d,payload)
    raw_spent_before_delivery = payer.spent
    branch.advance_wire(Q(1,8),receive)
    need(child.stock==child.spent==64 and not seen and source.job is old_adc,
         "Half-spent emitted parcel or concurrent ADC claim disappeared on source cut")
    branch.advance_wire(Q(1,8),receive)
    branch.advance_wire(Q(1,4),receive)
    need(seen==[(destination,raw.symbols(1,raw.MASK)[0])] and child.stock==0
         and payer.spent==raw_spent_before_delivery+8 and child.spent==128 and source.flight_heat==128
         and branch.flight_cells[child.physical_slot] is None
         and source.receivers_live[destination].queue.number(9,10)==512,
         "Old symbol failed once-only delivery/drop at its actual full receiver")
    need(first.claim.live and source.job is old_adc and not source.powered,
         "Receiving the emitted symbol retired a different still-local operation")
    joint.balance()
    return dict(reset_store_initially_full=funded_reset,old_queue=128,serializer_claims=1,
        queue_and_serializer_live=129,ADC_claim_retained=True,raw_I_words=8,
        recipient=destination.__dict__,per_record_work=4096,first_symbol_spent_from_parent=1792,
        source_heat_at_first_emission=1664,source_remaining_at_first_emission=2304,
        issued_symbol_work=128,half_remaining=64,symbol_flight_work_dissipated=128,
        receiver_full_drop=True,emitted_child_survives_cut=True,timed_parent_half_charge=10240)


def paid_source_reentry(payer, population, isa, compiled, capacity):
    """Separate post-cold local entry segment with an actual connected bank."""
    source=raw.LocalSourceBank(2,1,payer,population)
    need(source.reform()=="formed-unpowered" and source.reset_work.spent==504329,
         "Later rearm lacks its paid source-local cold preparation")
    slots=source.slots+[source.adc]
    need(all(s.cell.stock==Q(1,2) and s.reset for s in slots),
         "Post-dump work is not at its actual floors")
    # Actual connected E and eligible PC0 are supplied by the separate POWER
    # and prior parent-retirement orbit. This example does not refill E.
    operating=charging.OperatingBank((2,1),capacity,Q(capacity))
    cpu=charging.FramedParent(isa,compiled,bank=operating)
    bus=charging.JointCharge(operating,cpu,slots,raw.LocalSourceBank.DELTA)
    old=payer.spent
    need(source.begin_entry(operating) and source.energy is cpu.bank and payer.spent-old==256,
         "Actual U-paid entry request or operating identity changed")
    need(source.engine.get(94) and not source.admission and not source.emit_gate,
         "The new E connection supplied a free completed entry")
    delta=source.DELTA
    clock=bus.flow_full_delivery(delta,source_powered=source.powered)
    inputs_received=sum(bus.input_received)
    need(clock==charging.Clock(delta,()) and inputs_received==Q(84539311,2)
         and cpu.cell.stock==10240 and all(s.cell.stock==4096 for s in slots),
         "Timed shared post-dump cell recharge failed")
    clock=bus.flow_full_delivery(delta,source_powered=source.powered)
    need(clock==charging.Clock(delta,()) and cpu.recharge() and cpu.cell.stock==20480
         and operating.stock+inputs_received+20480==capacity,
         "Second CPU charge double-spent DATA or duplicated E")
    before=source.reset_work.spent
    need(source.entry_flow(Q(source.ENTRY_WORK,raw.CLEAR_RATE))
         and source.reset_work.spent-before==62506 and source.reset_work.spent==566835
         and source.admission and source.emit_gate and not source.engine.get(94),
         "Source did not consume the real paid strobe on the same bank")
    bus.balance()
    return dict(cpu_and_source_bank_identical=True,actual_charged_destinations=len(slots)+1,
        initial_operating_stock=capacity,remaining_operating_stock=operating.stock,
        DATA_ADC_transfers=inputs_received,cpu_timed_transfer=operating.supplied,
        cpu_charger_duration=2*delta,DATA_ADC_charger_duration=delta,
        actual_U_request_work=256,cold_native_work=504329,source_entry_work=62506,
        combined_reset_work=source.reset_work.spent,full_delivery_zero_other_draw_segment=True)


def ordinary_input_initial_points(population,resource,isa,compiled,capacity,source_capacity):
    """One-time native entry, retaining arbitrary bounded evidence values.

    The product law uses fixed LaneId incidence and distinct reset stores;
    representative boundary values exercise its physical state constructors.
    It is not a reset operation or a temporal publication theorem.
    """
    cases=[];reservations=[]
    for funded_reset in (False,True):
        payer=raw.SourceWork(2,source_capacity,source_capacity)
        captures={rb:{kind:raw.SharedCapture((2,0,rb),kind,payer)
                      for kind in ('primary','auxiliary')} for rb in (0,1)}
        lanes=[]
        for source_bank in (0,1):
            for receiver_bank in (0,1):
                active=source_bank==0
                lane=raw.RawLane(population,raw.LaneId(2,source_bank,0,receiver_bank),
                                 payer,captures[receiver_bank])
                value=0 if receiver_bank==0 else raw.MASK
                # Values/countdowns are evidence, independent of native entry.
                for record in lane.ordered:
                    record.value=value;record.staged=raw.MASK-value
                    record.set_ttl(record.cap)
                    need(record.control[record.ENABLE] and not record.control[record.BUSY]
                         and not record.control[record.TICK_VALID]
                         and not record.control[record.RECEIPT_VALID] and record.claim is None,
                         'Initial raw words silently changed native control entry')
                for symbol in range(512):
                    need(lane.queue.offer(((1<<96)-1) if symbol%2 else 0)=='accepted',
                         'Full initial finite raw queue cannot be represented')
                mode=raw.OPEN if active else raw.MASK_MODE
                lane.mode=mode;lane.masked=not active
                lane.ingress=active;lane.write_gate=active
                lane.line=raw.ReassertingControlLine(words=[mode]*8,valid=[True]*8)
                lane.line.phases=[Q(j+1,64) for j in range(8)]
                lane.reset_work.stock=Q(raw.RESET_CAP if funded_reset else 0)
                for capture in lane.captures.values():
                    capture.snapshot=value
                    need(capture.clock_enabled and not capture.control_dirty
                         and capture.pending is None,'Initial capture is not a native entry')
                before=tuple((r.value,r.ttl) for r in lane.ordered)
                need(all((r.readable()==r.value) if active else (r.readable()==raw.MASK)
                         for r in lane.ordered),'Initial hard lane contact differs from its bank role')
                # Releasing a cut preserves the deliberately wrong data and
                # finite queue; it does not apply this initial constructor.
                lane.ingress=False;lane.write_gate=False
                need(before==tuple((r.value,r.ttl) for r in lane.ordered)
                     and lane.queue.number(9,10)==512,'An input cut manufactured fresh evidence')
                lane.ingress=active;lane.write_gate=active
                lanes.append(lane)
                cases.append(dict(source_bank=source_bank,receiver_bank=receiver_bank,
                    active_source=active,records=len(lane.ordered),raw_value=value,
                    arbitrary_countdown_cap=max(r.cap for r in lane.ordered),
                    pending_raw_symbols=lane.queue.number(9,10),control_mode=mode,
                    actual_reset_stock=lane.reset_work.stock,clock_phases=list(lane.line.phases),
                    no_old_tick_receipt_or_reset_job=True))
        need(all(a.reset_work is not b.reset_work for i,a in enumerate(lanes)
                 for b in lanes[i+1:]),'Initial raw reset stocks alias')
        for rb in (0,1):
            pair=[lane for lane in lanes if lane.identity.receiver_bank==rb]
            need(all(pair[0].captures[kind] is pair[1].captures[kind]
                     for kind in ('primary','auxiliary')),
                 'Source banks duplicated an existing shared capture')
        reservations.append(old_native_claims(payer,lanes,population,isa,compiled,capacity,funded_reset))
    need(resource['new_reset_cells']==162 and resource['new_reset_stock']==162*raw.RESET_CAP,
         'Initial source-row store product differs from the full owner inventory')
    return dict(representative_boundary_cases=cases,distinct_reset_cells=True,
        shared_capture_identity_preserved=True,initial_wire_tail=raw.WIRE_DELAY,
        native_source_reservations=reservations,transferred_work_per_emitted_symbol=128,
        product_index='(region, source host, source bank, fixed receiver neighbor, receiver bank)',
        ordinary_records='arbitrary bounded payload/countdown; enabled coherent native control, no stale tick/receipt claim',
        ordinary_queues='arbitrary bounded symbols/occupancy with coherent FIFO and native parser entry',
        capture_entry='enabled clock, arbitrary snapshot, no pending old read, fixed source/receiver/kind identity',
        active_control='OPEN code4 at all eight stages; no pending copy/reset job',
        cold_control='MASK code0 at all eight stages; hard ingress/write inhibition',
        source_TX_ADC_entry='source-affine native controls, 10321 actual cells, fixed flight slots and matched physical stock/reservations in each coherent active old-operation state',
        initial_only=True,release_does_not_restore_this_relation=True)


def pc0_boot_prefix(isa,c,bounds,bank_capacity,targets,source_capacity,population):
    Ports=program.ports_class(isa);ports=Ports(c);machine=isa.Machine(c,poison=isa.WORD_MASK)
    need(machine.pc==0,'Initial processor did not start at actual PC0')
    while not machine.io_counts['cpu_count'] and machine.steps<bounds['boot_active_upper']+100:
        need(machine.step(ports),'Actual PC0 boot prefix blocked')
    k=c.constants
    need(machine.io_counts['cpu_count']==1 and machine.pc==48 and machine.R[1]==1
         and machine.W[0]==3 and not machine.halted,'Changed-image caller/return state differs')
    need(machine.W[k['ENTRY']]==k['ENTRY_FRAMES']
         and machine.W[k['PLANT_ENTRY']]==k['PLANT_ENTRY_FRAMES']
         and machine.W[k['VECTOR_CURSOR']]==0 and ports.world_latch==(60,60)
         and machine.io_counts['send_command']==40 and machine.io_counts['source_invalidate']==1,
         'Actual entry omitted neutralization or its entry gates')
    need(machine.C==c.image and not machine.code_writes,'PC0 prefix changed current C')
    capacity=Q(bank_capacity)
    need(capacity.denominator==1,'Initial bank capacity lost its exact integer type')
    operating=charging.OperatingBank((0,0),int(capacity),capacity)
    paid=charging.FramedParent(isa,c,bank=operating,targets=targets)
    payer=raw.SourceWork(0,source_capacity,source_capacity)
    native=local_source_at_initial_entry(payer,operating,True,False,population)
    native.valid=True
    native.I[5]=0  # Old completed evidence. BOOT's real invalidation is observable.
    installed=native.slots+[native.adc]
    need(all(not slot.claim and slot.cell.stock==4096 and slot.cell.spent==0 for slot in installed)
         and not native.recharge_needed and native.reset_work.stock==0 and native.admission,
         'CPU-only charging projection requires full, idle initialized input cells')
    # Exact zero-deficit projection during THIS particular prefix. No start
    # or offer is executed, no old job, flight or queue can spend a cell, and
    # native clocks continue. Its full port contribution is identically zero.
    cpu_only=charging.JointCharge(operating,paid,(),native.DELTA)
    paid.W[:]=[isa.WORD_MASK]*len(paid.W)
    paid_ports=raw.native_source_ports(isa)(c,native)
    while not paid.io_counts['cpu_count'] and paid.steps<bounds['boot_active_upper']+100:
        cpu_only.flow_full_delivery(2*native.DELTA,source_powered=native.powered)
        need(paid.step(paid_ports),'Timed PC0 boot prefix blocked')
    need(paid.steps==machine.steps and paid.pc==machine.pc and paid.R==machine.R
         and paid.W==machine.W and paid.C==machine.C and paid_ports.world_latch==ports.world_latch
         and paid.pending is None and paid.fabric.token is None and not paid.fabric.link_storage_busy(),
         'Actual routed parent does not refine the initial caller state')
    paid.balance()
    need(paid_ports.I is native.I and paid.bank is native.energy is operating and
         not native.publications and not native.samples and native.job is None
         and not native.valid and native.I[5]==raw.MASK and native.reset_work.spent==0
         and all(not slot.claim and slot.cell.stock==4096 and slot.cell.spent==0 for slot in installed),
         'PC0 prefix did not preserve the zero-deficit source frame')
    need(2*native.DELTA<Q(1,4*2**26)/Q(101,100),
         'Timed CPU recharge exceeds fastest allowed ordinary charging window')
    routine=program.production_boot_prefix(isa,c,bounds,Ports)
    extra=machine.steps-routine['retired_instructions']
    need(extra==3 and extra<=16,'Actual entry exceeds the existing boot reserve')
    # Inspect the actual two-instruction frame return and unconditional main
    # loop. This is a control-spine check, not another executed full frame.
    tail=len(c.nodes)-2
    need(isa.decode(c.image[tail])==(isa.LI,2,0,0,0)
         and isa.decode(c.image[tail+1])[0]==isa.RET,'Unexpected frame return spine')
    spine=isa.Machine(c);spine.pc=tail;spine.R[1]=1;spine.W[0]=7;pp=Ports(c)
    while spine.pc!=c.labels['frame'] and spine.steps<16:
        need(spine.step(pp),'Actual frame/main return spine blocked')
    need(spine.steps==7 and spine.pc==c.labels['frame'] and spine.R[1]==1 and spine.W[0]==7,
         'Main loop does not return to the next actual frame')
    return dict(entry_PC=0,retired_instructions=machine.steps,next_PC=machine.pc,
        stack_depth=machine.R[1],actual_return_PC=machine.W[0],neutral_command_count=40,
        world=list(ports.world_latch),initialized_cursor=0,full_boot_executed=False,
        cutoff='First actual cpu_count return, before the long drain loop',
        direct_call_routine_fixture=routine,actual_entry_extra_instructions=extra,
        frame_return_and_main_spine=spine.steps,
        paid_parent_prefix=dict(retired_instructions=paid.steps,actual_operating_transfer=paid.bank.supplied,
            work_spent=paid.cell.spent,unused_work_dissipated=paid.cell.dumped,
            retained_operating_stock=paid.bank.stock,initial_operating_stock=bank_capacity,
            nominal_work_time_upper=paid.nominal_work_time_upper,
            parent_empty_and_no_pending=paid.pending is None and paid.cell.stock==0,
            actual_routed_parent=True,actual_shared_E_owner=operating.owner,
            source_I_native=True,old_completed_ADC_status_invalidated=True,initial_DATA_ADC_cells_framed=len(installed),
            DATA_ADC_work_in_this_idle_prefix=0,timed_CPU_recharge_each=2*native.DELTA,
            root_token_consumed=paid.fabric.token is None,
            no_retained_link_storage=not paid.fabric.link_storage_busy(),
            fixed_setter_targets=list(targets)),
        routine_harness_is_not_initial_caller_state=True)


def normalize(x):
    if isinstance(x,Q):return str(x)
    if isinstance(x,dict):return {k:normalize(v) for k,v in x.items()}
    if isinstance(x,(tuple,list)):return [normalize(v) for v in x]
    return x


def generate():
    isa=program.load_isa();c=program.compile_program(isa,design.design(isa));bounds=program.bounds(isa,c)
    geometry_text=frozen('threshold_geometry_results.json');geometry=json.loads(geometry_text)
    publication_text=frozen('publication_timing_results.json');publication=json.loads(publication_text)
    field_text=legacy.text_at(FIELD,'portability/threshold_field_source_results.json');point=json.loads(field_text)
    field_code=legacy.text_at(FIELD,'portability/threshold_field_source.py');field=cam.f
    need(program.digest(HERE/'threshold_field_source.py')==program.hash_text(field_code),
         'Current native class differs from the frozen field point')
    cam_text=legacy.text_at(CAM_BASE,'portability/cam_reformation_results.json');cam_point=json.loads(cam_text)
    for name,sha in cam_point['sources_sha256_lf'].items():
        need(program.digest(HERE/name)==sha,'Cam initial-control supplier changed: '+name)
    need(program.hash_text(field_code)==point['sources_sha256_lf']['threshold_field_source.py'],
         'Initial native model differs from reviewed source')
    image_hash=program.hash_text(json.dumps(c.image))
    need(image_hash==geometry['changed_image_sha256'] and bounds==geometry['bounds'],
         'Initial code/geometry binding changed')
    need(len(c.image)==8192 and all(type(w) is int and 0<=w<2**192 for w in c.image),
         'Initial image is not a finite ordinary code state')
    population=12*(6+2**98)+2
    parent_text=legacy.text_at(PARENT_BASE,'portability/parent_realization_results.json')
    parent_point=json.loads(parent_text)
    for name,sha in parent_point['sources_sha256_lf'].items():
        need(program.digest(HERE/name)==sha,'Paid initial parent supplier changed: '+name)
    retirement_text=legacy.text_at(PARENT_BASE,'portability/parent_retirement_results.json')
    retirement_point=json.loads(retirement_text)
    for name,sha in retirement_point['sources_sha256_lf'].items():
        need(program.digest(HERE/name)==sha,'Retirable initial parent supplier changed: '+name)
    input_text=legacy.text_at(INPUT_BASE,'portability/input_lifecycle_results.json')
    input_point=json.loads(input_text)
    for name,sha in input_point['sources_sha256_lf'].items():
        need(program.digest(HERE/name)==sha,'Initial ordinary input supplier changed: '+name)
    incoming=input_point['resources']
    charging_text=legacy.text_at(CHARGING_BASE,'portability/shared_bank_charging.py')
    need(program.hash_text(charging_text)==program.digest(HERE/'shared_bank_charging.py'),
         'Initial operating-bank law differs from its bound physical source')
    gate_text=legacy.text_at(GATE_BASE,'portability/threshold_gate_source_results.json')
    gate_record=json.loads(gate_text)
    need(program.hash_text(gate_text)==program.digest(HERE/'threshold_gate_source_results.json') and
         gate_record['image_sha256']==image_hash, 'Startup and gate require the same source point')
    for name, sha in dict(gate_record['immutable_inputs_sha256_lf'], **gate_record['sources_sha256_lf']).items():
        need(program.digest(HERE/name)==sha,'Startup gate supplier changed: '+name)
    gate=gate_record['costs']
    source_capacity=Q(gate['upstream_capacity'])
    need(source_capacity+gate['new_recoverable_storage']==Q(incoming['updated_upstream_capacity']),
         'Gate parcels and native input cells must have distinct capacity owners')
    actual_bank=Q(parent_point['cost_bounds']['actual_bank_capacity'])
    need(actual_bank.denominator==1,'Physical ordinary E capacity must be an exact integer')
    native=native_initial_points(field,population,cam_point['control_line']['dispatch_entry_clear_bits'],
        isa,c,actual_bank,source_capacity)
    targets=tuple('region0/host'+str(x) for x in incidence.neighbors(population,0))
    changed_prefix=pc0_boot_prefix(isa,c,bounds,actual_bank,targets,source_capacity,population)
    need(geometry['changed_paced_frame']['retired_instructions']+changed_prefix['frame_return_and_main_spine']
         <=bounds['padded_frame_upper'],'Main-loop instructions exceed actual frame allocation')
    a=geometry['arithmetic'];k=c.constants
    fmin=Q(a['frames']['min']);fmax=Q(a['frames']['max']);boot=Q(a['vectors']['boot'])
    prefix_elapsed_max=2**26
    remaining_drain=Q(k['BOOT_DRAIN_STEPS']-prefix_elapsed_max)/(Q(101,100)*2**26)
    need(remaining_drain==Q(300,101)>Q(publication['initialization']['boot_pending_tail']),
         'Admitted initial prefix has insufficient real remaining drain')
    world_accurate=boot+(k['PLANT_ENTRY_FRAMES']+1)*fmax+3
    world_settled=world_accurate+10000
    commissioning=Q(a['recognition_allocation'])
    need(world_settled<commissioning==50000,'Initial world bootstrap exceeds its source tube')
    need(Q(publication['initialization']['plant_entry_min'])>
         boot+publication['receipts']['plant']['arbitrary_counter_cap']+4,
         'Initial plant data acquired a fictitious sample history')
    need(Q(publication['initialization']['maintenance_entry_min'])>
         boot+publication['receipts']['maintenance']['arbitrary_counter_cap']+4,
         'Initial maintenance data did not drain')
    full=Q(a['reconstruction_startup_allocation'])
    need(full==commissioning+Q(a['vectors']['data_and_pool_prepare'])+
         Q(a['vectors']['freshness']),'Changed split initialization allocation')
    # Every cold activation starts at actual zero. The no-earlier-loss
    # implication also needs the stated nominal cam/keeper and abort law.
    earliest_loss=Q(k['WARM_AT'])/Q(a['physical_inputs']['stroke_max'])
    job=Q(a['watchdog']['complete_timer_job'])
    need(full+job<earliest_loss,'Initial keeper cannot cover the complete nontransferable job')
    write_time=Q(a['vectors']['write_time'])
    cutoff=Q(a['geometry']['earliest_cutoff'])
    first_copy=full+write_time
    need(first_copy<cutoff and first_copy<earliest_loss,
         'Initial donor formation can be overtaken by the first uncharged write corridor')
    tube=2*Q(1,10**7)*commissioning
    need(tube==Q(1,100)<Q(1,20),'Initial world tube consumes the reserve')
    tracking=Q(publication['world']['tracker']['tracking_error'])
    need(tracking<Q(1,25),'Initial formed keeper lacks the conditional collar supplier')
    itinerary_text=legacy.text_at(ITINERARY_BASE,'portability/interrupted_renewal_results.json')
    itinerary=json.loads(itinerary_text)
    for name,sha in itinerary['sources_sha256_lf'].items():
        need(program.digest(HERE/name)==sha,'Interrupted-entry supplier changed: '+name)
    need(itinerary['actual_image_sha256']==image_hash
         and Q(itinerary['all_role_initialization'])==full
         and Q(itinerary['old_partial_allocation'])==Q(a['partial_time_allocation']),
         'Interrupted itinerary does not refine the same initial/phase source')
    sequence=Q(itinerary['corrected_sequence_allocation']);H=Q(a['candidate_H'])
    need(Q(itinerary['H'])==H and itinerary['raw_cover']==a['raw_token_cover'],
         'Itinerary changed the source horizon or cover')
    residual=sequence-full
    need(residual==Q(itinerary['corrected_partial_allocation'])+Q(a['abort_time_allocation'])+
         2*Q(a['fresh_half_time'])+Q(a['old_suffix_allocation']),
         'Initialization was charged twice or removed from the return allocation')
    need(full+residual<H,'Split bootstrap loses the deadline margin')
    epsilon=Q(2,11**10);W=2**98+6
    service=Q(3,10)*(1-Q(6,population))-Q(W,population)
    formed_service=(Q(3,10)-epsilon)*(1-Q(6,population))-Q(W,population)
    need(service>formed_service>Q(1,10),'Initial actual service does not fit the global consumer')
    resources=point['point']['resources']
    controls=cam_point['arithmetic']['resources']
    need(Q(controls['unchanged_upstream_capacity'])==Q(resources['upstream_capacity'])
         and controls['additional_recoverable_capacity']==0,'Cam changed initial recoverable capacity')
    joined_burst=Q(resources['upstream_burst'])+Q(controls['added_upstream_burst'])
    joined_rate=Q(resources['upstream_rate'])+Q(controls['added_upstream_rate'])
    joined_reserve=Q(resources['upstream_capacity'])-joined_burst-2*joined_rate
    need(joined_reserve==Q(controls['usable_reserve_lower'])>1,
         'Initial source spent the old field-only reserve after adding cam control')
    need(Q(incoming['updated_upstream_capacity'])+incoming['new_reset_stock']==Q(resources['upstream_capacity'])
         and Q(incoming['unchanged_total_host_capacity'])==Q(resources['unchanged_total_host_stock']),
         'Initial input reset stores lack a conserved source inventory')
    joined_capacity=Q(incoming['updated_upstream_capacity'])
    joined_burst+=Q(incoming['added_upstream_burst'])
    joined_rate+=Q(incoming['added_upstream_rate'])
    joined_reserve=joined_capacity-joined_burst-2*joined_rate
    need(joined_reserve==Q(incoming['usable_reserve_lower'])>1,
         'Initial source omitted the actual input-control demand')
    pr=retirement_point['resources']
    need(pr['new_reset_capacity']==0 and pr['new_reset_charger_cap']==0
         and Q(pr['unchanged_U_capacity'])==Q(resources['upstream_capacity'])
         and Q(pr['old_external_rate_slack'])>=0 and pr['old_metadata_slack']>=0,
         'Parent retirement does not fit the retained owner/reset allocation')
    need(Q(pr['combined_shared_reset_work'])<Q(pr['one_actual_reset_capacity'])
         and Q(pr['unchanged_cam_prepared_upper'])==Q(cam_point['arithmetic']['physical_prepared_upper']),
         'Parent cleanup changes the input/cam formation budget')
    joint_reaction=Q(incoming['complete_joint_reaction'])+Q(pr['added_parent_gate_reaction'])
    need(joint_reaction<field.REACTION,'Separately checked input/parent reactions exceed the joint field bound')
    pre_gate_reaction=joint_reaction
    joint_reaction+=Q(gate['added_joint_reaction'])
    need(joint_reaction==Q(gate['combined_joint_reaction'])<field.REACTION,'Gate mechanical load omitted')
    joined_capacity=source_capacity
    joined_rate+=Q(gate['upstream_rate_added'])
    joined_burst+=Q(gate['upstream_burst_added'])
    joined_reserve=joined_capacity-joined_burst-2*joined_rate
    need(joined_rate==Q(gate['combined_upstream_rate'])<Q(gate['offered_supply'])
         and joined_reserve==Q(gate['minimum_U_after_additions'])>2048,
         'One host U must fund all gate and source operations, including its sampler strobe')
    ordinary_inputs=ordinary_input_initial_points(population,incoming,isa,c,int(actual_bank),source_capacity)
    reentry_payer=raw.SourceWork(2,source_capacity,source_capacity)
    reentry=paid_source_reentry(reentry_payer,population,isa,c,int(actual_bank))
    entry_bound=Q(incoming['local_source_entry_time'])
    need(entry_bound==raw.CONTROL_DELAY+Q(raw.LocalSourceBank.ENTRY_WORK,raw.CLEAR_RATE)+raw.LocalSourceBank.DELTA
         ==Q(1139845121,2**30),'Native POWER-to-entry/charge budget changed')
    old_residence=Q(129,256)+Q(1,4)+Q(513,2048)
    receipt_suffix=2*Q(incoming['receipt_job_delay'])
    total_native_tail=entry_bound+Q(1,64)+old_residence+receipt_suffix
    parent_suffix=Q(1,64)+Q(1,2**26)
    need(old_residence==Q(2057,2048) and receipt_suffix==Q(1,8192)
         and total_native_tail==Q(2235213825,2**30)
         and parent_suffix+total_native_tail<remaining_drain,
         'Real input/parent effects may outlive the prepublication drain')

    need(ordinary_inputs['initial_wire_tail']<remaining_drain,
         'The new input source leaves old emitted evidence beyond the initial drain')
    files=('THRESHOLD-INITIALIZATION.md','threshold_initialization.py','threshold_program_model.py',
           'threshold_program_source.py','threshold_design.py','threshold_incidence_model.py',
           'constructors.py','legacy_realization.py','threshold_publication_model.py',
           'cam_reformation.py','CAM-REFORMATION.md','cam_reformation_results.json','threshold_field_source.py',
           'parent_realization.py','PARENT-REALIZATION.md','parent_realization_results.json',
           'parent_retirement.py','PARENT-RETIREMENT.md','parent_retirement_results.json',
           'input_lifecycle.py','INPUT-LIFECYCLE.md','input_lifecycle_results.json','shared_bank_charging.py','SHARED-BANK-CHARGING.md',
           'interrupted_renewal.py','INTERRUPTED-RENEWAL.md','interrupted_renewal_results.json',
           'LEGACY-REALIZATION.md','legacy_realization_results.json','threshold_field_source_results.json','THRESHOLD-FIELD-SOURCE.md')
    frozen_inputs={BASE+':portability/threshold_geometry_results.json':geometry_text,
        BASE+':portability/publication_timing_results.json':publication_text,
        FIELD+':portability/threshold_field_source_results.json':field_text,
        FIELD+':portability/threshold_field_source.py':field_code,
        CAM_BASE+':portability/cam_reformation_results.json':cam_text,
        PARENT_BASE+':portability/parent_realization_results.json':parent_text,
        PARENT_BASE+':portability/parent_retirement_results.json':retirement_text,
        INPUT_BASE+':portability/input_lifecycle_results.json':input_text,
        CHARGING_BASE+':portability/shared_bank_charging.py':charging_text,
        GATE_BASE+':portability/threshold_gate_source_results.json':gate_text,
        ITINERARY_BASE+':portability/interrupted_renewal_results.json':itinerary_text}
    for name in ('INITIAL-RETURN.md','PORT-SOURCE.md','CYCLE.md','HYBRID.md'):
        frozen_inputs[program.BASE+':local-control/'+name]=program.frozen(name)
    return normalize(dict(status='constructed initial relation and derived conditional split-bootstrap supplier',
        base=BASE,field_base=FIELD,cam_base=CAM_BASE,parent_base=PARENT_BASE,input_base=INPUT_BASE,shared_bank_base=CHARGING_BASE,gate_base=GATE_BASE,itinerary_base=ITINERARY_BASE,python_version=sys.version,frozen_isa_sha256=isa.source_hash,
        actual_image_sha256=image_hash,code_cells=len(c.image),population=population,
        initial_native_state=native,initial_ordinary_input_state=ordinary_inputs,later_paid_source_entry=reentry,changed_image_boot_prefix=changed_prefix,
        joined_initial_resources=dict(upstream_capacity=joined_capacity,
            upstream_burst=joined_burst,upstream_rate=joined_rate,usable_reserve_lower=joined_reserve,
            additional_cam_information_bits=controls['added_control_bits'],
            additional_input_information_bits=incoming['additional_control_bits'],
            additional_input_reset_stock=incoming['new_reset_stock'],
            physical_input_reset_cells=incoming['new_reset_cells'],
            acyclic_source_inventory_precedes_initialization=True,
            parent_retirement_new_reset_stock=pr['new_reset_capacity'],
            parent_retirement_shared_reset_work=pr['combined_shared_reset_work'],
            parent_reset_bitmap_bits=pr['parent_control_bits'],
            input_parent_cam_field_joint_reaction=pre_gate_reaction,
            combined_gate_reaction=joint_reaction,additional_gate_stock=gate['new_recoverable_storage'],
            initial_cam_words_are_state_not_READY=True),
        initial_relation=dict(keeper='A; symmetric relabeling permitted',
            active_code='actual changed compiled C at its physical rails; BOOT or a prefix of that same image, never frozen B80 addresses',
            active_tracker=Q(3,5),active_mailbox=Q(3,5),pending_WORLD_records=Q(3,5),actual_held_DAC=Q(3,5),active_activation=k['WARM_AT'],
            cam_guard_offset=[0,8000],cam_guard='actual keeper-side initial guard',
            NORMAL_STOP=True,FULL=False,ACTIVE=False,
            active_clamp=k['CLAMP_LIMIT'],active_writer_contact=False,
            active_cut=0,active_shunt=0,active_isolation=0,active_reset=k['RESET_LIMIT'],active_seating=12000,
            cold_cut=k['CUT_LIMIT'],cold_shunt=40000,cold_isolation=40000,
            cold_clamp=0,cold_reset=0,cold_seating_range=[0,12000],
            cold_activation=0,cold_energy_and_transit=0,cold_tracker_interval=[-1,1],cold_output_weight=0,
            inactive_code='arbitrary retained physical bit states, isolated from CPU/read service until actual formation',
            ordinary_command_fields_and_pending_commands='neutral; no arbitrary old CUT or MODE parent',
            raw_input_records_and_data_queues='arbitrary bounded evidence with coherent initial native FIFO/receipt/capture control; no fictitious sample times',
            raw_input_control_entry='actual initial_ordinary_input_state; active OPEN and cold MASK; later corruption requires physical source-row reformation',
            clocks='independent phases and admissible uncertain rates',world_box=[Q(2,5),Q(3,5)],
            host_and_coupler_initial_heat='within the recorded combined-energy initialization',
            upstream_initial_stock=joined_capacity,
            total_host_capacity_envelope=Q(resources['unchanged_total_host_stock']),
            fault_overlays='actual raw direct/physical footprints within hard state/flow caps; charged from time0',
            parent_route_initial_state='actual timed FramedParent root/return cuts and no live token; same physical setter; PC0 or the actual routed same-image paid prefix',
            initial_debt_clearing='conditional on actual finite initial-pipeline drainage, clock and custody suppliers'),
        bootstrap=dict(initial_drain_elapsed_max_instructions=prefix_elapsed_max,
            actual_remaining_initial_drain_min=remaining_drain,native_source_entry_upper=entry_bound,
            old_ADC_upper=Q(1,64),old_accepted_TX_flight_RX_upper=old_residence,
            old_retained_tick_receipt_upper=receipt_suffix,old_input_total_after_POWER=total_native_tail,
            nominal_old_parent_upper=parent_suffix,old_parent_plus_native_tail=parent_suffix+total_native_tail,
            prepublication_native_slack=remaining_drain-parent_suffix-total_native_tail,
            latest_accurate_DAC=world_accurate,latest_world_tracking=world_settled,
            early_commissioning=commissioning,world_tracking_slack=commissioning-world_settled,
            initial_displacement=tube,initial_reserve=Q(1,20),
            all_role_commissioning=full,early_world_not_delayed_to_vector_ready=True,
            first_nominal_keeper_loss_lower=earliest_loss,complete_job=job,
            initial_whole_job_slack=earliest_loss-full-job,
            initial_ready_plus_write=first_copy,
            initial_write_cutoff_slack=cutoff-first_copy,
            initial_donor_interval_slack=earliest_loss-first_copy,
            first_write_scope='uncharged initial target with fresh corridor start<=t_full; actual exclusion and no relevant interruption; later starts use the maintained-donor supplier',
            initial_service=service,later_formed_service=formed_service,
            recurrence_after_initialization=residual,H=H,H_slack=H-full-residual,
            fresh_phase4_extra=Q(itinerary['extra_fresh_phase4_and_band']),
            corrected_partial_itinerary=Q(itinerary['corrected_partial_allocation']),
            no_second_charge_of_initialization=True),
        source_premises=['complete ordinary parent/port nominal timing under actual funded entry',
            'initial native point at all uncharged sources, not restoration by release',
            'actual-cam/keeper/abort implication: initial A service cannot be lost before initially-zero B reaches warm',
            'actual overlap and mutable-code/field custody after first normal handover',
            'one common raw history and its execution/recipient-slot/export projections',
            'source-local reservoir, thermal and physical caps on the protected prefix'],
        remaining=['complete same-history physical source admission and all-mode continuation',
            'paid parent/port realization and actual reset/cam/phase mappings',
            'full charged/interrupted-state retirement and common recurrent closure',
            'positive spatial-density history and independent frozen transfer'],
        sources_sha256_lf={name:program.digest(HERE/name) for name in files},
        immutable_inputs_sha256_lf={name:program.hash_text(text) for name,text in frozen_inputs.items()},
        full_hybrid_trace=False,independent_review_pending=True,
        independent_review_scope='prior bounded initial-state/input/resource review; the timed shared-bank/native entry, physical flight and expanded old-tail join await independent review',
        program_completion=False))


def main():
    parser=argparse.ArgumentParser(description=__doc__);g=parser.add_mutually_exclusive_group(required=True)
    g.add_argument('--write',action='store_true');g.add_argument('--check',action='store_true');args=parser.parse_args()
    result=generate();path=HERE/'threshold_initialization_results.json'
    if args.write:path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n',encoding='utf-8',newline='\n')
    else:need(json.loads(path.read_text(encoding='utf-8'))==result,'Initial-state record differs')
    print('PASS finite native initial state and conditional split bootstrap; full source remains open')


if __name__=='__main__':main()

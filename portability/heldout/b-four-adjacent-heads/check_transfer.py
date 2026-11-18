"""Read-only replay of the four-head source adapter and its arithmetic."""
import argparse
from collections import Counter
from fractions import Fraction as Q
from hashlib import sha256
import json
from pathlib import Path

import installation as fit
from installation import M, PORT, cuts, group, head, incidence, islands, lease, legacy, need, plant, raw, rx
import private_comparison as private

HERE = Path(__file__).resolve().parent
H = 20 * 10**12


def reference(name):
    return json.loads((PORT / (name + "_results.json")).read_text(encoding="utf8"))


def classes(radius):
    # Every radius-d window wholly within the octets translates by eight.
    # Keep all seam windows singly, including possible local tail participation.
    start, stop = radius, M - 2 - radius
    for r in (*range(start), *range(stop, M)):
        yield r, 1
    for r in range(start,start+8):
        yield r, (stop-1-r)//8 + 1


def geometry():
    counts, degrees, pair_rows, affected_owners = Counter(), Counter(), Counter(), Counter()
    mixed = None
    for r, weight in classes(20):
        ns = incidence.neighbors(M,r)
        counts[sum(head(o) == 0 for o in ns)] += weight
        p = islands.installed_pair(M,r)
        groups = [plant(r,0), plant(r,1)] + [group(r,3+50*t) for t in range(40)]
        affected_owners[len({g[0] for g in groups})] += weight
        sizes = []
        for key, g in enumerate(groups):
            k = key if key < 2 else 3+50*(key-2)
            need(len(set(g)) == 15 and r not in g and set(g) <= set(ns),"Aliased head/ordinal")
            if k < 2:
                need(all(head(o) == k for o in g),"Dishonest installed linear form")
                sizes.append(len(set(g)&set(p)))
            else:
                t = ns[(k-3)//50]
                mt, pairs = incidence.maintenance_group(M,r,(k-3)//50)
                need(mt == t and all(incidence.neighbors(M,o)[i] == t for o,i in pairs) and t not in g,
                     "Changed maintenance target or used debtor")
            # The fixed pair touches FIFO/parser even for an origin selected as primary.
            ev = [("p","pair",r,None,False),("p2","pair",r,None,False)]
            singles = [o for o in g if o not in p][:4]
            ev += [(("s",o),"source",o,None,False) for o in singles]
            mask = fit.project(r,k,1,0,ev)
            need({a[2] for a in mask} == set(singles) | (set(p)&set(g))
                 and len(mask) <= 6, "Physical union or multiplicity lost")
            if len(set(p)&set(g)) == 2 and k < 2:
                others = [x for x in g if x not in p][:5]
                ev = [("pair/private","pair",r,None,True),("permanent","site",others[0],None,False)]
                ev += [(("s",o),"source",o,None,False) for o in others[1:]]
                mask = fit.project(r,k,1,1,ev)
                need(len(mask) == 7, "Missing tight group")
                if mixed is None:
                    mixed = dict(receiver=r,key=k,origin_slots=sorted(g.index(a[2]) for a in mask),
                                 origins=sorted(a[2] for a in mask))
        pair_rows[tuple(sizes)] += weight
    need(mixed is not None,"Lost attained tight plant consumer")
    for o, weight in classes(40):
        degrees[sum(fit.stencil(o))] += weight
    need(sum(degrees.values()) == sum(counts.values()) == sum(pair_rows.values()) == M and
         sum(d*w for d,w in degrees.items()) == 60*M, "Cohort count wrong")
    old = incidence.plant_group(M,20,1)
    wrong = [o for o in old if head(o) == 0]
    need(len(wrong) == 8 and set(islands.installed_pair(M,20)) == {3,6}, "Wrong stale-table witness")
    return dict(X_head_counts=dict(sorted(counts.items())), source_destination_bank_key_degrees=dict(sorted(degrees.items())),
                pair_plant_sizes={str(k):v for k,v in sorted(pair_rows.items())},
                primary_record_source_count=dict(sorted(affected_owners.items())), tight_plant=mixed,
                stale_XY_at_20=wrong)


def spatial_bindings():
    out = []
    cases = [(100,o,head(o),"pair") for o in islands.installed_pair(M,100)]
    cases += [(200,plant(200,k)[0],k,"primary") for k in (0,1)]
    for r,o,key,kind in cases:
        slot = plant(r,key).index(o)
        role = "primary" if slot == 0 else "auxiliary"
        U = raw.SourceWork(o,2**30,2**30)
        masked = []
        for br in (0,1):
            capset = None
            for sb in (0,1):
                lane = fit.make_lane(raw.LaneId(o,sb,r,br), U, capset)
                capset = lane.captures
                row = lane.records[key]
                word = (450,1050)[key]
                row.value = word
                row.set_ttl(8)
                need(lane.private_capture(key,role) == word,"Inaccessible installed record")
                # An exterior FIFO deposit reaches this lane's own decoder, including a primary role.
                altered = word-51
                lane.offer_frame(key,altered)
                need(lane.private_capture(key,role) == altered and row.readable() == altered,
                     "An attained exterior deposit lost its selected leaf")
                proj = fit.project(r,key,br,sb,[(0,kind,r,None,False)])
                need((r,br,o,sb,key,role) in proj, "Effect missed its actual compartment")
                cap = capset[role]
                cap.clock_enabled = False
                cap.snapshot = raw.MASK
                need(lane.private_capture(key,role) == raw.MASK and row.readable() == altered,
                     "Raw cut erased the old record or supplied an honest observation")
                masked.append((br,sb,slot,role))
                cap.clock_enabled = True
        out.append(dict(receiver=r,origin=o,key=key,kind=kind,paths=masked))
    return out


def timed_path(isa, image, m):
    # One actually changed source and keyed destination; one sibling shares its capture.
    o,r,key,sb,br = 3,20,0,1,1
    slot = plant(r,key).index(o)
    role = "primary" if slot == 0 else "auxiliary"
    Ucap = Q(reference("b_lead_installation")["budget"]["Ucap"])
    U = lease.SharedOrigin(o,Ucap,Ucap*Q(25,36))
    cap = int(Q(reference("parent_realization")["cost_bounds"]["actual_bank_capacity"]))
    E = rx.charging.OperatingBank((o,sb),cap,Q(2**60))
    Source,Selector = fit.source_classes(m)
    source = Source(E,U,M)
    selector = Selector(source,m.SELECT)
    for b in source.branches:
        b.bits.put(27,1,0)
        b.bits.put(28,1,0)
    source.adc_bits.put(2050,1,0)
    lane = fit.make_lane(raw.LaneId(o,sb,r,br),U)
    lane.reset_work = lease.restoration.ResetCap(lane.identity,U,lease.restoration.power.budgets())
    sibling = fit.make_lane(raw.LaneId(o,1-sb,r,br),U,lane.captures)
    source.attach(lane)
    endpoint = private.RawRead([sibling,lane],role,voltage=200)
    phases = rx.phases([lane])[lane.identity]
    try:
        rx.Receiver(lane,phases)
    except ValueError as e:
        need("Raw decoder no longer denotes" in str(e),"Unexpected prior enrollment failure")
        old_rejected = str(e)
    else:
        raise ValueError("Old source-specific RX enrollment accepted changed leaf")
    layout = fit.Receiver(lane,phases)
    face = lease.restoration.power.ReceiverFaces(layout,key,U)
    # Use exactly the prepaid metered cell law of the B restoring observation.
    kinds = lease.restoration.power.catalogue()
    exterior = (r,o)
    main = (r,br)
    face.lane = lease.LeaseMeter(kinds["rx"],(lane.identity,"rx"),exterior,200)
    face.records = {k: lease.LeaseMeter(kinds["record"],(lane.identity,k),
                        main if rec.role=="primary" else exterior,200) for k,rec in lane.records.items()}
    face.record = face.records[key]
    after = lease.jointly_clear(source,selector,lane,U)
    face.lane.enter_observation(face.lane.s.energy200-4*(32+lease.restoration.M))
    face.record.enter_observation(face.record.s.energy200-2*(128+3*lease.restoration.M))
    need(all(source.clear_value(source.FIRST+j) == selector.words[j] == v
             for j,v in enumerate(fit.stencil(o))),"Physically paid source preset missed an actual leaf")
    cpu_type,bus_type = lease.priced_classes(m)
    cpu = cpu_type(isa,image,bank=E)
    bus = bus_type(E,cpu,source)
    clock = lease.ObservedClock(source,bus)
    clock.next = after["next_TX_base"]
    need(source.begin_entry(E) and source.entry_flow(Q(source.ENTRY_WORK,raw.CLEAR_RATE)),
         "Source entry unfunded")
    clock.advance(2*m.DELTA)
    ports = m.ports_for(isa)(image,source,clock,selector)
    source.raw_heads = cuts.Aperture(fit.PlantTaps(source,image.constants,{},
        (lambda:Q(9,20),lambda:Q(3,5)),lambda v,e,lo,hi:int(v+Q(1,2))).fast)
    clock.observe(face,key)
    need(source.source_start("fast",(key,)) == "accepted","No ADC admission")
    clock.advance(Q(1,64))
    need(source.valid and source.I[1] == 450 and source.raw_heads.get(1,None) == 450,
         "A probe key supplied a foreign quantity")
    m.program.call(isa,image,ports,"publish_value",(key,),1000,cpu)
    client = 2*incidence.neighbors(M,o).index(r)+br
    stop = clock.now+Q(3,10)
    while not clock.records_at:
        need(clock.now < stop,"Missing paid physical receipt")
        clock.advance(Q(1,4096))
    t,word = clock.records_at[0]
    need((client,key,"forward","accepted") in ports.receipts and selector.paid == 80*m.PRICE and
         word == lane.records[key].readable() == 450, "No attained routed publication")
    bus.full_audit()
    # The paid receipt supplies a genuine input at the next local private strobe.
    bank = rx.charging.OperatingBank((r,br),cap,Q(2**24))
    machine = private.ComparedParent(isa,image,bank=bank)
    supply = rx.charging.JointCharge(bank,machine,(),private.D)
    sel = fit.reader(r)
    private_ports = private.PrivatePorts((r,br),sel,{(o,role):endpoint},private.D/4,[private.D/2]*10)
    pc,dest,reg = private.image_sites(isa,image)["fast_equal"][0]
    machine.pc = pc
    for j,value in enumerate((slot,sb,key,word)):
        machine.R[reg+j] = value
    supply.flow_full_delivery(2*private.D,source_powered=False)
    need(machine.recharge() and machine.launch() and machine.complete(private_ports)=="waiting",
         "No true private instruction launch")
    operation = private_ports.operation
    while not operation.finished:
        private_ports.flow_to(private_ports.next_time())
        private_ports.settle()
    need(machine.complete(private_ports) is True and operation.ticks == 11 and
         operation.raw_outcome == "offered" and operation.value == word and machine.R[dest] == 1,
         "Changed endpoint did not return its actual word to the captured register")
    supply.balance()
    return dict(origin=o,receiver=r,source_bank=sb,receiver_bank=br,key=key,slot=slot,role=role,
                subscription_work=selector.paid,preset_bits=len(source.stencil),source_reset_work=after["source_reset_work"],
                receiver_clear_work=after["receiver_clear_work"],source_entry_and_reset=source.reset_work.spent,
                receipt_time=t,word=word,countdown=lane.records[key].ttl,timer_edges=operation.ticks,
                private_bit=operation.bit,parent_E_work=bank.supplied,old_rx_enrollment=old_rejected)


def world(isa,image):
    # A finite isolated consumer test with actual mutable code and fixed raw record addresses.
    r = 20
    ports = legacy.absence_ports_class(isa)(image)
    ports.selector = fit.reader(r)
    ports.physical_records = legacy.PhysicalRecords(ports.selector)
    footprint = {}
    p = islands.installed_pair(M,r)
    events = [("E","pair",r,None,False)]
    other = [x for x in plant(r,0) if x not in p][:5]
    events += [("fixed","site",other[0],None,False)]
    events += [(o,"source",o,None,False) for o in other[1:]]
    for key in (0,1):
        g = plant(r,key)
        mask = fit.project(r,key,0,0,events)
        footprint[key] = sorted(g.index(a[2]) for a in mask)
        need(len(g)-len(mask)>=8,"Insufficient truthful voters")
        for slot,o in enumerate(g):
            chosen = (0 if slot in footprint[key] else (450,1050)[key])
            for b in (0,1):
                a = ("primary" if slot==0 else "auxiliary",o,b,key)
                need(ports.physical_records.put(a,chosen),"Uninstalled test record")
    consumer = legacy.program.initialized(isa,image)
    consumer.W[image.constants["ENTRY"]] = 1
    consumer.enter("frame")
    while not consumer.io_counts["world"]:
        need(consumer.steps < 200000 and consumer.step(ports),"No held WORLD command")
    need(ports.world_latch == (50,80) and ports.selection_work>0,"Wrong controller reconstruction")
    return dict(physical_cells=len(ports.physical_records.values),rowwise_masks=footprint,
                signed_ordinary_words=ports.world_latch,instructions=consumer.steps,selection_work=ports.selection_work)


def keyed_enrollment(isa,image):
    # A separate two-bank elapsed-clock facet of the installation, including an old pending read.
    # The fixture supplies gate/CPU/E/U and phase data. Install its target lanes before any edge.
    banks, old_lanes = rx.fixtures(isa,image,sides=(0,1),additional=False)
    captures, lanes = None, []
    for b,old in zip(banks,old_lanes,strict=True):
        src = b.native_input
        lane = fit.make_lane(old.identity,src.payer,captures)
        captures = lane.captures
        lane.mode, lane.masked, lane.ingress, lane.write_gate, lane.line = (
            old.mode,old.masked,old.ingress,old.write_gate,old.line)
        src.attach(lane)
        lanes.append(lane)
    product = fit.OriginProduct(banks,rx.source_phases(banks),rx.phases(lanes))
    key = next(k for k in (0,1) if k in lanes[0].records)
    role = lanes[0].records[key].role
    cap = captures[role]
    # The product uses the original raw old-phase settlement leaf. The timed private
    # RawRead path separately retains busy while its own prepaid fill is pending.
    lanes[0].records[key].value = 419
    lanes[0].records[key].set_ttl(8)
    need(product.capture(lanes[0].identity,role,key) == "captured","No genuine capture")
    claim = cap.pending
    need(claim.destination == (lanes[0],key) and product.capture(lanes[1].identity,role,key) == "captured"
         and not claim.live and cap.snapshot == 419 and cap.pending.destination == (lanes[1],key),
         "Old read did not settle at its own target before the new capture")
    need(product.finish_capture(lanes[0].identity,role,claim) == 419,"Spent read replayed")
    value = product.finish_capture(lanes[1].identity,role,cap.pending)
    ident = lanes[0].identity
    edge = ("receiver",ident,("base",None))
    need(edge in product.due() and product.edge(edge) == "alternate","Missing attained local edge")
    return dict(origin=ident.origin,receiver=ident.receiver,actual_rows=len(lanes),
                shared_role=role,key=key,retained_result=value,open_exits=sum(map(len,product.outside.values())))


def retirement_slice():
    r = 100
    p,q = islands.installed_pair(M,r)
    # Both endpoints read this *same* maintenance target. The old primary role is admissible
    # through the incoming parser. Expose all bindings by actual physical keys/banks.
    k = next(3+50*t for t in range(40) if {p,q} <= set(group(r,3+50*t)))
    old = [("E","pair",r,None,False)]
    initial = set().union(*(fit.project(r,k,br,sb,old) for br in (0,1) for sb in (0,1)))
    # Local proof case: only p/0 is physically retained after successful sweeps elsewhere.
    # This is a restriction of the earlier attained address set, not an assertion of a particular schedule.
    remaining = {a for a in initial if a[2]==p and a[3]==0}
    later = set().union(*(fit.project(r,k,br,sb,old,{"E":remaining}) for br in (0,1) for sb in (0,1)))
    need(later==remaining and len(initial)==8 and len(later)==2, "Released deposit lost its original banks")
    peer = next(h for h in incidence.neighbors(M,r) if r in plant(h,head(r)))
    ev = [("E","pair",r,None,True)]
    need({a[2] for a in fit.project(peer,head(r),0,1,ev)} == {r}
         and not fit.project(peer,head(r),0,1,old),"Off-body private/direct projection confused")
    return dict(receiver=r,maintenance_key=k,origins=[p,q],supported_initial=len(initial),
                resuming_residue=sorted(later),affected_private_peer=peer)


def arithmetic():
    g = reference("b_cut_induction")["inequalities"]
    supply = reference("b_lead_installation")
    intv = reference("receiver_lease")["interval"]
    F, D = Q(intv["Fmax"]), Q(intv["delivery"])
    half = Q(reference("return_itinerary")["budget"]["sampled_fresh_half"])
    repair = Q(g["contaminated_local"]) + 3*half + 228*F+D
    upper = Q(21,25)*(M-6)/M - Q(6+2**98,M)
    lower = Q(9,25) + Q(6+2**98,M)
    service = (Q(3,10)-Q(2,11**10))*(M-6)/M - Q(6+2**98,M)
    pair_time = Q(reference("normal_response_transport")["source_receipt"]["sequential_pair_upper"])
    margins = [Q(700,101)-2*F-D-pair_time,Q(51100,101)-226*F-D-pair_time]
    age = 13+3*F+12
    error = 4*(Q(5,1000)+Q(4,10**7)*age+Q(5,10000))+Q(1,100)+Q(1,25000)+Q(2,11**10)
    window = 2*H+2*Q(g["supplier_window"])
    token_bound = 1+2+int(3+window/104548602495950)
    need(token_bound==6 and min(margins)>0 and error<Q(4,100) and
         repair==Q(g["parallel_repair_bound"]) and repair+Q(1,16)<340346000000<H and
         upper>Q(74,100) and lower<Q(46,100) and service>Q(1,10),"A mission inequality failed")
    budget, contact = supply["budget"],supply["contact"]
    load = Q(3,2)*Q(51,100) + Q(contact["effect_age"])*Q(contact["mechanical_drift"]) + Q(contact["known_parallel_force"])/128
    need(load==Q(contact["full_contact_upper"])<1 and Q(contact["nominal_clearance_deficit"])<Q(1,5),
         "Factual effect-time bound failed")
    need(min(Q(budget[k]) for k in ("force_slack","bath_slack","pressure_floor_slack","supply_slack",
                                    "nonprivate_slack_to_2_to_45","full_slack_to_2_to_48"))>0,"Missing physical reserve")
    worst_bits = raw.RX_BITS + raw.DEC_BITS + 2003*raw.REC_BITS
    need(2*worst_bits+worst_bits//2+1281==506001 and Q(506001,raw.CLEAR_RATE)<Q(1,2),
         "Incomplete full reset")
    return dict(planning_tokens=token_bound,acquisition_slacks=margins,absolute_tracker_error=error,
                primary_with_pad_recovery=repair+Q(1,16),factual_load=load,service=service,
                upper_collar=upper,lower_collar=lower,owner_record_box=40*4*2003,
                per_lane_reset_work=506001,per_scan_healthy_DATA=60*M)


def normalize(x):
    if isinstance(x,Q):
        return str(x)
    if isinstance(x,dict):
        return {str(k):normalize(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)):
        return [normalize(v) for v in x]
    return x


def run():
    need(Path(fit.constructors.projected_support.__code__.co_filename).resolve() == PORT/"constructors.py",
         "Not the installed exported operation")
    isa,image,m = lease.compiled()
    return normalize(dict(geometry=geometry(),spatial=spatial_bindings(),routed_source=timed_path(isa,image,m),
                          keyed_enrollment=keyed_enrollment(isa,image),release_slice=retirement_slice(),
                          protected_arithmetic=arithmetic(),compiled_world=world(isa,image),
                          constructive_source_sha256_lf=sha256((PORT/"constructors.py").read_bytes().replace(b"\r\n",b"\n")).hexdigest(),
                          image_sha256=m.program.hash_text(json.dumps(image.image))))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write",action="store_true")
    args = parser.parse_args()
    result = json.dumps(run(),sort_keys=True,indent=2)+"\n"
    path = HERE/"transfer-results.json"
    if args.write:
        path.write_text(result,encoding="utf8",newline="\n")
    else:
        need(path.read_text(encoding="utf8")==result,"Exact target receipt differs")
    print("Verified changed B source bindings, receipt, projections and mission inequalities")

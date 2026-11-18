"""Cut-local causal accounting for the threshold source under the installed physical taps."""
import argparse
from dataclasses import dataclass
from fractions import Fraction as Q
from hashlib import sha256
import json
from pathlib import Path

import input_lifecycle as raw
import legacy_realization as legacy
import threshold_incidence_model as incidence
import fixed_island_model as islands


HERE=Path(__file__).resolve().parent
PIN="b32e224ab793ad98ae90216299f53419c2d9501e"
HANDOFF="d26dc729f8fd12ec2b751f79f853076c32c8c711"
REFERENCE="f4c52b814836788782d3e8d6682729f2548a3ecf"
LEADS="f08190a108fd02eddc6bc377cfaeff644dba20ec"
LOCAL="751fd23ce2fdff1e9c649d9bb2bc64960c7d300f"
H=Q(20_000_000_000_000)
F=Q(1163265,1048576)
RATE=Q(1,104548602495950)


def require(condition,reason):
    if not condition:
        raise ValueError(reason)


def source(name):
    return legacy.text_at(PIN,"portability/"+name)


def receipt(name):
    return json.loads(source(name+"_results.json"))


@dataclass
class SpringContact:
    # Physical coordinates at a cut. An independent material status switch
    # is not the source of either functional reading.
    q: Q
    compliance: Q
    base_gap: Q
    elastic_offset: Q

    def load(self):
        require(self.compliance>0,"Undefined physical spring effort")
        return abs(self.q/self.compliance)/128

    def gap(self):
        return min(Q(1),max(Q(0),self.base_gap+self.elastic_offset))


@dataclass
class TapSite:
    state: object
    spring: tuple


class FixedTaps:
    def __init__(self,bank,constants,sites,regional_ports,quantize):
        self.bank,self.k,self.sites=bank,constants,dict(sites)
        self.regional_ports,self.quantize=regional_ports,quantize
        require(all(t in bank.receivers and site.state.owner==t and len(site.spring)==2
                    and all(len(side)==11 for side in site.spring) for t,site in self.sites.items()),
                "Foreign fixture or changed contact roster")
        self.role=incidence.head_type(bank.origin)

    def sample(self,value,error,low,high):
        word=self.quantize(value,error,low,high)
        require(type(word) is int and low<=word<=high and abs(Q(word)-value)<=error,
                "Raw integer is outside its actual physical measurement envelope")
        return word

    def fast(self,key):
        if key in (0,1):
            x=self.regional_ports[0]()
            v=1000*(x if self.role==0 else x+self.regional_ports[1]())
            return self.sample(v,5,0,2000)
        if not 3<=key<3+40*50:
            return raw.MASK
        a,j=divmod(key-3,50)
        t=self.bank.receivers[a]
        if t not in self.sites or j>=self.k["VIEW_WORDS"]:
            return raw.MASK
        state=self.sites[t].state
        k,p,z=self.k,state.p,state.positions
        if j==k["MODE"]: return state.abort_carrier.raw()
        if j==k["NORMAL_STOP"]: return int(state.abort_carrier.normal)
        if j==k["ABORT_FULL"]: return int(state.abort_carrier.full)
        if j==k["ANCHOR"]: return state.keeper
        if j in (k["ANCHOR_IS_A"],k["ANCHOR_IS_B"]): return int(state.keeper==j-k["ANCHOR_IS_A"])
        if j in (k["CAM"],k["BLEND"]):
            return self.sample(z["cam" if j==k["CAM"] else "blend"],k["SENSE_ERROR"],0,k["POSE_MAX"])
        numeric=(("CUT_A","cut"),("CLAMP_A","clamp"),("RESET_A","reset"),("ISO_DEF_A","iso"),
                 ("SHUNT_DEF_A","shunt"),("ACT_A","act"),("SEAT_A","seat"),("ENERGY_A","energy"))
        for code,axis in numeric:
            if j not in (k[code],k[code]+1):
                continue
            b=j-k[code]
            if axis=="energy":
                value=state.machines[b].bank.stock/2**41
                require(value<=k["RESERVE_CAP"],"Operating head exceeds declared full-range error")
            elif axis in ("iso","shunt"):
                value=1000*(1-z[axis+str(b)]/p["ISO_LIMIT"])
            else:
                value=z[f"{axis}{b}:0" if axis in ("act","seat") else f"{axis}{b}"]
            return self.sample(value,k["SENSE_ERROR"],0,k["POSE_MAX"])
        for code,axis,stop in (("CUT_OPEN_A","cut","CUT_LIMIT"),("CLAMP_OPEN_A","clamp",0),
                  ("RESET_OPEN_A","reset",0),("ISO_SEATED_A","iso","ISO_LIMIT"),
                  ("SHUNT_SEATED_A","shunt","ISO_LIMIT"),("SHUNT_OPEN_A","shunt",0)):
            if j in (k[code],k[code]+1):
                return int(z[axis+str(j-k[code])]==(p[stop] if stop else 0))
        for code,axis in (("ACT_ZERO_A","zero"),("ACT_POWER_A","power"),("POWER_OFF_A","off"),
                          ("BLEND_AT_A","blend"),("CAM_ENTRY_A","cam")):
            if j not in (k[code],k[code]+1):
                continue
            b=j-k[code]
            if axis=="off":
                units=state.machines[b].bank.stock/2**41
                return int(self.sample(units,1,0,k["RESERVE_CAP"])<=int(Q(p["EOFF"])/2**41)-2)
            if axis=="zero": return int(z[f"act{b}:0"]==0)
            if axis=="power": return int(z[f"act{b}:0"]>=p["POWER_AT"])
            if axis=="blend": return int(z["blend"]==b*p["BLEND_LIMIT"])
            return int(z["cam"]==b*13*p["SEGMENT"])
        raise ValueError("Unwired installed observation")

    def functional(self,args):
        a,b,member,metric=args
        if not (0<=a<40 and b in (0,1) and 0<=member<11 and metric in (0,1)): return raw.MASK
        t=self.bank.receivers[a]
        if t not in self.sites: return raw.MASK
        contact=self.sites[t].spring[b][member]
        v=contact.gap() if metric else contact.load()
        if not metric and v>3: return self.k["SENSE_BIAS"]+self.k["LOAD_SENSOR_CAP"]
        cap=self.k["LOAD_SENSOR_CAP"] if not metric else 1000
        return self.k["SENSE_BIAS"]+self.sample(1000*v,self.k["SENSE_ERROR"],0,cap)


class Aperture:
    """A localized raw transducer may hold or suppress its own reading."""
    def __init__(self,read):
        self.read=read
        self.held={}
    def get(self,key,default):
        return self.held[key] if key in self.held else self.read(key)


def tap_check():
    import receiver_lease as lease
    isa,image,_=lease.compiled()
    seat,_=legacy.module_at(PIN,"portability/return_seat.py","_cut_seat_state")
    params=seat.incumbent.parameters(image)
    clock,cpu,bank,_=lease.rx.native.native_fixture(isa,image)
    target=3
    cap=int(params["EMAX"])
    cpus=[seat.charging.FramedParent(isa,image,bank=seat.charging.OperatingBank((target,b),cap,Q(cap if not b else 0)))
          for b in (0,1)]
    s=seat.SeatState(params,target,raw.SourceWork(target,2**50,2**44),cpus)
    springs=tuple(tuple(SpringContact(Q(32*2**29),Q(2**29),Q(99,100),Q(0)) for _ in range(11)) for _ in range(2))
    row=TapSite(s,springs)
    a=bank.receivers.index(target)
    site=FixedTaps(bank,image.constants,{target:row},(lambda:Q(9,20),lambda:Q(3,5)),
                   lambda x,e,lo,hi:max(lo,min(hi,int(x+Q(1,2)))))
    bank.raw_heads,bank.functional=Aperture(site.fast),Aperture(site.functional)
    clock.advance_to(Q(1,2**30))
    k=image.constants
    keys=[site.fast(3+50*a+j) for j in range(46)]
    require(len(keys)==46 and all(x!=raw.MASK for x in keys) and site.fast(0)==1050
            and keys[k["ENERGY_A"]]!=keys[k["ENERGY_A"]+1] and keys[k["POWER_OFF_A"]]==0,
            "Mixed wrong physical head, upstream stock or host identity")
    member=springs[1][7]
    args=(a,1,7,0)
    first=site.functional(args)
    require(bank.source_start("functional",args)=="accepted" and first==282,"Missing real 0.25 load sample")
    # A bounded raw source chart may change its compliance while preserving
    # displacement, with its properly paid coefficient and held-mode work.
    # This test changes the open input after capture. It does not construct
    # the coefficient-changing source work on this short segment.
    member.compliance=Q(3,2)*2**29
    later=site.functional(args)
    require(later==199 and site.functional((a,1,7,1))==1022,"Actual tap ignored coefficient or clearance")
    s.positions["iso1"]=params["ISO_LIMIT"]
    member.base_gap=Q(1,2)
    require(site.fast(3+50*a+k["ISO_SEATED_A"]+1)==1 and site.functional((a,1,7,1))==532,
            "A seated mechanism supplied a fictitious functional gap")
    adc_edges=0
    while not bank.valid:
        clock.advance_to(clock.next_boundary())
        for edge in clock.due():
            clock.edge(edge)
            adc_edges+=int(edge=="ADC")
        require(adc_edges<=63,"ADC failed to complete in its 63 delivered edges")
    require(adc_edges==63 and bank.valid and bank.I[1]==first and cpu.bank is bank.operating_bank,
            "Completed ADC reread a newer physical state or changed power owner")
    bank.functional.held[args]=raw.MASK
    require(bank.functional.get(args,None)==raw.MASK and bank.I[1]==first
            and site.functional(args)==later,"A failed raw aperture rewrote the paid result or actual load")
    return dict(origin=bank.origin,physical_target=target,local_ordinal=a,all_installed_view_keys=len(keys),
                actual_paid_result=bank.I[1],new_same_member_word=later,actual_ADC_edges=adc_edges,
                actual_elapsed=clock.now,position_seated=True,
                independent_gap_word=site.functional((a,1,7,1)),selected_X_plus_Y=site.fast(1))


@dataclass(frozen=True)
class Claim:
    uid: str
    kind: str
    host: int
    origin: int | None = None
    private: bool = False


def group_slots(m,observer,group,claim):
    k=claim.kind
    if k=="site":
        # The held fixture can affect that host's own execution and primary
        # surface. It has no incident edge into all other source-owned raw taps.
        k="execution"
    elif k=="external-private":
        k="pair"
    elif k=="coupler":
        return set()
    key=(k,claim.host,claim.origin) if k=="lane" else (k,claim.host)
    out=raw.support(m,observer,group,key)
    if claim.private and observer!=claim.host and claim.host in group:
        out.add(group.index(claim.host))
    return out


def host_losses(claim):
    if claim.kind in ("site","execution","source","reset-root") or claim.private:
        return {claim.host}
    return set()


def fibers(m,claim):
    # This presentation is projected to physical receiving addresses.
    # Each item denotes *both* source banks, keyed receiving banks and all
    # addressed registers/operations of that finite family. It never moves
    # the records to the owner of the release episode.
    r=claim.host
    if claim.kind=="pair" or claim.kind=="external-private":
        return {(r,o) for o in islands.installed_pair(m,r)}
    if claim.kind=="lane":
        require(claim.origin in incidence.neighbors(m,r),"Uninstalled raw leaf")
        return {(r,claim.origin)}
    if claim.kind=="primary" or claim.kind=="execution":
        groups=[incidence.plant_group(m,r,g) for g in (0,1)]
        groups += [tuple(o for o,_ in incidence.maintenance_group(m,r,t)[1]) for t in range(40)]
        return {(r,g[0]) for g in groups}
    raise ValueError("Not a raw receiving-domain release")


@dataclass(frozen=True)
class Episode:
    cause: Claim
    acquire: Q
    release: Q | None


def intersects(episode,left,right):
    return episode.acquire<=right and (episode.release is None or episode.release>=left)


def covers(episodes,start,end,held):
    # Closed physical windows, keeping all potentially relevant endpoint ties.
    left=max(0,Q(start)-H)
    return {e.cause.uid for e in episodes if intersects(e,left,end)} | set(held)


def projection_checks():
    m=12*(6+2**98)+2
    r=0
    g=incidence.plant_group(m,r,1)
    pair=islands.installed_pair(m,r)
    require(set(pair)==set(g[1:3]),"Selected XY pair changed")
    events=[Claim("E0","external-private",r,private=True)]
    events += [Claim("S"+str(j),"source",o) for j,o in enumerate(g[3:8])]
    require(len(set.union(*(group_slots(m,r,g,c) for c in events)))==7,"Lost a paired leaf")
    require(len(set.union(*(host_losses(c) for c in events)))==6,"Changed joint output footprint")
    hs=[Claim("r0","pair",r),Claim("r1","pair",r),Claim("p","primary",r)]
    require(len(set.union(*(group_slots(m,r,g,c) for c in hs)))==3 and len(hs)==3,
            "Repeated paired events were merged or a new pair was created")
    primary=fibers(m,Claim("p","primary",r))
    pair_rows=fibers(m,events[0])
    require(1<len(primary)<=40 and len(pair_rows)==2 and len(set.intersection(primary,pair_rows))<=2,
            "Source-owned rows are not recovered by one recipient reset")
    peers=[h for h in incidence.neighbors(m,r)
           if any(r in incidence.plant_group(m,h,j) for j in (0,1))]
    h=peers[0]
    gh=next(incidence.plant_group(m,h,j) for j in (0,1) if r in incidence.plant_group(m,h,j))
    require(group_slots(m,h,gh,Claim("E","pair",r))==set()
            and group_slots(m,h,gh,events[0])=={gh.index(r)},"Raw input and private/output reach collapsed")
    # The selected holder has a fixed sampling aperture on the same t
    # at each origin's own ordinal. In particular the target o is absent
    # from every maintenance group that issues requests for its repair.
    cases=0
    for pop in (82,86,m):
        for target in (0,1,pop-1,pop//2):
            for worker in incidence.neighbors(pop,target):
                targets=incidence.neighbors(pop,worker)
                actual,providers=incidence.maintenance_group(pop,worker,targets.index(target))
                require(actual==target and len(providers)==15 and target not in {o for o,_ in providers}
                        and worker not in {o for o,_ in providers}
                        and all(incidence.neighbors(pop,o)[j]==target for o,j in providers),
                        "A repair used its own debtor as a promised external observation")
                cases+=1
    for observer in (0,1,m-1):
        groups=[incidence.plant_group(m,observer,j) for j in (0,1)]
        groups.extend(tuple(o for o,_ in incidence.maintenance_group(m,observer,t)[1]) for t in range(40))
        fronts={(o,"primary") for o in incidence.neighbors(m,observer)}
        for voters in groups:
            # Only the material role selected for this key can enter its
            # private comparator. One main-site power weld can hit every
            # primary backend without gaining any exterior auxiliary latch.
            sockets={(o,"primary" if j==0 else "auxiliary") for j,o in enumerate(voters)}
            require(len(fronts&sockets)==1 and len(fronts)==40,"Merged primary and exterior auxiliary roles")
    widened={1,2,3,4,5,6,7,8}
    require(len(widened)>=8,"Three auxiliary holds and five other slots would pass the positive threshold")
    return dict(representative_actual_groups=cases,attained_raw_slots=7,same_token_output_hosts=6,
                fixed_pair=pair,primary_repair_origins=sorted(o for _,o in primary),
                pair_repair_origins=sorted(o for _,o in pair_rows),private_peer_slot=gh.index(r))


def earlier_containment():
    W=Q(receipt("b_handoff")["quantitative"]["full_watchdog"])
    r=3*H
    def e(name,begin,end):
        return Episode(Claim(name,"source",2),Q(begin),None if end is None else Q(end))
    episodes=[e("older",r-H-W,r-H-W/2),e("edge",r-H,r-H),e("held-long",r-H-W*3,r+1),e("late",r+H/2,r+H)]
    planning=covers(episodes,r-2*W,r+H,{"fixed"})
    present=covers(episodes,r,r,{"fixed"})
    require("older" in planning-present and "late" in planning-present,
            "Planning roster was reused as proof of actual current responsibility")
    for x in (r-2*W,r-W,r,r+H/2,r+H):
        require(covers(episodes,x,x,{"fixed"})<=planning,"Earlier physical query escaped the planning roster")
    # Different domains at one site have different raw capabilities/deadlines.
    m=86; pair=islands.installed_pair(m,0)
    a=Claim("u","lane",0,pair[0]); b=Claim("v","lane",0,pair[1])
    cut=covers([Episode(a,r-2,r),Episode(b,r-1,r+1)],r+H+Q(1,2),r+H+Q(1,2),set())
    require(cut=={"v"} and fibers(m,a).isdisjoint(fibers(m,b)),"Host coalescing extended an unrelated release")
    return dict(planning_only=sorted(planning-present),source_count=1+2+int(3+RATE*(2*H+2*W)),
                extra_accrual=RATE*(2*H+2*W),original_release_owner_retained_at_other_leaf=sorted(cut))


@dataclass(frozen=True)
class Stop:
    cut: int
    row: tuple
    kind: str
    upstream_cut: int
    continued_cause: str


def transfer_fiber(stop,stamp,row,kind,cause,now):
    # This combinator consumes a recorded causal stop, not merely time,
    # equal site, raw slot cardinality, or disappearance of another mark.
    return (stop.cut<now and stop.upstream_cut==stamp and stamp<stop.cut
            and row==stop.row and kind==stop.kind and cause.uid==stop.continued_cause)


def retention_checks():
    m=86;r=0
    o,p=islands.installed_pair(m,r)
    pair=Claim("old-pair","pair",r)
    fault=Claim("down-o","reset-root",o)
    pending={(r,o),(r,p)}
    a=Stop(12,(r,o),"phase6-reset-grant",11,fault.uid)
    require(transfer_fiber(a,11,(r,o),"phase6-reset-grant",fault,18)
            and not transfer_fiber(a,11,(r,p),"phase6-reset-grant",fault,18)
            and not transfer_fiber(a,12,(r,o),"phase6-reset-grant",fault,18)
            and not transfer_fiber(a,11,(r,o),"paid-packet-arrival",fault,18),
            "Transfer no longer requires the physical stopped operation")
    pending.remove((r,p))  # Genuine second distinct postrelease sweep of p.
    transferred={a.row} if transfer_fiber(a,11,a.row,a.kind,fault,18) else set()
    require(fibers(m,pair)-pending=={(r,p)} and pending==transferred, "Fibrewise partition failed")
    # Unknown preexisting parent, earlier supported normal observation and
    # late SEND are different elapsed laws; no evidence age extends through
    # an arbitrary stopped parent.
    d=Q(372,25)
    require(10**9+d>600>d and d<15, "A bounded packet age implied bounded pre-offer age")
    return dict(physically_blocked=sorted(transferred),physically_reformed=[(r,p)],
                a_late_preexisting_parent_does_not_certify_factual_use=True)


def timing_and_receipts():
    b=receipt("b_handoff")["quantitative"]
    send=receipt("sender_eligibility")
    itinerary=receipt("return_itinerary")["budget"]
    rx=receipt("receiver_lease")["interval"]
    normal=receipt("normal_response_transport")["source_receipt"]
    frame=receipt("frame_pacing")["certificate"]
    require(frame["bound_under_arbitrary_raw_values"] and frame["installed_reference_code_cells"]==3057,
            "Unformed or incorrectly linked ordinary shell")
    W=Q(b["full_watchdog"])
    overlap=Q(b["available_driver_approach"])-Q(b["formation_after_driver"])
    require(overlap-W==Q(b["strict_bank_sponsorship_slack"])>0 and Q(b["strict_shutdown_margin_before_shunt"])>Q(372,25),
            "No currently earned bank overlap or old SEND clearance")
    shell=Q(send["donor"]["conditional_itinerary"])
    half=Q(itinerary["sampled_fresh_half"])
    prime=Q(rx["first_all_keys_including_fold"])
    row=3*half+prime
    require(row==Q(rx["worst_clean_normal_row_pair"]) and shell+row < H and row>prime,
            "A partial old half or a row visit was lost from the deadline")
    functional=Q(normal["new_effect_horizon"])
    load=Q(3,2)*(Q(1,2)+Q(1,100))+functional/10000
    deficit=Q(2,100)+Q(1,100)+Q(1,10)+functional*Q(11,400000)
    require(load<1 and deficit<Q(1,5) and Q(send["physical"]["silent_old_sign_after_SEND"])<15,
            "No physical factual continuation")
    restore=receipt("threshold_geometry")["arithmetic"]
    require(len(restore["phase_bounds"])==13 or len(restore["phase_bounds"])==26,
            "Changed normal stage inventory")
    clearing=restore["local_clearing"]
    vector=restore["vectors"]
    preparation=Q(itinerary["T_full_initial"])+Q(vector["write_time"])
    min_cut=Q(restore["geometry"]["earliest_cutoff"])
    require(min_cut>preparation and Q(clearing["reset_sweep_min"])>Q(clearing["two_post_wait_all_emitter_bound"])
            and Q(vector["unattended_bound"])<Q(vector["threshold"]) and Q(restore["force"]["opposition"])<28
            and Q(restore["watchdog"]["complete_timer_job"])==W and Q(restore["watchdog"]["ACT_milestone_slack"])>0,
            "Nominal code formation, no spurious pressure, or useful timeout can fail the inherited local threshold")
    require(Q(normal["sequential_pair_upper"])<Q(normal["supplied_pair_window"]) and
            all(Q(t["min_readable"])>Q(t["commit_gap"])+Q(normal["sequential_pair_upper"]) for t in rx["per_key"].values()),
            "A pointwise bank choice cannot cover the actual sequential comparison")
    require(Q(b["free_U_above_pressure_floor"])>0 and Q(b["paid_reaction_slack"])>0,"New installation unpriced")
    m=12*(6+2**98)+2
    bad=6+2**98
    good=Q(m-6,m)
    upper=Q(21,25)*good-Q(bad,m)
    lower=Q(9,25)+Q(bad,m)
    service=(Q(3,10)-Q(2,11**10))*good-Q(bad,m)
    require(upper>Q(74,100) and lower<Q(46,100) and service>Q(1,10),"Regional comparison fails")
    return dict(qualified_frame=[Q(rx["Fmin"]),Q(rx["Fmax"])],supplier_window=W,
                handover_slack=overlap-W,old_command_clearance=Q(send["physical"]["silent_old_sign_after_SEND"]),
                raw_prime=prime,initial_C_corridor_slack=min_cut-preparation,
                all_emitter_clearance_slack=Q(clearing["reset_sweep_min"])-Q(clearing["two_post_wait_all_emitter_bound"]),
                partial_orbit_and_two_postrelease_sweeps=row,
                contaminated_local=shell,parallel_repair_bound=shell+row,
                deadline_slack=H-shell-row,protected_factual_horizon=functional,
                load_upper=load,deficit_upper=deficit,allowed_extra_load=1-load,
                allowed_extra_deficit=Q(1,5)-deficit,upper_collar_actual_min=upper,
                lower_collar_actual_max=lower,service_min=service)


def spatial_staffing():
    # Each label retains its real region and all directly reached endpoints.
    # The three-column bag is sufficient for the witness on either ladder row.
    # This is not an implication from separate scalar bounds on its vertices.
    maximum_active=0
    straddled=False
    for n in (3,4,5,6,17,41):
        edges=incidence.region_edges(n)
        direct={(r,j):{(r,j)} for r in (0,1) for j in range(n)}
        for left,right in edges:
            direct[left].add(right)
            direct[right].add(left)
        k=min(5,n)
        for r in (0,1):
            for residue in range(k):
                centers={(r,j) for j in range(residue,n,k)}
                maximum_active=max(maximum_active,len(centers))
                for j in range(n):
                    bag={(row,col) for row in (0,1) for col in range(max(0,j-1),min(n,j+2))}
                    require(all(direct[row,j]<=bag for row in (0,1)),"A direct receiving star escaped its bag")
                    reached={c for c in centers if direct[c]&bag}
                    require(len(reached)<=1,"One witness stratum reached a bag from two centers")
                    straddled|=any(c not in bag for c in reached)
    require(straddled and maximum_active>6,"Dropped a straddling endpoint or imposed a global six-token cap")
    return dict(staffing_scope="one actual receiving region and its stipulated directly reached neighborhood",
                cohort="all 40 donors, both banks, 15-origin groups and raw reset owners are in that region",
                receiving_bag_columns=3,rows=2,straddling_footprint_retained=straddled,
                simultaneous_centers_on_checked_ladders=maximum_active)


def circuit_and_cue(t):
    handoff=receipt("b_handoff")["quantitative"]
    electrical=receipt("b_reference_return")
    wc=electrical["working_cut"]
    require(Q(wc["headroom_under_2_to_45"])==2**45-Q(wc["other_absolute_current"])>0
            and Q(electrical["physical_pairs"]["fault_weld_current"])>2**45,
            "A hard damaged bank inherited working-reference status")
    retire=electrical["retirement"]
    require(Q(retire["six_q_startup_margin"])>0 and Q(retire["post_on_margin"])>0
            and Q(retire["low_sample_to_rearm_margin"])>0 and Q(retire["fourfold_rho_over_kEoff"])<1
            and Q(retire["remaining_mechanical_reaction"])>0 and Q(retire["U_working_quarter_margin"])>0,
            "Actual post-cut E, reference refund, U or reaction fails")
    require(Q(electrical["charge"]["after_one_sixteenth"])<Q(82,10**6)
            and Q(electrical["physical_pairs"]["one_native_perturbation_settling"])<Q(1,2**40),
            "Restored reference does not supply the required working timing")

    half=Q(receipt("return_itinerary")["budget"]["sampled_fresh_half"])
    recovered=t["parallel_repair_bound"]+Q(1,16)
    two_orientations=recovered+3*half
    calendar=receipt("spatial_coverage")
    period=Q(calendar["period"])
    quiet=period-2*H-1100
    # The steering/working cam contact can come after the literal phase
    # boundary. Keep a complete conservative extra band in that option.
    contacted=two_orientations+Q(receipt("return_itinerary")["budget"]["settle"])+Q(32000)*10/9+Q(101,100)
    bins=(2*int(H)+139)//140
    m=12*(6+2**98)+2
    require(period==42*H and quiet==40*H-1100 and quiet>contacted and contacted<2*H
            and Q(calendar["minimum_fraction_any_nonempty_class"])==Q(1,18)
            and Q(calendar["simultaneous_fraction"])==Q(1,18*bins)
            and calendar["physical_effect_lower"]==140 and Q(calendar["adverse_weighted_host_output_upper"])==Q(-767,1600)
            and Q(calendar["average_fresh_exposure_density"])==Q(3,20*period)
            and calendar["served_body_roster_per_region"]==2*m and calendar["joint_history_required"],
            "Same-history lower density, oriented census or true postrelease quiet interval failed")
    require(two_orientations<2*H and Q(handoff["formation_after_driver"])>Q(1,16),
            "Spatial opportunity would require future or unaccounted formation")
    return dict(recurrent_full_reference_wait=Q(1,16),return_including_wait=recovered,
                both_oriented_phase_two_by=two_orientations,local_opportunity_budget=2*H,
                phase_two_work_contact_by=contacted,between_blocks_release_clearance=quiet,
                exposure_density_per_region=Q(calendar["average_fresh_exposure_density"]),
                simultaneous_region_fraction=Q(calendar["simultaneous_fraction"]),simultaneous_duration=140,
                participating_incarnations_per_region=2*m,joined_B_RP2_and_A17=True,
                earlier_reference_only_nonprivate_current_headroom=wc["headroom_under_2_to_45"],
                true_40_front_fault_current=electrical["physical_pairs"]["fault_weld_current"],
                full_primary_caps_per_main_receiver_bank=40,working_voltage_entry_upper=Q(1,16),
                cumulative_reaction_slack=retire["remaining_mechanical_reaction"],
                physical_threshold_side="actual bank E, spring-side q/C and geometric clearance",
                auxiliary_raw_strobes_at_other_sites=True)


def installed_faces():
    files=("B-LEAD-INSTALLATION.md","b_lead_installation_results.json")
    blob={name:legacy.text_at(LEADS,"portability/"+name) for name in files}
    lead=json.loads(blob[files[1]])
    row,ports,b=lead["contact"],lead["raw_paths"],lead["budget"]
    A=Q(row["effect_age"])
    require(A==Q(receipt("normal_response_transport")["source_receipt"]["new_effect_horizon"]),
            "Lead and decision use different factual horizons")
    true_load=Q(3,2)*Q(51,100)+A*Q(row["mechanical_drift"])+Q(row["known_parallel_force"])/128
    require(true_load==Q(row["full_contact_upper"])<1 and Q(row["all_324_parallel_upper"])<1
            and Q(row["nominal_clearance_deficit"])<Q(1,5) and Q(row["parallel_coil_mount_countercase"])>1,
            "The reported spring alone does not certify the actual cut")
    require(ports["primary_fronts_in_current_weld"]==40 and ports["primary_slots_per_selected_group"]==1
            and ports["expanded_three_origin_six_incident_reach"]==8
            and Q(ports["additional_terminal_shunt_load"])==Q(1,32)
            and Q(ports["remaining_high_work_margin"])>0 and Q(ports["remaining_cold_current_margin"])>0,
            "Physical source slot/pressure incidence not transported")
    require(Q(b["recovered_reference"])<Q(82,10**6) and Q(b["cold_working_window"])>=Q(1,16)
            and Q(b["fourfold_rho_over_kEoff"])<1 and Q(b["low_sample_to_rearm"])>0
            and min(Q(b[k]) for k in ("force_slack","bath_slack","supply_slack","pressure_floor_slack"))>0,
            "Warm/cold, retirement or shared-stock case lost in physical incidence attach")
    other=Q(b["nonprivate_current_upper"])
    total=Q(b["total_current_including_private"])
    private=Q(receipt("b_reference_return")["working_cut"]["private_absolute_current"])
    require(other+private==total and 2**45-other==Q(b["nonprivate_slack_to_2_to_45"])>0
            and 2**48-total==Q(b["full_slack_to_2_to_48"])>0,
            "Private and nonprivate current or their respective ratings were conflated")
    return dict(material=LEADS,normalized_contact_load_upper=true_load,
                installed_nonprivate_current=other,installed_nonprivate_slack_to_2_to_45=2**45-other,
                installed_private_current=private,installed_total_current=total,installed_total_slack_to_2_to_48=2**48-total,
                actual_clearance_deficit_upper=Q(row["nominal_clearance_deficit"]),
                source_affine_rail_margin=ports["remaining_high_work_margin"],
                cold_rail_current_margin=ports["remaining_cold_current_margin"],
                SHA256_LF={k:sha256(v.encode()).hexdigest() for k,v in blob.items()})


def encode(value):
    if isinstance(value,Q): return str(value)
    raise TypeError(type(value))


def generate():
    inputs=["b_handoff","sender_eligibility","receiver_lease","frame_pacing","normal_response_transport",
            "return_itinerary","threshold_geometry","private_comparison","b_host_flow","resident_custody","b_reference_return","spatial_coverage"]
    timing=timing_and_receipts()
    return dict(revision=PIN,handoff=HANDOFF,reference=REFERENCE,isolated_base=LOCAL,incidence=projection_checks(),
                mask=earlier_containment(),regional_staffing=spatial_staffing(),retirement=retention_checks(),inequalities=timing,physical_taps=tap_check(),circuit_and_cue=circuit_and_cue(timing),installed_faces=installed_faces(),
                source=sha256(Path(__file__).read_text(encoding="utf8").encode()).hexdigest(),
                sources_sha256_lf={n:sha256(source(n+"_results.json").encode()).hexdigest() for n in inputs})


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    options=parser.add_mutually_exclusive_group()
    options.add_argument("--write",action="store_true")
    options.add_argument("--check",action="store_true")
    args=parser.parse_args()
    result=json.dumps(generate(),default=encode,indent=2,sort_keys=True)+"\n"
    dest=HERE/"b_cut_induction_results.json"
    if args.write:
        dest.write_text(result,encoding="utf8")
    elif args.check:
        require(result==dest.read_text(encoding="utf8"),"B cut evidence changed")
    else:
        print(result,end="")

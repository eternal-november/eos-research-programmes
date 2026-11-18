"""Matched qualified publication on the current B binary and physical stencil."""
import argparse
from collections import Counter
from fractions import Fraction as Q
from hashlib import sha256
import json
from pathlib import Path

import receiver_lease as lease

HERE=Path(__file__).resolve().parent
need=lease.need


def experiment(isa,c,m,origin,mode):
    Source,Selector=lease.recovery_classes(m)
    Parent,Bus=lease.priced_classes(m)
    common=json.loads((HERE/"b_lead_installation_results.json").read_text())["budget"]
    capU=Q(common["Ucap"])
    U=lease.SharedOrigin(origin,capU,capU)
    cap=int(Q(json.loads((HERE/"parent_realization_results.json").read_text())
              ["cost_bounds"]["actual_bank_capacity"]))
    E=lease.rx.charging.OperatingBank((origin,1),cap,Q(common['warm_keeper_energy']))
    s=Source(E,U,m.POPULATION);selector=Selector(s,mode)
    need(s.reform()=="formed-unpowered" and s.begin_entry(E)
         and s.entry_flow(Q(s.ENTRY_WORK,lease.raw.CLEAR_RATE)),"Source stencil or entry was not paid")
    cpu=Parent(isa,c,bank=E);bus=Bus(E,cpu,s)
    clock=lease.ObservedClock(s,bus)
    ports=m.ports_for(isa)(c,s,clock,selector)
    clock.advance(2*m.DELTA)
    first_stock=E.stock
    initial_cpu=cpu.bank.supplied
    # Both keys see the single installed rank-one head at this origin.
    # At the symmetric x=y=1/2 witness the nominal head reads 500 or 1000.
    observed=(500,1000)[m.incidence.head_type(origin)]
    for key in (0,1):
        m.convert(ports,key,observed)
        m.program.call(isa,c,ports,"publish_value",(key,),1000,cpu)
    at_offer=clock.now
    all_receipts=dict(Counter(t[2] for t in ports.receipts))
    count=s.publications
    clock.advance(Q(1,3))
    mask=m.installed_mask(m.POPULATION,origin)
    wanted=160 if mode==m.PASS else sum(a+b for a,b in mask)
    need(count==wanted and len(ports.receipts)==selector.inspected==160
         and selector.paid==160*m.PRICE and tuple(selector.words)==s.stencil,
         "Gate or stencil did not match this installation")
    need(all(accepted=="accepted" if tag=="forward" else
             accepted is None and tag=="source-suppressed" and not mask[i][k]
             for i,k,tag,accepted in ports.receipts),"Unaccounted silent or uninstalled issue")
    emitted=sum(b.sent for b in s.branches)
    need(emitted==4*count and not any(b.flights for b in s.branches) and s.flight_heat==512*count,
         "Lost paid parcel, source-bound branch or endpoint work")
    bus.full_audit()
    return dict(mode=mode,compared_io=all_receipts,actual_lookup_work=selector.paid,
                restored_bits=sum(a==b for a,b in zip(s.stencil,selector.words)),
                producer_retirements=cpu.retired,head=observed,physical_DATA=count,
                symbols=emitted,wire_work=s.flight_heat,source_processing=s.local_heat,
                all_branch_charge=bus.data_transferred,requested_source_uses=selector.inspected,
                bank_work_since_frame=first_stock-E.stock,parent_work_since_frame=cpu.bank.supplied-initial_cpu,
                after_offers=at_offer,end=clock.now,actual_payer=U.origin)


def report():
    isa,c,m=lease.compiled()
    old=json.loads((HERE/"matched_publication_results.json").read_text())
    changed=json.loads((HERE/"image_transport_results.json").read_text())
    need(c.image and m.program.hash_text(json.dumps(c.image))==changed["new_image"]
         and changed["old_image"]==old["image_sha256"],"Unrelated source points")
    arms=[experiment(isa,c,m,2,v) for v in (m.PASS,m.SELECT)]
    a,b=arms
    need(a["after_offers"]==b["after_offers"] and a["end"]==b["end"] and
         a["producer_retirements"]==b["producer_retirements"] and
         a["restored_bits"]==b["restored_bits"]==160 and
         a["actual_lookup_work"]==b["actual_lookup_work"] and
         a["parent_work_since_frame"]==b["parent_work_since_frame"],
         "Unmatched origin clock, capacities or physical code work")
    delta=a["physical_DATA"]-b["physical_DATA"]
    product_parents=a["producer_retirements"]*20480
    sentinel=a["parent_work_since_frame"]-product_parents
    need(product_parents==39690240 and sentinel==2*20480,"The two harness return boundaries are distinct from fanout retirements")
    need(delta>0 and a["symbols"]-b["symbols"]==4*delta and
         a["wire_work"]-b["wire_work"]==512*delta and
         a["bank_work_since_frame"]-b["bank_work_since_frame"]==4096*delta,
         "A later recharge, emitted packet or field work was omitted")
    pop=m.POPULATION
    full=2*80*pop
    selected=2*2*15*pop
    need(full==old["forward_DATA"] and selected==old["subscribed_DATA"],"Architecture-wide recipient degree changed")
    final=json.loads((HERE/"b_lead_installation_results.json").read_text())["budget"]
    working=json.loads((HERE/"frame_pacing_results.json").read_text())["certificate"]
    inventory=json.loads((HERE/"legacy_realization_results.json").read_text())["inventory"]
    duration=Q(working["qualified_boot_upper"])+1
    available=Q(final["warm_keeper_energy"])
    gross=Q(inventory["retained_downrated_bank_allowance"])
    # Before the first quantum conservatively ignore inlet flow. At the
    # functioning transit contact T'=2.05D-4.1T gives 4T>=1.5D after
    # one quantum even at T(0)=0. Later full-supply draws cannot lower E.
    init=json.loads((HERE/"threshold_initialization_results.json").read_text())["bootstrap"]
    need(3*gross/2>gross+2**44+Q(81,16) and duration<Q(init["first_nominal_keeper_loss_lower"]),
         "No stable first-period source contact")
    E_floor=available-(gross+2**44+Q(81,16))*min(1,duration)-2**52-max(a["bank_work_since_frame"],b["bank_work_since_frame"])
    Eoff=Q(lease.rx.gates.parameters(c)["EOFF"])
    drift=Q(2,10**7)*duration
    require_prices=(Q(final["Ucap"]),Q(final["pressure_floor_slack"]),Q(final["supply_slack"]),
                    Q(final["bath_slack"]),Q(final["force_slack"]),Q(final["nonprivate_slack_to_2_to_45"]),Q(final["full_slack_to_2_to_48"]))
    need(E_floor>Eoff and 2*drift<Q(1,2000) and min(require_prices)>0
         and Q(final["warm_pad_Q_at_r_zero"])==Q(1,2**20),
         "Cannot embed both nominal policies on the same closed-reference plant")
    return lease.rx.gates.normalize(dict(arms=arms,final_source_cap=final["Ucap"],
               source_E_lower_envelope=E_floor,positive_Eoff_margin=E_floor-Eoff,
               boot_plus_first_plant_window=duration,worst_sum_row_drift=2*drift,
               frame_timing=final["working_frame"],physical_image=changed["new_image"],same_local_time=a["end"],
               per_origin_example_delta=delta,actual_fanout_parents_work=product_parents,
               extra_harness_return_parcels=sentinel,tagged_DATA_work_includes_signal=True,
               equality_saves_no_parent_work=True,
               one_nominal_scan_one_source_bank_per_host=dict(forward=full,subscribed=selected,excess=full-selected),
               source_family_positive=False,full_program_reuse_assessed=False,
               inputs={f:sha256((HERE/f).read_bytes().replace(b"\r\n",b"\n")).hexdigest() for f in
                   ("REPEATED-PROOF-BURDEN.md","current_publication_comparison.py","receiver_lease.py","receiver_lease_results.json",
                    "b_handoff_results.json","b_lead_installation_results.json","frame_pacing_results.json","legacy_realization_results.json","threshold_initialization_results.json","matched_publication_results.json","world_channel_results.json",
                    "image_transport_results.json","regional_assembly_results.json")}))


if __name__=="__main__":
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument("--write",action="store_true");args=ap.parse_args()
    text=json.dumps(report(),sort_keys=True,indent=2)+"\n"
    output=HERE/"current_publication_comparison_results.json"
    if args.write:output.write_text(text,encoding="utf8",newline="\n")
    else:need(output.read_text(encoding="utf8")==text,"Different paired publication receipt")
    print("Verified same-plant B publisher executions, two finite physical ledgers and current image")

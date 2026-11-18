"""Verify geometric, time and physical lower bounds for same-history spatial coverage."""
import argparse
from dataclasses import dataclass
from fractions import Fraction as Q
from hashlib import sha256
from math import ceil
from pathlib import Path
import json
import spatial_history as spatial
import return_seat as seat_source

HERE=Path(__file__).resolve().parent
need=spatial.need


def color(region,n):
    r,col=region
    need(n>=3 and r in (0,1) and 0<=col<n,"Uninstalled protected region")
    return (r,col%min(5,n))


def ladder(n):
    neighborhoods=spatial.regions(n)
    colors={(r,k):set() for r in (0,1) for k in range(min(n,5))}
    for region in neighborhoods:
        colors[color(region,n)].add(region)
    for units in colors.values():
        need(len(units)*18>=2*n,"A witness stratum has vanishing geometric size")
        for mid in range(n):
            bag={(r,c) for r in (0,1) for c in range(max(0,mid-1),min(n,mid+2))}
            need(sum(bool(neighborhoods[z]&bag) for z in units)<=1,
                 "A local observation bag includes two direct exposure neighborhoods")
    need(set.union(*colors.values())==set(neighborhoods) and
         sum(map(len,colors.values()))==2*n,"The strata omitted or duplicated an installation")
    return len(colors),min(map(len,colors.values()))


@dataclass(frozen=True)
class Loss:
    # Proof observer's single-history identifier, not a field on the source wire.
    run: int
    unit: int
    start: Q
    duration: Q


def overlap(receipts,domain,bin_width,physical_prefix,physical_length):
    """Find an actual simultaneous interval from already observed onsets."""
    need(receipts and domain[0]<=domain[1] and bin_width>0
         and physical_length>bin_width,"Invalid observation horizon")
    bins=ceil((domain[1]-domain[0])/bin_width) or 1
    hist={}
    unit_set=set()
    run=receipts[0].run
    for r in receipts:
        need(r.run==run and r.unit not in unit_set and domain[0]<=r.start<=domain[1]
             and r.duration>=physical_prefix+physical_length,"Unmatched physical receipt")
        unit_set.add(r.unit)
        key=min(bins-1,int((r.start-domain[0])//bin_width))
        hist.setdefault(key,[]).append(r)
    bucket=max(hist.values(),key=len)
    left=max(row.start+physical_prefix for row in bucket)
    right=min(row.start+physical_prefix+physical_length for row in bucket)
    need(right-left>=physical_length-bin_width and len(bucket)>=ceil(Q(len(receipts),bins)),
         "The chosen observations have no guaranteed common interval")
    return len(bucket),left,right


def report():
    cases=[ladder(n) for n in range(3,101)]
    # Genuine current B timing bounds. During a selected local interval the
    # signed command application and the physical motion/age laws, not marks,
    # give a positive amount of actual removed service.
    record=lambda f:json.loads((HERE/f).read_text())
    world=record("world_channel_results.json")["source"]
    program=record("frame_pacing_results.json")["certificate"]
    seat=record("return_itinerary_results.json")["budget"]
    geometry=record("threshold_geometry_results.json")["arithmetic"]["physical_inputs"]
    q=Q(500)
    speed=Q(geometry["stroke_max"])
    isa=seat_source.program.load_isa()
    compiled,_=seat_source.candidate(isa)
    need(seat_source.program.hash_text(json.dumps(compiled.image))==record("frame_pacing_results.json")["image"],
         "Qualification and physical weighting are not from the same source image")
    blend=compiled.constants["BLEND_LIMIT"]
    weight=1-speed*q/blend
    worst=weight*Q(-1,2)+(1-weight)
    H=Q(seat["H"]);epochs=42*H;window=2*H
    half=Q(seat["sampled_fresh_half"])
    region_count_number=18
    buckets=ceil(window/140)
    need(Q(world["stable_replacement_bound"])<3
         and Q(world["held_minus_one_tracker_ceiling_after_200"])==Q(-1,2)
         and worst<Q(-47,100) and speed*1100<Q(geometry["power_at"]),
         "Continuing role, physical application or amplitude boundary failed")
    need(500>3*11*Q(program["qualified_frame_q"][1]) and
         3*half+1100<H and 40*H-1100>H+3*half,"No between-block recovery and same-side opportunity")
    rate=Q(seat["lambda_per_q"])
    need(3/(40*H)<=rate and int(3+2*H*rate)+3==6,"The unchanged local raw limits failed")
    # Two unequal and one endpoint-coincident old examples. The sample is a
    # small finite check on the interval extractor, not an admitted plant orbit.
    dates=[Q(0),Q(1,4),Q(7,4),Q(2)]
    trial=[Loss(0,i,v,8) for i,v in enumerate(dates)]
    num,left,right=overlap(trial,(Q(0),Q(2)),1,1,3)
    need(num==2 and right-left>=2,"Small witness changed")
    try:overlap([trial[0],Loss(1,4,Q(1,3),8)],(Q(0),Q(2)),1,1,3)
    except (ValueError,AssertionError):pass
    else:raise AssertionError("Different runs were spliced")
    return dict(checked_ladder_sizes=len(cases),minimum_fraction_any_nonempty_class="1/18",
                by_region_epoch_pairs_upper=10,service_effect_epochs_per_pair=1,
                joint_history_required=True,H=str(H),period=str(epochs),physical_effect_lower=140,
                maximum_time_bins=buckets,simultaneous_fraction=f"1/{region_count_number*buckets}",
                average_fresh_exposure_density=str(Q(3,20)/epochs),
                keeper_weight_floor=str(weight),adverse_weighted_host_output_upper=str(worst),
                served_body_roster_per_region=2*spatial.COHORT,
                source_capture_horizon=str(Q(world["stable_replacement_bound"])),
                positive_family_and_admitted_opportunity_required=True,
                sample_extraction=[num,str(left),str(right)],
                sources={f:sha256((HERE/f).read_bytes().replace(b"\r\n",b"\n")).hexdigest() for f in
                         ("SPATIAL-COVERAGE.md","spatial_coverage.py","spatial_history.py","threshold_incidence_model.py","return_seat.py",
                          "world_channel_results.json","return_itinerary_results.json","threshold_geometry_results.json",
                          "frame_pacing_results.json","regional_assembly_results.json")})


if __name__=="__main__":
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument("--write",action="store_true");args=ap.parse_args()
    output=json.dumps(report(),indent=2,sort_keys=True)+"\n"
    dest=HERE/"spatial_coverage_results.json"
    if args.write:dest.write_text(output,encoding="utf8",newline="\n")
    else:need(dest.read_text(encoding="utf8")==output,"Different coverage receipt")
    print("Verified rotating regional coverage, compatible raw accrual and simultaneous-output extraction")

"""Conditional exact publication/age join for the candidate physical ports."""
from fractions import Fraction as F
import argparse
import json
import sys
import threshold_program_model as p


def generate():
    isa=p.load_isa();c=p.compile_program(isa,p.production_design(isa));k=c.constants;b=p.bounds(isa,c)
    mu=2**26;fast=F(101,100);field_wait=F(1,64)
    fmin=F(k['FRAME_STEPS'],mu)/fast
    fmax=F(b['padded_frame_upper'],mu)+k['VECTOR_UPDATES']*field_wait
    p.need(b['active_frame_upper']<=k['FRAME_STEPS'],'Uncovered active work')
    p.need(fmax<2,'Source-cache fanout allocation no longer covers a full frame')
    maintenance=(F((k['RAW_MAINT_HEADS']+k['FAST_BATCH']-1)//k['FAST_BATCH'])+1)*fmax
    plant=2*fmax
    fold=(1+(max(k['CONNECTORS_A'],k['CONNECTORS_B'])-1+k['FAST_BATCH']-1)//k['FAST_BATCH'])*fmax
    sample=F(1);cache=F(2);data=F(2)
    # Periods bound successive COMPLETED per-client offers. Conversion and
    # fanout already lie inside F; only arrival spread and a reserve remain.
    gap_extra=data+1
    lives={'plant':8,'maintenance':512};periods={'plant':plant,'maintenance':maintenance}
    timing={}
    for name,e in lives.items():
        bits=e.bit_length();cap=(1<<bits)-1
        minimum=F(e-1)/fast
        required=periods[name]+gap_extra
        p.need(minimum>required,'Nominal receipt can expire before refresh: '+name)
        timing[name]=dict(nominal_ticks=e,counter_bits=bits,arbitrary_counter_cap=cap,
                         free_running_lifetime_min=str(minimum),required_gap=str(required),
                         gap_slack=str(minimum-required),singleton_age=str(sample+cache+data+e))
    short_min=F(256-1)/fast
    p.need(short_min<maintenance+gap_extra,'Expected short-lifetime failed inequality disappeared')
    boot=F(b['boot_padded_upper']+16,mu)
    instruction=F(1,mu)+field_wait
    boot_tail=instruction+F(1,64)+data
    p.need(F(k['BOOT_DRAIN_STEPS'],mu)/fast>boot_tail,'Boot drain omits actual pending suffix')
    entry=F(k['ENTRY_FRAMES']-1)*fmin
    plant_entry=F(k['PLANT_ENTRY_FRAMES']-1)*fmin
    p.need(entry>boot+timing['maintenance']['arbitrary_counter_cap']+4,'Maintenance initial I not drained')
    p.need(plant_entry>boot+timing['plant']['arbitrary_counter_cap']+4,'Plant initial I not drained')
    p.need(F(12*(k['CONVERSION_POLLS']-2),mu)/fast>F(1,64),'Nominal conversion can time out')
    per_target=(F((k['DEGREE']+k['MAINT_BATCH']-1)//k['MAINT_BATCH'])+1)*fmax
    compare=F(b['instruction_upper_bounds']['helper']+64,mu)+field_wait
    withdrawal=per_target+2*3+6+3
    pose_age=sample+cache+data+lives['maintenance']
    functional_age=pose_age+fold
    horizon=functional_age+compare+withdrawal
    # Preserve coefficient-jump and geometric-residual distinctions from
    # the stateful source; their enlarged field realization remains owed.
    load_multiplier=F(3,2);load_drift=F(1,10000)
    deficit_rate=F(11,400000);deficit_residual=F(1,10)
    load_needed=1-((1-load_drift*horizon)/load_multiplier-F(1,100))
    deficit_needed=F(1,100)+deficit_residual+deficit_rate*horizon
    force_upper=load_multiplier*(1-F(k['LOAD_MARGIN'],1000)+F(1,100))+load_drift*horizon
    deficit_upper=F(1,5)-F(k['ISOLATION_MARGIN'],1000)+F(1,100)+deficit_residual+deficit_rate*horizon
    p.need(force_upper<1 and deficit_upper<F(1,5),'Failed-mode continuation exceeds physical rule')
    p.need(F(k['LOAD_MARGIN'],1000)>=load_needed,'Functional load margin fails')
    p.need(F(k['ISOLATION_MARGIN'],1000)>=deficit_needed,'Functional clearance margin fails')
    p.need(F(1,8)+F(1,100)<=1-F(k['LOAD_MARGIN'],1000),'Working load does not permit action')
    p.need(2*F(1,100)<=F(1,5)-F(k['ISOLATION_MARGIN'],1000),'Working clearance does not permit action')
    post_min=(k['POST_STAGE_FRAMES']-1)*fmin
    # Keep the old18 allowance conservatively, even though private writer
    # hardware is removed. New field pulses have their own longer retirement.
    p.need(post_min>pose_age+18,'Post-stage contacts omit ordinary causal tail')
    world_age=sample+cache+data+lives['plant']+3*fmax+3+6+3
    row_beta=F(5,1000)+F(4,10**7)*world_age
    p.need(F(k['ROW_VERIFY_RADIUS'],1000)>=2*row_beta,'Row range availability fails')
    feedback=4*(row_beta+F(1,2000))+F(1,100)
    p.need(feedback<F(4,100),'No room remains within proposed tracker error budget')
    records=2+k['FAST_BATCH'];rate=F(records)/fmin
    tx_backlog=2*records+rate/256
    rx_backlog=264+F(1040,2048)
    p.need(tx_backlog<128 and rx_backlog<512,'Nominal/raw queue capacity fails')
    source_names=('publication_timing.py','THRESHOLD-PUBLICATION.md','threshold_program_model.py','threshold_program_source.py')
    return dict(scope='conditional source-local arithmetic; physical suppliers and joint realization remain open',
        frozen_base=p.BASE,frozen_isa_sha256=isa.source_hash,
        frozen_geometry_sha256=p.hash_text(p.frozen('geometry_results.json')),
        production_image_sha256=p.hash_text(json.dumps(c.image)),
        sources_sha256_lf={name:p.digest(p.HERE/name) for name in source_names},python_version=sys.version,
        primitive_assumptions=dict(instruction_min=mu,receipt_clock_min=1,clock_max=str(fast),field_nonretiring_wait=str(field_wait),
            sample_age_allowance=1,actual_conversion_max='1/64',cache_fanout=2,data_delivery=2,command_stable=3,ordinary_force_tail=6,
            retirement=3,TX_records_per_quantum=256,RX_symbols_per_quantum=2048,
            raw_RX_envelope='264+1040*t',raw_functional_error='1/100',load_multiplier=str(load_multiplier),
            load_drift=str(load_drift),deficit_slew=str(deficit_rate),deficit_total_residual=str(deficit_residual),raw_row_error='5/1000',row_slew_per_quantum='4/10000000'),
        frames=dict(min=str(fmin),max=str(fmax)),publication_periods=dict(plant=str(plant),maintenance=str(maintenance)),
        fold_oldest_span=str(fold),receipts=timing,
        failed_short_lifetime=dict(nominal_ticks=256,min=str(short_min),required=str(maintenance+gap_extra),
            shortage=str(maintenance+gap_extra-short_min),scope='failed selected sufficient gap certificate, not a loss trace'),
        initialization=dict(boot=str(boot),boot_pending_tail=str(boot_tail),maintenance_entry_min=str(entry),
            plant_entry_min=str(plant_entry),initial_unknown_records_have_no_sample_history=True),
        functional=dict(age=str(functional_age),helper_compare_to_emit=str(compare),per_target=str(per_target),
            withdrawal=str(withdrawal),full_horizon=str(horizon),load_margin_required=str(load_needed),
            deficit_margin_required=str(deficit_needed),force_upper=str(force_upper),deficit_upper=str(deficit_upper),
            nominal_full_clearance_observation_threshold_slack='0',post_stage_min=str(post_min)),
        world=dict(full_age=str(world_age),row_beta=str(row_beta),feedback_error=str(feedback),
            remaining_below_point04=str(F(4,100)-feedback),tracker_transient_not_supplied=True),
        traffic=dict(records_per_bank_branch_per_frame=records,full_bank_offers_per_frame=2*k['DEGREE']*records,
            TX_arrival_burst=2*records,TX_arrival_rate=str(rate),TX_backlog=str(tx_backlog),RX_backlog=str(rx_backlog)),
        unclosed=['physical field I/O wait','new origin/capture/decoder clock and power graph','actual primitive error/slew laws',
                  'all-emitter entry and interval cover','field pulse freshness/retirement','tracker dynamics and world barriers',
                  'work/heat/stock and all-history source composition'],program_completion=False)


def main():
    parser=argparse.ArgumentParser(description=__doc__);g=parser.add_mutually_exclusive_group(required=True)
    g.add_argument('--write',action='store_true');g.add_argument('--check',action='store_true');args=parser.parse_args()
    result=generate();path=p.HERE/'publication_timing_results.json'
    if args.write:path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n',encoding='utf-8',newline='\n')
    else:p.need(json.loads(path.read_text(encoding='utf-8'))==result,'Publication timing record differs')
    print('PASS conditional publication timing; physical/recurrent source remains open')


if __name__=='__main__':main()

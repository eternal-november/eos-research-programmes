"""Exact finite-pool field certificates and source-local countercases.

The constructor supplies a cyclic plan and inequalities, not physical delivery,
reserved work, field realization or a full-source winning certificate.
"""
from __future__ import annotations
import argparse
from dataclasses import dataclass
from fractions import Fraction as Q
from hashlib import sha256
import json
from pathlib import Path
from constructors import CertificateFailure, exact, natural, require

HERE=Path(__file__).resolve().parent


@dataclass(frozen=True)
class PulseDesign:
    sample_edges: int
    pulse_edges: int
    clock_min: Q
    clock_max: Q
    delivery: Q
    settle: Q
    withdrawal: Q
    disposal: Q
    refill: Q
    max_slots: int
    capsule_energy: Q
    setup_work: Q
    edge_work: Q
    driver_power: Q
    parent_tail: Q
    operation_floor: Q


def construct(d: PulseDesign):
    ns=natural(d.sample_edges,'Sampler edge count',positive=True)
    np=natural(d.pulse_edges,'Pulse edge count',positive=True)
    cap=natural(d.max_slots,'Installed slot capacity',positive=True)
    names=('clock_min','clock_max','delivery','settle','withdrawal','disposal','refill',
           'capsule_energy','setup_work','edge_work','driver_power','parent_tail','operation_floor')
    v={name:exact(getattr(d,name),name) for name in names}
    require(v['clock_min']>0 and v['clock_max']>=v['clock_min'],'Invalid nominal clock interval')
    require(all(v[name]>=0 for name in names if name not in ('clock_min','clock_max')),'Negative pulse bound')
    smin=Q(ns-1)/v['clock_max'];smax=Q(ns)/v['clock_min']
    dmin=Q(np-1)/v['clock_max'];dmax=Q(np)/v['clock_min']
    require(smin>0,'No positive sampler-spacing certificate')
    overlap=dmin-smax-v['delivery']
    require(overlap>0,'No strict continuous-pulse overlap')
    lifetime=v['delivery']+dmax+v['withdrawal']+v['disposal']+v['refill']
    ratio=lifetime/smin
    pool=ratio.numerator//ratio.denominator+1
    require(pool<=cap,'Insufficient installed slots for strict complete-lifetime reuse')
    work=v['setup_work']+np*v['edge_work']+v['driver_power']*(v['delivery']+dmax+v['withdrawal'])
    require(work+v['operation_floor']<v['capsule_energy'],'No strictly funded complete pulse profile above operation floor')
    # Old active wrong slots can retain selector priority until their expiry.
    freshness=max(smax+v['delivery'],v['delivery']+dmax)+v['settle']
    retirement=v['parent_tail']+v['delivery']+dmax+v['withdrawal']
    return dict(pool_size=pool,cyclic_plan=list(range(pool)),sample_min=smin,sample_max=smax,
                pulse_min=dmin,pulse_max=dmax,overlap=overlap,slot_lifetime=lifetime,
                reuse_slack=pool*smin-lifetime,profile_work=work,
                energy_margin=v['capsule_energy']-work-v['operation_floor'],
                total_residue_bound=v['capsule_energy']-work,operation_floor=v['operation_floor'],
                stable_setting_to_field=freshness,cutoff_to_zero=retirement,
                inhibited_initial_pool_drain_refill=v['parent_tail']+lifetime)


def sample_run(pool, spacing, pulse_duration, withdrawal, disposal, refill, count):
    """One admitted constant-clock local run, not a source/controller simulator."""
    free=[Q(0)]*pool;active=[];rejected=[];accepted=[]
    for k in range(count):
        t=k*spacing;slot=k%pool
        if free[slot]>t:
            rejected.append((k,t,slot))
        else:
            end=t+pulse_duration
            active.append((t,end,slot,1))
            free[slot]=end+withdrawal+disposal+refill
            accepted.append((k,t,slot))
    return accepted,rejected,active


def selected(intervals, time):
    active=[row for row in intervals if row[0]<=time<row[1]]
    return min(active,key=lambda row:row[2])[3] if active else 0


def check_failure(call, label):
    try:call()
    except CertificateFailure as e:return str(e)
    raise AssertionError('Invalid pulse design accepted: '+label)


def base_design():
    return PulseDesign(2**20,2**21,Q(1),Q(101,100),Q(1),Q(1000),Q(1000),Q(1),
                       Q(100000),3,Q(2**26),Q(2**16),Q(16),Q(8),Q(1,64),Q(1))


def generate():
    from dataclasses import replace
    d=base_design();c=construct(d)
    require(c['pool_size']==3 and c['slot_lifetime']==2198154,'Candidate pool point changed')
    require(c['inhibited_initial_pool_drain_refill']==d.parent_tail+c['slot_lifetime'],'Initial drain omitted upstream parent tails')
    require(c['profile_work']==50405192 and c['energy_margin']==16703671 and c['total_residue_bound']==16703672,'Full profile work changed')
    actual_spacing=Q(d.sample_edges)/d.clock_max
    a2,r2,v2=sample_run(2,actual_spacing,c['pulse_max'],d.withdrawal,d.disposal,d.refill,8)
    a3,r3,v3=sample_run(3,actual_spacing,c['pulse_max'],d.withdrawal,d.disposal,d.refill,20)
    require([x[0] for x in r2[:2]]==[2,3] and not r3,'Cyclic occupancy witness changed')
    gap_start=actual_spacing+c['pulse_max']+d.withdrawal
    gap_end=4*actual_spacing
    require(gap_end-gap_start==Q(102659448,101)>0,'Two-slot zero-field gap changed')
    require(selected(v2,(gap_start+gap_end)/2)==0,'Two-slot gap not in the actual active set')
    # An initially wrong slot0 can dominate a fresh correct slot1.
    wrong=[(Q(-1),c['pulse_max']-1,0,-1),
           (actual_spacing,actual_spacing+c['pulse_max'],1,1)]
    test=actual_spacing+2*d.delivery+d.settle
    require(test<c['pulse_max']-1 and selected(wrong,test)==-1,'Old-priority freshness obstruction missing')
    # An old expiration may not zero a currently selected newer pulse.
    correct=[(Q(0),c['pulse_max'],0,1),
             (actual_spacing,actual_spacing+c['pulse_max'],1,1)]
    require(selected(correct,c['pulse_max'])==1,'Active-set expiry erased a newer pulse')
    naive_expiry_output=0
    require(naive_expiry_output!=selected(correct,c['pulse_max']),'Unconditional-zero countercase missing')
    # CPU-only cutoff leaves an independently powered sampler renewing bad fields.
    replay=[(a,b,s,-1) for a,b,s,_ in v3]
    witness_time=10*actual_spacing+Q(1)
    require(witness_time>c['cutoff_to_zero'] and selected(replay,witness_time)==-1,
            'Uncut-sampler retirement obstruction missing')
    bad=[check_failure(lambda:construct(replace(d,max_slots=2)),'two slots'),
         check_failure(lambda:construct(replace(d,clock_min=1.0)),'floating clock'),
         check_failure(lambda:construct(replace(d,sample_edges=True)),'Boolean edges'),
         check_failure(lambda:construct(replace(d,capsule_energy=Q(1024))),'unfunded profile'),
         check_failure(lambda:construct(replace(d,pulse_edges=2**19)),'no overlap'),
         check_failure(lambda:construct(replace(d,operation_floor=Q(20000000))),'unfunded nominal floor')]
    # A family of boundary parameter checks with explicit constructive outputs.
    cases=0
    for ns in (16,32,64):
        for np in (2*ns,3*ns,4*ns):
            for delay in (Q(0),Q(1,2),Q(1)):
                e=replace(d,sample_edges=ns,pulse_edges=np,delivery=delay,withdrawal=Q(1),
                          disposal=Q(1),refill=Q(3),settle=Q(1),max_slots=10)
                cert=construct(e)
                require(cert['pool_size']*cert['sample_min']>cert['slot_lifetime'],'Bad constructive pool')
                require((cert['pool_size']-1)*cert['sample_min']<=cert['slot_lifetime'],'Pool not minimal for this bound')
                require(cert['overlap']>0 and cert['profile_work']<e.capsule_energy,'Bad time/work certificate')
                cases+=1
    L=8192*192;channels=4*40*L;Em=Q(4096);Tr=Q(100000)
    capacity=3*channels*(d.capsule_energy+Em)
    # These are declared installed charger caps, not inferred from refill deadlines.
    charger_cap=2*capacity/Tr
    sampler_slope=16*d.clock_max*channels;sampler_burst=16*channels
    require(capacity==50668588184371200,'Capsule placement count changed')
    return dict(scope='cyclic local pulse construction and countercases; physical suppliers and full source remain open',
                point=c,clock_extreme_trace=dict(actual_spacing=actual_spacing,
                    two_slot_rejected_attempts=[k for k,t,s in r2],zero_field_gap=gap_end-gap_start,
                    three_slot_accepted=len(a3)),
                countercases=dict(old_priority_still_wrong_at=test,unconditional_expiry_zero_is_wrong=True,
                    uncut_sampler_old_force_at=witness_time),
                inventory=dict(image_bits=L,outgoing_channels=channels,slots=3*channels,
                    capsule_energy_capacity=capacity,installed_continuous_charger_cap=charger_cap,
                    charger_cap_is_a_primitive_input=True,nominal_refill_is_a_separate_obligation=True,
                    sampler_demand_slope=sampler_slope,sampler_demand_burst=sampler_burst),
                rejections=bad,boundary_parameter_cases=cases,
                sources_sha256_lf={name:sha256((HERE/name).read_bytes().replace(b'\r\n',b'\n')).hexdigest()
                                  for name in ('pulse_model.py','PULSE-FIELDS.md','constructors.py')},
                program_completion=False,physical_source_realized=False)


def serial(x):
    if isinstance(x,Q):return str(x)
    if isinstance(x,dict):return {str(k):serial(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)):return [serial(v) for v in x]
    return x


def main():
    p=argparse.ArgumentParser(description=__doc__);g=p.add_mutually_exclusive_group(required=True)
    g.add_argument('--write',action='store_true');g.add_argument('--check',action='store_true');a=p.parse_args()
    result=serial(generate());path=HERE/'pulse_results.json'
    if a.write:path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n',encoding='utf-8',newline='\n')
    else:require(json.loads(path.read_text(encoding='utf-8'))==result,'Pulse evidence binding differs')
    print('PASS local pulse certificates; full-source realization remains open')


if __name__=='__main__':main()

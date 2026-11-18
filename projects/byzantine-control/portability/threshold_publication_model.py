"""Execute actual producer publications through fixed physical incidence.

Finite instruction/data-path checks; fixture ticks and immediate records do
not certify physical timing, energy, fresh acquisition or recurrent service.
"""
from __future__ import annotations
import argparse
from dataclasses import dataclass, replace
import json
import sys
import threshold_program_model as program
import threshold_incidence_model as incidence

HERE=program.HERE
need=program.need


@dataclass(frozen=True)
class Receipt:
    provider: int
    provider_bank: int
    receiver: int
    receiver_bank: int
    source_key: int
    slot: int
    destination_key: int
    value: int


def route(c,population,provider,provider_bank,client,key,value):
    """Captured physical endpoint selects origin; payload truth is unchecked."""
    incidence.check_population(population)
    k=c.constants
    need(k['DEGREE']==len(incidence.OFFSETS) and k['ORIGINS']==15
         and k['FAST_KEYS']==3+k['DEGREE']*k['FAST_TARGET_KEYS'],
         'Compiled design is outside the fixed incidence interface')
    if not (type(provider) is int and 0<=provider<population
            and type(provider_bank) is int and provider_bank in (0,1)
            and type(client) is int and 0<=client<2*k['DEGREE']
            and type(key) is int and 0<=key<k['FAST_KEYS']
            and type(value) is int and 0<=value<(1<<256)):
        return None
    ordinal,receiver_bank=divmod(client,2)
    receiver=incidence.neighbors(population,provider)[ordinal]
    if key in (0,1):
        group=incidence.plant_group(population,receiver,key)
        destination_key=key
    elif key==2:
        return None
    else:
        source_ordinal,relative=divmod(key-3,k['FAST_TARGET_KEYS'])
        target=incidence.neighbors(population,provider)[source_ordinal]
        targets=incidence.neighbors(population,receiver)
        if target not in targets:
            return None
        receiver_ordinal=targets.index(target)
        actual,pairs=incidence.maintenance_group(population,receiver,receiver_ordinal)
        need(actual==target,'Target transport changed object')
        group=tuple(j for j,_ in pairs)
        destination_key=3+receiver_ordinal*k['FAST_TARGET_KEYS']+relative
    if provider not in group:
        return None
    return Receipt(provider,provider_bank,receiver,receiver_bank,key,
                   group.index(provider),destination_key,value)


def deliveries(c,population,provider,bank,ports,receiver,receiver_bank):
    # Complete the fixture's final funded send; not a physical delay proof.
    ports.elapse(2)
    result=[]
    actual_client=2*incidence.neighbors(population,provider).index(receiver)+receiver_bank
    for _,kind,args,value in ports.delivered:
        if kind!='source_offer_fast' or args[0]!=actual_client:
            continue
        r=route(c,population,provider,bank,*args,value)
        if r is not None and (r.receiver,r.receiver_bank)==(receiver,receiver_bank):
            result.append(r)
    return result


def install(ports,receipts):
    for r in receipts:
        ports.fast[(r.slot,r.provider_bank,r.destination_key)]=r.value


def plant_receipts(isa,c,b,Ports,population,receiver,receiver_bank,x,total,
                   changed=None,missing=()):
    changed=changed or {}
    producers=set(incidence.plant_group(population,receiver,0))|set(incidence.plant_group(population,receiver,1))
    receipts=[];steps=0;emitted=0
    for provider in sorted(producers):
        value=changed.get(provider,(x,total)[incidence.head_type(provider)])
        for bank in (0,1):
            if provider in missing:
                continue
            p=Ports(c)
            p.fast[('head',0)]=value;p.fast[('head',1)]=value
            m=program.call(isa,c,p,'publish_plant',(),b['instruction_upper_bounds']['publish_plant']+10)
            need(p.samples==2 and p.offers==4*c.constants['DEGREE'] and p.dropped_offers==0,
                 'Plant producer did not execute both full fanouts')
            need(all(e[2]==value for e in p.publications),'Rank-one publication differs')
            receipts.extend(deliveries(c,population,provider,bank,p,receiver,receiver_bank))
            steps+=m.steps;emitted+=len(p.publications)
    return receipts,dict(actual_producers=len(producers)-len(set(missing)&producers),
                         producer_instructions=steps,accepted_offers=emitted,
                         mapped_receipts=len(receipts))


def consume_world(isa,c,b,Ports,receipts,x,total,receiver):
    p=Ports(c);install(p,receipts)
    local=(x,total)[incidence.head_type(receiver)]
    p.fast[('head',0)]=local;p.fast[('head',1)]=local
    m=program.initialized(isa,c);m.W[c.constants['ENTRY']]=1;m.enter('frame')
    while not m.io_counts['world'] and m.steps<b['active_frame_upper']:
        need(m.step(p),'Production prefix stopped before WORLD')
    need(m.io_counts['world']==1 and m.C==c.image,'Consumer failed or changed code')
    return p.world_latch,m.steps


def estimate(isa,c,b,Ports,receipts,key,maximum):
    p=Ports(c);install(p,receipts)
    m=program.call(isa,c,p,'estimate',(key,maximum),b['instruction_upper_bounds']['estimate']+10)
    return m.result(),m.W[c.constants['EST_VALID']],m.steps


def plant_checks(isa,c,b,Ports):
    huge=12*(6+2**98)+2;reports=[]
    cases=((82,0,0,450,1050),(86,85,1,550,1050),(huge,huge-1,0,450,1050))
    for population,receiver,bank,x,total in cases:
        receipts,counts=plant_receipts(isa,c,b,Ports,population,receiver,bank,x,total)
        need(len(receipts)==60,'Two rows times fifteen providers times two banks not routed')
        observed,steps=consume_world(isa,c,b,Ports,receipts,x,total,receiver)
        expected=(60+(2*(x-500))//10,60+(2*(total-x-500))//10)
        need(observed==expected,'Receiver did not consume actual rank-one publications')
        for row,value in ((0,x),(1,total)):
            result,valid,_=estimate(isa,c,b,Ports,receipts,row,2000)
            need((result,valid)==(value,1),'Transported plant estimate differs')
        reports.append(dict(population=str(population),receiver=str(receiver),receiver_bank=bank,
                            rows=[x,total],world=list(observed),consumer_prefix_instructions=steps,**counts))
    population=86;receiver=0;providers=incidence.plant_group(population,receiver,1)
    checks=[]
    for count in (7,8):
        receipts,counts=plant_receipts(isa,c,b,Ports,population,receiver,0,450,1050,missing=providers[:count])
        observed,_=consume_world(isa,c,b,Ports,receipts,450,1050,receiver)
        expected=(50,80) if count==7 else (60,60)
        need(observed==expected,'Missing-provider availability boundary changed')
        checks.append(dict(missing_physical_providers=count,world=list(observed),**counts))
    # Six physical tokens reach seven slots. The paired input mutation does
    # not change receiver private state; the five sources execute publication.
    pair=incidence.input_slots(population,'paired_island',receiver,(providers[1],providers[2]),receiver,providers)
    direct=providers[3:8]
    supports=[incidence.input_slots(population,'digital',j,(),receiver,providers) for j in direct]
    support=set(pair).union(*supports)
    need(len(support)==7,'Six-token paired support differs')
    receipts,_=plant_receipts(isa,c,b,Ports,population,receiver,0,450,1050,
                              changed={j:500 for j in direct})
    paired=[replace(r,value=500) if r.destination_key==1 and r.slot in pair else r for r in receipts]
    observed,_=consume_world(isa,c,b,Ports,paired,450,1050,receiver)
    need(observed==(50,80),'Seven affected slots defeated this constant-row case')
    beyond=[replace(r,value=500) if r.destination_key==1 and r.slot==0 else r for r in paired]
    changed,_=consume_world(isa,c,b,Ports,beyond,450,1050,receiver)
    need(changed==(50,30),'Eight-slot threshold boundary did not change command')
    nominal=plant_receipts(isa,c,b,Ports,population,receiver,0,450,1050)[0]
    one_bank=[replace(r,value=500) if r.destination_key==1 and r.provider_bank==1 and r.slot<7 else r for r in nominal]
    need(consume_world(isa,c,b,Ports,one_bank,450,1050,receiver)[0]==(50,80),'Banks counted independently')
    return dict(positive=reports,availability=checks,paired_plus_five=dict(
        physical_tokens=6,affected_slots=sorted(support),world=list(observed),
        eighth_slot_boundary_world=list(changed),
        boundary_scope='finite group/code countercase; not an admitted hybrid history or universal impossibility'),
        two_banks_count_once=True)


def maintenance_checks(isa,c,b,Ports):
    population=86;receiver=0;k=c.constants;reports=[]
    for target_ordinal in (0,19,20,39):
        target,pairs=incidence.maintenance_group(population,receiver,target_ordinal)
        receipts=[];steps=0;wrong_target_records=0
        for provider,source_ordinal in pairs:
            need(source_ordinal!=target_ordinal,'Witness no longer distinguishes local ordinals')
            for bank in (0,1):
                p=Ports(c);m=program.initialized(isa,c)
                for j,actual_target in enumerate(incidence.neighbors(population,provider)):
                    for relative in range(k['VIEW_WORDS']):
                        raw=100000+actual_target*8+relative if relative<k['POSE_WORDS'] else 0
                        if relative==k['MODE']:raw=2
                        p.fast[('head',3+j*k['FAST_TARGET_KEYS']+relative)]=raw
                m.W[k['FAST_CURSOR']]=source_ordinal*k['RAW_TARGET_HEADS']+k['CAM']
                m=program.call(isa,c,p,'publish_fast',(),b['instruction_upper_bounds']['publish_fast']+10,m)
                receipts.extend(deliveries(c,population,provider,bank,p,receiver,1));steps+=m.steps
                client=2*incidence.neighbors(population,provider).index(receiver)+1
                wrong_key=3+target_ordinal*k['FAST_TARGET_KEYS']+k['CAM']
                r=route(c,population,provider,bank,client,wrong_key,17)
                need(r is None or r.destination_key!=3+target_ordinal*k['FAST_TARGET_KEYS']+k['CAM'],
                     'Equal-ordinal shortcut rebound another target')
                wrong_target_records+=1
        key=3+target_ordinal*k['FAST_TARGET_KEYS']+k['CAM']
        result,valid,count=estimate(isa,c,b,Ports,receipts,key,k['POSE_MAX'])
        expected=100000+target*8
        need((result,valid)==(expected,1),'Maintenance producer target not consumed')
        reports.append(dict(target=target,receiver_ordinal=target_ordinal,
                            provider_ordinals=[local for _,local in pairs],cam=result,
                            producer_instructions=steps,consumer_instructions=count,
                            rejected_equal_ordinal_rebindings=wrong_target_records))
    target_ordinal=0;target,pairs=incidence.maintenance_group(population,receiver,target_ordinal)
    receipts=[];fold_steps=0
    for provider,local in pairs:
        for bank in (0,1):
            p=Ports(c);m=program.initialized(isa,c)
            for side,count in ((0,k['CONNECTORS_A']),(1,k['CONNECTORS_B'])):
                for member in range(count):
                    p.functional[(local,side,member,0)]=k['SENSE_BIAS']+125
                    p.functional[(local,side,member,1)]=k['SENSE_BIAS']+1000
            m.W[k['FAST_CURSOR']]=local*k['RAW_TARGET_HEADS']+k['VIEW_WORDS']
            members=2*(k['CONNECTORS_A']+k['CONNECTORS_B'])
            for _ in range((members+k['FAST_BATCH']-1)//k['FAST_BATCH']):
                before=m.steps
                m=program.call(isa,c,p,'publish_fast',(),b['instruction_upper_bounds']['publish_fast']+10,m)
                fold_steps+=m.steps-before
            receipts.extend(deliveries(c,population,provider,bank,p,receiver,0))
    p=Ports(c);install(p,receipts)
    base=k['TARGET_BASE']+target_ordinal*k['TARGET_WORDS']
    guards=[]
    for side in (0,1):
        m=program.call(isa,c,p,'permission',(base,side),b['instruction_upper_bounds']['permission']+10)
        guards.append(m.result())
    need(guards==[1,1],'Actual functional folds did not supply both guards')
    key=3+target_ordinal*k['FAST_TARGET_KEYS']+k['VIEW_WORDS']
    need(all(p.fast[(origin,bank,key+side)]==125 and p.fast[(origin,bank,key+2+side)]==0
             for origin in range(15) for bank in (0,1) for side in (0,1)),'Functional fold value/route mismatch')
    return dict(targets=reports,functional_fold=dict(actual_target=target,guards=guards,
        source_maxima=[125,125,0,0],producer_instructions=fold_steps,
        scope='constant raw connector fixture; physical load/clearance laws not inferred'))


def address_checks(c):
    checks=0
    for index,bad in ((0,-1),(0,86),(0,True),(1,2),(1,False),(2,-1),(2,80),(2,0.0),
                      (3,-1),(3,c.constants['FAST_KEYS']),(3,False),(4,-1),(4,1<<256),(4,0.0)):
        args=[1,0,0,0,450];args[index]=bad
        need(route(c,86,*args) is None,'Malformed wire address accepted');checks+=1
    need(route(c,86,1,0,0,2,450) is None,'Uninstalled row accepted')
    from types import SimpleNamespace
    incompatible=SimpleNamespace(constants={**c.constants,'DEGREE':41})
    try:
        route(incompatible,86,0,0,80,0,450)
    except AssertionError:
        pass
    else:
        raise AssertionError('Incompatible incidence degree was not rejected')
    return dict(malformed_rejections=checks,incompatible_design_rejected=True,uninstalled_row_rejected=True,
                payload_truth_not_checked=True,physical_origin_not_taken_from_header=True)


def generate():
    isa=program.load_isa();c=program.compile_program(isa,program.production_design(isa));b=program.bounds(isa,c)
    Ports=program.ports_class(isa)
    print('executing rank-one producers and actual production consumers',flush=True)
    plant=plant_checks(isa,c,b,Ports)
    print('executing actual-target maintenance publication and functional folds',flush=True)
    maintenance=maintenance_checks(isa,c,b,Ports)
    sources=('threshold_publication_model.py','THRESHOLD-PUBLICATION.md','threshold_program_model.py',
             'threshold_program_source.py','threshold_incidence_model.py','constructors.py')
    return dict(scope='finite ordinary-instruction and fixed-address data-path bridge; not full source admission',
                frozen_base=program.BASE,frozen_isa_sha256=isa.source_hash,
                frozen_geometry_sha256=program.hash_text(program.frozen('geometry_results.json')),
                production_image_sha256=program.hash_text(json.dumps(c.image)),
                sources_sha256_lf={f:program.digest(HERE/f) for f in sources},python_version=sys.version,
                plant=plant,maintenance=maintenance,addresses=address_checks(c),
                omissions=['physical conversion/delivery/error/age proof','source and receiver power/work accounting',
                           'joint hybrid realizability of fault countercases','recurrent common-action service',
                           'complete fresh publication cycle from arbitrary cursor','production pacing after first WORLD'],
                program_completion=False,source_admission=False)


def main():
    p=argparse.ArgumentParser(description=__doc__);g=p.add_mutually_exclusive_group(required=True)
    g.add_argument('--write',action='store_true');g.add_argument('--check',action='store_true');a=p.parse_args()
    result=json.loads(json.dumps(generate()));path=HERE/'threshold_publication_results.json'
    if a.write:path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n',encoding='utf-8',newline='\n')
    else:need(json.loads(path.read_text(encoding='utf-8'))==result,'Publication bridge record differs')
    print('PASS actual rank-one publication/data-path bridge; timed physical source remains open')


if __name__=='__main__':main()

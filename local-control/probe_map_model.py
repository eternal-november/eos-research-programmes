"""Raw functional head, process-connection graph and existing-program adapter checks.

Sample times and fault locations below are analyst trace data, never actor inputs.
"""
from __future__ import annotations
import argparse
from collections import defaultdict, deque
from dataclasses import dataclass
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations
import json
import math
from pathlib import Path
import sys
import incidence_model as incidence

HERE=Path(__file__).resolve().parent
BIAS=32
ERROR=10
ADC_MAX=4095
WORD_MASK=(1 << 256)-1
S=F(1,64)


def require(ok,message):
    if not ok:
        raise AssertionError(message)


def digest(path):
    return sha256(path.read_text(encoding='utf-8-sig').replace('\r\n','\n').encode()).hexdigest()


def nearest(q):
    return math.floor(q+F(1,2))


def raw_for(q,integer_error=0):
    require(q>=0,'Negative physical quantity is outside this unipolar port')
    n=nearest(1000*q)+integer_error
    require(abs(n-1000*q)<=ERROR,'Nominal ADC error exceeded its actual bound')
    return max(0,min(ADC_MAX,BIAS+n))


def possible_codes(q,error=ERROR,bias=BIAS,maximum=ADC_MAX):
    for n in range(math.ceil(1000*q-error),math.floor(1000*q+error)+1):
        yield n,max(0,min(maximum,bias+n))


def decode(raw,kind):
    cap=3000 if kind==0 else 1000
    if not BIAS-ERROR<=raw<=BIAS+cap+ERROR:
        return None
    value=max(0,min(cap,raw-BIAS))
    return value if kind==0 else 1000-value


def fold(words,kind):
    values=[decode(raw,kind) for raw in words]
    return None if any(value is None for value in values) else max(values)


def vote_count(records,threshold):
    return sum(any(v is not None and v<=threshold for v in pair) for pair in records)


@dataclass(frozen=True)
class Head:
    origin:int
    bank:int
    target:int
    side:int
    conduit:int
    kind:int

    @property
    def endpoint(self):
        return self.target,self.side,self.conduit,self.kind


def capture(head,world,start,binding=None,raw_override=None,prepaid=4096,delay=S):
    if prepaid<4096:
        return dict(payload=None,sample=None,completion=None,charged_energy=0,started=False)
    require(S/2<=delay<=S,'Raw conversion time outside declared physical law')
    actual=head.endpoint if binding is None else binding
    sampled=start+delay/2
    completed=start+delay
    quantity=world[actual](sampled) if callable(world[actual]) else world[actual]
    raw=raw_for(quantity) if raw_override is None else raw_override
    require(0<=raw<=WORD_MASK,'Raw word exceeded finite I width')
    return dict(payload=raw,sample=sampled,completion=completed,endpoint=actual,charged_energy=4096,remaining_prepaid=prepaid-4096,started=True)


class GroupGraph:
    """Functional error-propagation graph; world-value changes are a different type."""
    def __init__(self,receiver=0,target=1,n=432,contacts=11):
        self.receiver,self.target,self.n,self.contacts=receiver,target,n,contacts
        self.origins,_=incidence.groups(receiver,target,n)
        self.edges=defaultdict(set)
        self.heads=[]
        self.records={}
        for slot,origin in enumerate(self.origins):
            for bank in (0,1):
                adc=('adc',origin,bank)
                calibration=('calibration',origin,bank)
                record=('functional_record',origin,bank)
                self.records[record]=slot
                self.edges[adc].add(calibration)
                self.edges[calibration].add(record)
                for side in (0,1):
                    for conduit in range(contacts):
                        for kind in (0,1):
                            h=Head(origin,bank,target,side,conduit,kind)
                            self.heads.append(h)
                            self.edges[('coupling',h)].add(('head',h))
                            self.edges[('head',h)].add(adc)
        frontend=('frontend',receiver)
        self.edges[frontend].update(('functional_record',self.origins[0],bank) for bank in (0,1))
        # Status fanout is explicit and does not feed a functional raw head.
        for slot,origin in enumerate(self.origins):
            self.edges[('target_status',target)].add(('status_record',origin,slot))

    def closure(self,starts):
        seen=set(starts)
        pending=deque(starts)
        while pending:
            node=pending.popleft()
            for child in self.edges.get(node,()):
                if child not in seen:
                    seen.add(child);pending.append(child)
        return seen

    def functional_slots(self,starts):
        return {self.records[node] for node in self.closure(starts) if node in self.records}

    def status_slots(self,starts):
        return {node[2] for node in self.closure(starts) if node[0]=='status_record'}

    def body_support(self,domains):
        starts=[]
        for origin in self.origins:
            if origin in domains:
                starts.extend(('calibration',origin,bank) for bank in (0,1))
        if self.receiver in domains:
            starts.append(('frontend',self.receiver))
        return self.functional_slots(starts)


def quantized_checks():
    load_cases=iso_cases=plant_cases=0
    for i in range(0,12001,5):
        q=F(i,2000)
        for n,raw in possible_codes(q):
            decoded=decode(raw,0)
            if decoded is not None and decoded<3000:
                require(1000*q<=decoded+10,'A low accepted raw load underestimated its actual object')
            if q<=3:
                require(decoded is not None and abs(decoded-1000*q)<=10,'In-range functional error was not preserved')
            if q>=F(6,5):
                require(decoded is None or decoded>700,'Unsafe load became a passing low value')
            load_cases+=1
    for i in range(2001):
        q=F(i,2000)
        for _,raw in possible_codes(q):
            decoded=decode(raw,1)
            require(decoded is not None and abs(decoded-1000*(1-q))<=10,'Isolation reversal/clipping lost its physical error')
            iso_cases+=1
    for i in range(4001):
        q=F(i,2000)
        for n,raw in possible_codes(q,error=5,bias=0,maximum=2000):
            require(abs(raw-1000*q)<=5,'Plant saturation lost its separate five-unit error')
            plant_cases+=1
    pairs=0
    for _,load in possible_codes(F(0)):
        for _,iso in possible_codes(F(1)):
            require(decode(load,0)<=700 and decode(iso,1)<=20,'Safest-state noise caused permanent abstention')
            pairs+=1
    for raw in range(11):
        require(decode(raw,0) is None and decode(raw,1) is None,'Settled electrical open became a numeric permission')
    require(raw_for(F(100))==ADC_MAX and decode(ADC_MAX,0) is None,'Overload saturation did not fail the ordinary range check')
    over_q=F(151,50)
    over_raw=BIAS+3010
    require(decode(over_raw,0)==3000 and abs(3000-1000*over_q)==20,'Overrange precision counterexample lost')
    return dict(load_cases=load_cases,isolation_cases=iso_cases,plant_cases=plant_cases,safest_endpoint_noise_pairs=pairs,settled_open_raw_values=11,overload_rejected=True,overrange_valid_high_value={'actual_load':'151/50','raw':over_raw,'decoded':3000,'two_sided_error':20,'still_fails_low_guard':True})


def graph_checks():
    graph=GroupGraph()
    require(len(graph.heads)==13*2*2*11*2==1144,'Independent functional head inventory wrong')
    world={(1,s,p,k):(F(6,5) if k==0 else F(1)) for s in (0,1) for p in range(11) for k in (0,1)}
    denied=capture(graph.heads[0],world,F(0),prepaid=0)
    require(not denied['started'] and denied['payload'] is None,'An unfunded probe fabricated a fresh reading')
    samples=[]
    for j,head in enumerate(graph.heads):
        start=F(j%17,100)+F(j//17,64)
        sample=capture(head,world,start,delay=S if j%2 else S/2)
        require(start<=sample['sample']<=sample['completion']<=start+S,'Raw conversion fabricated a current-frame callback')
        samples.append(sample)
        if head.kind==0:
            require(decode(sample['payload'],0)>700,'Internal target load change corrupted the independent relation')
        require(graph.functional_slots([('coupling',head)])=={graph.origins.index(head.origin)},'A head failure was counted by a name rather than its actual reach')
    require(graph.functional_slots([('target_status',1)])==set(),'Shared target status entered functional path')
    require(graph.status_slots([('target_status',1)])==set(range(13)),'Common status dependency disappeared')
    require(graph.functional_slots([('frontend',0)])=={0},'Whole primary frame silently became13 sources')
    # One added common tap/anchor reaches every functional source despite owner=t.
    common=('shared_tap',1)
    graph.edges[common].update(('coupling',h) for h in graph.heads)
    require(graph.functional_slots([common])==set(range(13)),'Common connection was charged as one target label')
    # A plausible wrong finite binding is not an open-circuit indication.
    head=graph.heads[0]
    wrong=(2,head.side,head.conduit,head.kind)
    world[wrong]=F(0)
    counterfeit=capture(head,world,F(0),binding=wrong)
    require(decode(counterfeit['payload'],0)==0,'Wrong-object binding was given a validity oracle')
    private_bays={2*incidence.neighbors(1,432).index(h.origin)+h.bank for h in graph.heads}
    require(len(private_bays)==26 and all(0<=bay<80 for bay in private_bays),'Independent heads conflicted with private candidate incidence')
    return dict(unfunded_has_no_fresh_result=True,selected_private_candidate_leads=len(private_bays),selected_origins=list(graph.origins),functional_heads_in_group=len(graph.heads),capture_cases=len(samples),per_capture_energy=4096,max_conversion=str(S),shared_status_affected_slots=13,shared_status_functional_slots=0,primary_frame_functional_slots=1,shared_tap_functional_slots=13,wrong_binding_raw=counterfeit['payload'],wrong_binding_looks_numeric=True,head_components_per_provider_bank=40*44,head_components_per_host=2*40*44,total_heads_at432=432*2*40*44,no_per_client_head_replication=True)


def incidence_and_history_checks():
    graph=GroupGraph()
    checked=0
    for target in incidence.neighbors(0,432):
        selected,_=incidence.groups(0,target,432)
        receiver_index=incidence.neighbors(0,432).index(target)
        for provider in selected:
            provider_index=incidence.neighbors(provider,432).index(target)
            require(incidence.neighbors(provider,432)[provider_index]==target,'Provider head measured a different physical target')
            returned=incidence.neighbors(0,432).index(incidence.neighbors(provider,432)[provider_index])
            require(returned==receiver_index,'Return wire changed the physical key')
            checked+=1
    provider=graph.origins[0]
    ci=incidence.neighbors(0,432).index(1)
    pi=incidence.neighbors(provider,432).index(1)
    wrong=incidence.neighbors(provider,432)[ci]
    require((provider,ci,pi,wrong)==(413,20,39,414),'Selected-provider wrong-ordinal witness changed')
    roster=(0,*graph.origins)
    cases=0
    for count in range(6):
        for retained in combinations(roster,count):
            permanent={1}
            initial=set(retained[::2])
            later=set(retained[1::2])
            union=permanent|initial|later
            actual=graph.body_support(union)
            require(len(union)<=6 and len(actual)<=len(union),'Joint P/A0/retained cover understated evidence reach')
            cases+=1
    first=set(graph.origins[:6]);second=set(graph.origins[6:12])
    require(len(graph.body_support(first))==len(graph.body_support(second))==6,'Instantaneous support countercase missing')
    require(len(graph.body_support(first|second))==12,'Old-record window union was incorrectly reset')
    return dict(physical_target_routes=checked,selected_wrong_ordinal={'provider':provider,'receiver_ordinal':ci,'provider_ordinal':pi,'wrong_target':wrong},joint_cover_cases=cases,P_target_internal_only_creates_no_extra_functional_slot=True,instantaneous_bad_origins=6,full_window_bad_origins=12,release_is_not_cleaning=True)



def plant_map_checks():
    routes=0
    for receiver in range(432):
        for parity in (0,1):
            origins=[o for o in incidence.neighbors(receiver,432) if o%2==parity][:13]
            require(len(origins)==13,'Plant row lacks its thirteen distinct origins')
            for origin in origins:
                region=origin//72
                heads=((region-1)%6,region,(region+1)%6)
                require(receiver//72 in heads,'A declared plant head observed the wrong region')
                routes+=1
    a=(F(2,5),F(3,5));b=(F(3,5),F(2,5))
    require(sum(a)==sum(b),'Same-sum ambiguity changed')
    difference_a=nearest(1000*(a[0]-a[1])+1000)
    difference_b=nearest(1000*(b[0]-b[1])+1000)
    require((difference_a,difference_b)==(800,1200),'Complementary rank-one row was replaced by a full-state head')
    return dict(origin_region_routes=routes,one_rank_per_origin=True,sum_ambiguous_states=[[str(x) for x in a],[str(x) for x in b]],different_encoded_difference_rows=[difference_a,difference_b],plant_integer_error=5,functional_integer_error=10)


def logical_quorum_checks():
    outcomes={}
    for affected in (0,1,6,7,13):
        records=[(0,1200) if j<affected else (1200,1200) for j in range(13)]
        count=vote_count(records,700)
        require(count==affected,'A/B records were counted as separate logical origins')
        outcomes[str(affected)]={'count':count,'permission':count>=7}
    require(not outcomes['6']['permission'] and outcomes['7']['permission'],'Threshold boundary lost')
    return dict(origin_once=outcomes,common_tap_count=13,healthy_sibling_does_not_cure_bad_A=True)


def program_checks():
    import program_model as P
    design=P.Design(degree=40,bays=80,origins=13,connectors_a=11,connectors_b=11,fast_batch=1,query_batch=1,physical_parameters=(("LOAD_MARGIN",300),("ISOLATION_MARGIN",180)))
    compiled=P.compile_check(design);k=compiled.constants
    require(k['SENSE_BIAS']==32 and k['SENSE_ERROR']==10 and k['LOAD_SENSOR_CAP']==3000,'Functional ABI changed')
    machine=P.formation(compiled)
    source=P.RawPorts(compiled)
    target_index=39
    initial_code=machine.C[:]
    results=[]
    for raw_words,kind in (([raw_for(F(6,5))]+[raw_for(F(1,5))]*10,0),([raw_for(F(1))]*11,1),([0]+[raw_for(F(1,5))]*10,0),([raw_for(F(100))]+[raw_for(F(1,5))]*10,0),([0]+[raw_for(F(1))]*10,1)):
        offset=k['VIEW_WORDS']+(0 if kind==0 else k['CONNECTORS_A']+k['CONNECTORS_B'])
        machine.W[k['FAST_CURSOR']]=target_index*k['RAW_TARGET_HEADS']+offset
        source.publications=[]
        for member,word in enumerate(raw_words):
            source.functional[(target_index,0,member,kind)]=word
        for _ in raw_words:
            machine.enter('publish_fast');require(machine.run(source,until_yield=False)=='halt','Ordinary source fold failed to finish')
        key=3+target_index*k['FAST_TARGET_KEYS']+k['VIEW_WORDS']+(0 if kind==0 else 2)
        offered=[event[2] for event in source.publications if event[0]=='source_offer_fast' and event[1][1]==key]
        expected=fold(raw_words,kind)
        require(offered and all(v==(WORD_MASK if expected is None else expected) for v in offered),'Actual P differed from the raw-head fold adapter')
        results.append({'kind':kind,'expected':expected,'fanout_offers':len(offered)})
    require(machine.C==initial_code,'Raw probe values changed actual C')
    receiver=P.RawPorts(compiled)
    receiver_target=20
    base=k['TARGET_BASE']+receiver_target*k['TARGET_WORDS']
    key=3+receiver_target*k['FAST_TARGET_KEYS']+k['VIEW_WORDS']
    permissions=[]
    for bad in (0,1,6,7,13):
        for origin in range(13):
            receiver.fast[(origin,0,key)]=0 if origin<bad else 1200
            receiver.fast[(origin,1,key)]=1200
            for bank in (0,1):receiver.fast[(origin,bank,key+2)]=0
        machine.enter('permission',(base,0));require(machine.run(receiver,until_yield=False)=='halt','Receiver guard did not finish')
        permissions.append(machine.result())
    require(permissions==[0,0,0,1,1],'Actual receiver lost its physical-origin threshold')
    primary=[]
    for value in (691,710):
        for origin in range(13):
            for bank in (0,1):
                receiver.fast[(origin,bank,key)]=value if origin==0 else 691 if origin<=6 else 710
                receiver.fast[(origin,bank,key+2)]=0
        machine.enter('permission',(base,0));machine.run(receiver,until_yield=False);primary.append(machine.result())
    require(primary==[1,0],'Whole primary frame stopped affecting the actual decision')
    return dict(actual_stored_source=True,source_fold_cases=results,provider_target_ordinal=target_index,receiver_target_ordinal=receiver_target,permission_bad_origin_counts=[0,1,6,7,13],permission_results=permissions,primary_values=[691,710],primary_permission_results=primary,code_preserved=True,scope='actual function execution plus INCIDENCE map; scheduling and maintained availability remain ACQUISITION/RUNTIME suppliers')


def future_envelope_check():
    values=[F(1,5)+F(j,1000) for j in range(11)]
    times=[F(j,64) for j in range(11)]
    rate=F(1,10000)
    effect=F(2000)
    reports=[decode(raw_for(value+rate*time),0) for value,time in zip(values,times)]
    maximum=max(reports)
    margin=F(10)+1000*rate*(effect-min(times))
    require(all(1000*(value+rate*effect)<=maximum+margin for value in values),'Multi-read fold lost its oldest-member future envelope')
    # A truthful past sample does not constrain an unbudgeted later physical jump.
    past=raw_for(F(1));gap=decode(past,1)
    require(gap==0 and gap<=20,'Initially isolated sample did not pass')
    actual_isolation_after=F(0)
    require(actual_isolation_after<F(4,5),'Future jump did not violate the actual condition')
    return dict(heterogeneous_member_samples=11,oldest_member_not_snapshot=True,truthful_sample_followed_by_unbudgeted_short={'raw':past,'decoded_deficit':gap,'actual_later_isolation':0,'corrupted_heads':0,'requires_slew_or_jump_supplier':True})


def normalize(value):
    if isinstance(value,F):return str(value)
    if isinstance(value,dict):return {str(k):normalize(v) for k,v in value.items()}
    if isinstance(value,(list,tuple)):return [normalize(v) for v in value]
    return value


def main():
    require(not sys.flags.optimize,'Optimized execution removes evidence checks')
    parser=argparse.ArgumentParser(description=__doc__)
    group=parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--write',action='store_true');group.add_argument('--check',action='store_true')
    args=parser.parse_args()
    names=('PROBE-MAP.md','probe_map_model.py','incidence_model.py','program_model.py','program_source.py')
    before={name:digest(HERE/name) for name in names}
    path=HERE/'probe_map_results.json'
    expected=json.loads(path.read_text(encoding='utf-8')) if args.check else None
    if expected:require(expected['sources']==before,'Bound probe/source inputs changed')
    result=normalize(dict(schema='functional-probe-map-v1',sources=before,scope='ideal raw measurement and finite dependency graph; full source admission and recurring support remain separate',quantization=quantized_checks(),graph=graph_checks(),incidence=incidence_and_history_checks(),plant_map=plant_map_checks(),quorum=logical_quorum_checks(),program=program_checks(),future_envelope=future_envelope_check()))
    require(before=={name:digest(HERE/name) for name in names},'Probe inputs changed during checking')
    if args.write:path.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n',encoding='utf-8',newline='\n')
    else:require(result==expected,'Reproduced probe result differs')
    print('PASS probe map:',result['graph']['functional_heads_in_group'],'independent head paths;',result['incidence']['joint_cover_cases'],'joint-cover cases; actual PROGRAM guards',result['program']['permission_results'])


if __name__=='__main__':main()

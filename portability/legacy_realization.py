"""Owner-indexed ordinary inventory and total removed-port source outcomes.

Finite source construction/encoding checks; not complete ISA/source admission.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as Q
import json
import subprocess
import sys
import types
import threshold_program_model as program
import threshold_design as design
import threshold_incidence_model as incidence
import threshold_publication_model as publication

HERE=program.HERE
PREFIX='theories-and-designs/byzantine-control/'
BASE='f9f9d48167aacce265f7e303e881cf2e5af93d1c'
FIELD='70ac3c8678e0de5a01136a11d6e97d321a088b0c'
need=program.need
MASK=(1<<256)-1


def text_at(commit,name):
    return subprocess.check_output(['git','show',commit+':'+PREFIX+name],cwd=program.REPO).decode('utf-8-sig').replace('\r\n','\n')


def module_at(commit,name,label):
    text=text_at(commit,name)
    module=types.ModuleType(label)
    module.__file__=str(HERE/name.split('/')[-1])
    sys.modules[label]=module
    exec(compile(text,module.__file__,'exec'),module.__dict__)
    return module,text


def inputs():
    resource,_=module_at(BASE,'local-control/port_resource_model.py','_legacy_resource')
    source,core,ports,bindings=resource.source_inputs()
    field_text=text_at(FIELD,'portability/threshold_field_source_results.json')
    field=json.loads(field_text)
    for name,sha in field['sources_sha256_lf'].items():
        need(program.hash_text(text_at(FIELD,'portability/'+name))==sha,'Frozen field source differs')
    return source,core,ports,field,bindings,field_text


def owner_record_index(receiver_ordinal,receiver_bank,source_bank,key,keys=2003):
    for value,bound in ((receiver_ordinal,40),(receiver_bank,2),(source_bank,2),(key,keys)):
        need(type(value) is int and 0<=value<bound,'Record address outside physical box')
    return (((receiver_ordinal*2+receiver_bank)*2+source_bank)*keys+key)


def capture_index(receiver_ordinal,receiver_bank,kind):
    for value,bound in ((receiver_ordinal,40),(receiver_bank,2),(kind,2)):
        need(type(value) is int and 0<=value<bound,'Capture address outside physical box')
    return (receiver_ordinal*2+receiver_bank)*2+kind


class GroupSelector:
    """Receiver-private fixed wiring; raw I contains no selector/control word."""
    def __init__(self,population,receiver):
        neighbors=incidence.neighbors(population,receiver)
        groups=[incidence.plant_group(population,receiver,row) for row in (0,1)]
        groups += [tuple(j for j,_ in incidence.maintenance_group(population,receiver,t)[1]) for t in range(40)]
        words=[0]*(2048*16)
        for key in range(2003):
            if key==2:continue
            group=groups[key if key<2 else 2+(key-3)//50]
            for slot,origin in enumerate(group):
                words[key*16+slot]=64+neighbors.index(origin)
        self.words=tuple(words)
        level=self.words
        while len(level)>1:level=tuple((level[i],level[i+1]) for i in range(0,len(level),2))
        self.tree=level[0]
        self.neighbors=neighbors

    @staticmethod
    def less(value,bound):
        # One declared four-work bit-comparison cell per captured wire bit.
        less=False;equal=True
        for bit in range(255,-1,-1):
            a=(value>>bit)&1;b=(bound>>bit)&1
            less=less or (equal and not a and b)
            equal=equal and a==b
        return bool(less)

    def walk(self,key,slot):
        node=self.tree
        address=(key<<4)|slot
        for bit in range(14,-1,-1):node=node[(address>>bit)&1]
        return node

    def select(self,key,slot,bank):
        if any(type(v) is not int or not 0<=v<=MASK for v in (key,slot,bank)):
            raise ValueError('Selector accepts actual unsigned256-bit wires')
        valid=[self.less(v,b) for v,b in ((key,2003),(slot,15),(bank,2))]
        # All paths reserve the complete fixed bound, including rejection.
        work=3*256*4+15*256+64
        if not all(valid):return None,work
        node=self.walk(key,slot)
        if not node&64 or (node&63)>=len(self.neighbors):return None,work
        return (self.neighbors[node&63],bank,'primary' if slot==0 else 'auxiliary'),work


class ArrivalDecoder:
    """One fixed source-bank/receiver-bank lane; no payload origin address."""
    def __init__(self,population,receiver,provider):
        targets=incidence.neighbors(population,receiver)
        need(provider in targets,'Arrival path is not an actual neighbor')
        source_targets=incidence.neighbors(population,provider)
        groups={key:incidence.plant_group(population,receiver,key) for key in (0,1)}
        for t in range(40):groups[3+50*t]=tuple(o for o,_ in incidence.maintenance_group(population,receiver,t)[1])
        words=[0]*2048
        for key in range(2003):
            if key==2:continue
            if key<2:destination=key;group=groups[key]
            else:
                t,relative=divmod(key-3,50);actual=source_targets[t]
                if actual not in targets:continue
                local=targets.index(actual);destination=3+50*local+relative;group=groups[3+50*local]
            if provider in group:
                words[key]=4096+2048*int(group.index(provider)==0)+destination
        self.words=tuple(words);level=self.words
        while len(level)>1:level=tuple((level[i],level[i+1]) for i in range(0,len(level),2))
        self.tree=level[0]

    def decode(self,key):
        if type(key) is not int or not 0<=key<2048:return None
        node=self.tree
        for bit in range(10,-1,-1):node=node[(key>>bit)&1]
        return None if not node&4096 or (node&2047)>=2003 or (node&2047)==2 else ('primary' if node&2048 else 'auxiliary',node&2047)

class PhysicalRecords:
    """Fixed installed cells; an address cannot allocate a new physical record."""
    def __init__(self,selector,initial=None):
        self.addresses={}
        for key in range(2003):
            if key==2:continue
            for slot in range(15):
                word=selector.words[key*16+slot]
                owner=selector.neighbors[word&63]
                role='primary' if slot==0 else 'auxiliary'
                for bank in (0,1):
                    self.addresses[(role,owner,bank,key)]=len(self.addresses)
        self.values=[MASK]*len(self.addresses) if initial is None else list(initial)
        need(len(self.values)==len(self.addresses) and all(type(v) is int and 0<=v<=MASK for v in self.values),'Initial raw words exceed installed cells/wires')
        need(len(self.values)==60060,'Installed sparse record cells differ')

    def get(self,address,default=MASK):
        index=self.addresses.get(address)
        return default if index is None else self.values[index]

    def put(self,address,value):
        index=self.addresses.get(address)
        if index is None or type(value) is not int or not 0<=value<=MASK:return False
        self.values[index]=value
        return True

def address_checks():
    seen=set()
    for r in range(40):
        for rb in range(2):
            for sb in range(2):
                for key in range(2003):
                    index=owner_record_index(r,rb,sb,key)
                    need(index not in seen,'Owner record allocation aliases')
                    seen.add(index)
                    tail,k=divmod(index,2003);tail,s=divmod(tail,2);r0,b=divmod(tail,2)
                    need((r0,b,s,k)==(r,rb,sb,key),'Owner inverse failed')
    need(len(seen)==320480 and max(seen)<1420796,'Owner budget exceeded')
    captures={320480+capture_index(r,b,t) for r in range(40) for b in range(2) for t in range(2)}
    need(len(captures)==160 and not captures&seen and max(captures)<1420796,'Capture padding aliases live records')
    populations=(82,86,12*(6+2**98)+2)
    groups_checked=lookups=0
    for m,r in ((populations[0],0),(populations[1],85),(populations[2],0),(populations[2],populations[2]-1)):
        selector=GroupSelector(m,r)
        for key in range(2003):
            if key==2:continue
            if key<2:group=incidence.plant_group(m,r,key)
            else:group=tuple(o for o,_ in incidence.maintenance_group(m,r,(key-3)//50)[1]) if (key-3)%50==0 else group
            groups_checked+=1
            for slot,o in enumerate(group):
                word=selector.walk(key,slot)
                need(word==64+selector.neighbors.index(o),'Fixed selector tree changed origin')
                lookups+=1
                if key<2 or (key-3)%50==0:
                    for bank in (0,1):
                        selected,work=selector.select(key,slot,bank)
                        need(selected==(o,bank,'primary' if slot==0 else 'auxiliary') and work==6976,'Private wire decode changed origin')
        for args in ((2,0,0),(2003,0,0),(0,15,0),(0,0,2),(MASK,0,0),(0,MASK,0),(0,0,MASK)):
            need(selector.select(*args)[0] is None,'Invalid route created an endpoint')
    # A real pointwise owner count already defeats exact receiver averaging.
    m=82;o=2;owned=0
    for receiver in incidence.neighbors(m,o):
        owned+=sum(o in incidence.plant_group(m,receiver,row) for row in (0,1))
        for target in range(40):
            owned+=50*sum(j==o for j,_ in incidence.maintenance_group(m,receiver,target)[1])
    owned*=4
    need(owned==120132>120120,'Expected pointwise averaging countercase differs')
    return dict(owner_box_exhaustive=len(seen),capture_padding_slots=len(captures),
                maximum_owner_index=max(captures),selector_groups=groups_checked,
                selector_lookups=lookups,selector_work_upper=6976,
                countercase=dict(population=m,source=o,actual_owned_records=owned,
                                 receiver_installed_records=120120),
                family_proof='Fixed radix injections, not translation-average or population enumeration')


def inventory(c,b,source,core,ports,field):
    k=c.constants;d=k['DEGREE'];n=2
    need((d,k['BAYS'],k['FAST_KEYS'],k['ORIGINS'])==(40,1,2003,15),'Wrong compiled inventory')
    private=c.next_register+k['DATA_WORDS']+32
    extra_private=8*(2*d+1)
    need(private==4140 and private+extra_private<=core['padded_private_words'],'Private capture state unallocated')
    owner_records=40*2*2*k['FAST_KEYS'];captures=40*2*2
    slots=dict(instructions=n,conversion=n,own_read=0,own_write=0,
               command=2*(d+1)*128,held_request=0,data=2*(2*d)*129)
    port_count=sum(v for key,v in slots.items() if key!='instructions')
    need(port_count==31138,'Wrong ordinary source capsule count')
    # Fixed decode leaves and active-path control at each installed tree node.
    hop_phases=dict(capture=32+8,forward=1+7,response=32+2*13+4,scrub=32+8)
    need(sum(hop_phases.values())+2*256<=1024,'Arrival payload transport exceeds its hop budget')
    need(sum(hop_phases.values())<=256 and max(15+4+3+1,13+3+1)<=32, 'Routing header/control/work exceeds its node')
    selector_bits=n*(2048*16*7+(2048*16-1)*32)
    translation_bits=160*(2048*13+2047*32)
    pairs=2*d*(15+2)
    memory=dict(code_and_private=n*(192*k['IMAGE_CELLS']+256*(private+extra_private)),
        selected_input_records=owner_records*2048+captures*(256+512),source_scratch=n*4096,
        request_receivers=0,port_descriptors=port_count*1024,instruction_latches=n*2048,
        command_mailboxes=n*(64*d+128),request_mailboxes=0,
        data_and_propagation=320*(115712+264*128),passive_target_endpoints=160*1024,
        held_fields=pairs*256,local_route_metadata=owner_records*128+selector_bits+translation_bits)
    comparisons={}
    for key,value in memory.items():
        old=core['memory_categories'][key]
        need(value<=old,'Pointwise memory owner row exceeds old allocation: '+key)
        comparisons[key]=dict(new_owner_upper=value,old_owner_allocation=old,slack=old-value)
    bits=sum(memory.values());autonomous=bits-memory['code_and_private']
    clock=Q(core['background_clock_rate']);leakage=Q(bits,1024)
    need(bits<=core['memory_bits'] and autonomous<=core['autonomous_bits'],'Background circuit envelope fails')
    actual_power=pairs*Q(core['actual_force_pair_power'])+20
    actual_field_stock=pairs*Q(core['actual_force_pair_stock'])+200
    need(actual_power==4080020<=Q(core['generator_power']),'Real ordinary fields underfunded')
    naive=n*d*(64+8)*12
    need(naive<actual_power,'Naive new generator allocation should fail')
    need(actual_field_stock==49160<=Q(core['transducer_capacity']),'Ordinary field stock underallocated')
    writer_stock=12800*4096;writer_rate=writer_stock*2**30
    ordinary_capsule=n*20480+port_count*4096
    flight=ports['data_field_energy_capacity']
    ordinary_stock=ordinary_capsule+flight
    need(ordinary_stock<=ports['isolated_energy_capacity']-writer_stock,'Writer saving reused as ordinary stock')
    recharge=port_count*4096*2**30+n*4*20480*2**27
    bank_rate=Q(recharge,2)+actual_power/2+leakage/2
    retained_bank_rate=Q(core['per_bank_rate'])-Q(writer_rate,2)
    need(bank_rate<=retained_bank_rate,'Actual ordinary bank demand exceeds downrated transit supplier')
    keeper_cap_time=1+2*Q(core['per_bank_capacity'])/retained_bank_rate
    keeper_head=Q(core['per_bank_capacity'])//Q(core['energy_head_unit'])
    need(keeper_cap_time<21 and keeper_head<2**20,'Connected keeper cap/head comparison fails')
    # Target-head operations retain a conservative old endpoint work envelope;
    # their source-paid pulse remains one operation, not fresh target E/T fuel.
    external_rows=[dict(name='raw symbols',count=160,price=8,burst=264,rate=1040),
                   dict(name='passive measured-head endpoints',count=160,price=4096,burst=1,rate=2**27)]
    ext_burst=sum(r['count']*r['price']*r['burst'] for r in external_rows)
    ext_rate=sum(r['count']*r['price']*r['rate'] for r in external_rows)+autonomous*clock+leakage
    need(Q(11584*101,100*2**31)<Q(1,2048), 'Fixed arrival decoder breaks RX service')
    need(ext_burst<=Q(core['external_burst']) and ext_rate<=Q(core['external_rate']),'External owner envelope exceeded')
    capture_stock=captures*1024;capture_rate=captures*2*1024*2**30
    need(capture_stock<=12800*1024 and capture_rate<=12800*2*1024*2**30,'Origin-affine capture envelope exceeded')
    e=source['parameters']['execution'];delta=Q(1,2**30)
    private_work=928+6976+1024+256
    suffix=Q(404,100)*delta+2*delta+Q(928+6976+256)/Q(e['private_native_work_rate_capacity'])
    need(private_work<20480 and suffix<Q(3,4)/Q(e['nominal_instruction_rate_max']), 'Explicit group selector breaks parent/timing budget')
    need(suffix+Q(1,4*2**27)<Q(1)/Q(e['nominal_instruction_rate_max']), 'Selector/reset/recharge overlap')
    fr=field['point']['resources']
    need(Q(fr['removed_writer_stock'])==writer_stock and Q(fr['removed_writer_peak'])==writer_rate,'Field ledger uses another saving')
    need(Q(fr['new_bank_rate'])==retained_bank_rate,'Field ledger transit rate differs')
    need(Q(fr['usable_reserve_lower'])>1,'Frozen field reserve is unavailable')
    return dict(processors=n,code_capacity_per_processor=k['IMAGE_CELLS'],compiled_cells=len(c.nodes),
        private_program_words=private,additional_private_boundary_words=extra_private,
        fast_key_capacity=k['FAST_KEYS'],uninstalled_keys=[2],selected_records_per_receiver_bank=2*15*(k['FAST_KEYS']-1),
        receiver_record_count_upper=2*2*15*k['FAST_KEYS'],owner_record_count_upper=owner_records,
        raw_capture_cells_per_owner=captures,raw_capture_cells_per_receiver=captures,
        selector_table_bits=selector_bits,key_translation_bits=translation_bits,routing_hop_work=hop_phases,
        memory_by_owner=comparisons,owner_memory_bits_upper=bits,autonomous_owner_bits=autonomous,
        slots=slots,ordinary_port_capsules=port_count,ordinary_capsule_capacity=ordinary_capsule,
        retained_flight_capacity=flight,ordinary_installed_capacity_ceiling=ordinary_stock,
        retained_ordinary_capacity_envelope=ports['isolated_energy_capacity']-writer_stock,
        actual_signed_pairs=pairs,actual_ordinary_power=actual_power,actual_ordinary_field_stock=actual_field_stock,
        failed_naive_generator_allowance=naive,retained_generator_allowance=Q(core['generator_power']),
        actual_ordinary_recharge_peak=recharge,actual_ordinary_bank_rate_upper=bank_rate,
        connected_keeper_cap_time=keeper_cap_time,actual_keeper_energy_word=keeper_head,pointwise_draw_does_not_require_instruction_success=True,
        actual_energy_head_unit=core['energy_head_unit'],
        retained_downrated_bank_allowance=retained_bank_rate,external_rows=external_rows,
        external_burst_upper=ext_burst,external_rate_upper=ext_rate,capture_capacity=capture_stock,
        capture_upstream_rate=capture_rate,private_IO_work_with_selector=private_work,
        private_IO_native_suffix=suffix,unassigned_parent_work=20480-private_work,
        unassigned_native_work=16384-928-6976-256,
        field_additions_not_rebilled={key:fr[key] for key in ('pulse_stock','setter_stock','reset_stock','new_control_bits','holding_power','reset_chargers')},
        field_reserve=fr['usable_reserve_lower'],total_host_capacity_upper=fr['unchanged_total_host_stock'],
        unused_old_devices_installed=False,additional_stock_saving_credited=False,
        direct_billing_map_scope='Owner-local envelope domination; full parent/native timing implementation remains separate')


def absence_ports_class(isa):
    Parent=program.ports_class(isa)
    class AbsentPorts(Parent):
        def __init__(self,c):
            super().__init__(c)
            for name in ('requests','replies','target_cells','own_bays','own_override','write_enabled'):
                if hasattr(self,name):delattr(self,name)
            self.absent=[]
            self.selector=GroupSelector(12*(6+2**98)+2,0)
            self.physical_records=PhysicalRecords(self.selector)
            self.selection_work=0
        def perform(self,name,args,machine):
            if name in ('fast_cmp','fast_equal','fast_range'):
                slot,bank,key,*bounds=args
                selected,work=self.selector.select(key&MASK,slot&MASK,bank&MASK)
                self.selection_work+=work
                value=MASK if selected is None else self.physical_records.get((selected[2],selected[0],selected[1],key),MASK)&MASK
                if name=='fast_cmp':return int(value<=bounds[0])
                if name=='fast_equal':return int(value==bounds[0])
                return int(bounds[0]<=value<=bounds[1])
            if name=='source_start_fast' and args==(2,):
                self.sample_attempts+=1
                if self.job is not None:return 0
                self.I[0]=2;self.valid=False;self.samples+=1
                self.job=(self.now+self.conversion_delay,'fast',2,MASK)
                return 0
            if name in program.FORBIDDEN:
                # Fixed opcode decoder: no old physical endpoint or child slot.
                if name=='source_capture_request':self.I[0]=isa.WORD_MASK
                work=6+64+(256 if name=='source_capture_request' else 0)
                self.absent.append(dict(name=name,args=list(args),work=work,result=0))
                return 0
            return super().perform(name,args,machine)
    return AbsentPorts


def decoder_checks(isa,c,b,port_module,field_module):
    Ports=absence_ports_class(isa);reports=[]
    for name in sorted(program.FORBIDDEN):
        arity=isa.PRIM_ARITY[name]
        for malformed in (False,True):
            machine=program.initialized(isa,c);ports=Ports(c)
            args=([0,1,7,991][:arity] if not malformed else [-1]*arity)
            machine.C[0]=isa.encode(isa.IO,2,3,arity,isa.PRIM[name]);machine.C[1]=isa.encode(isa.HALT)
            machine.R[3:3+arity]=[a&isa.WORD_MASK for a in args]
            ports.I[:]=[77]*8;ports.job=(1000000,'functional',(0,0,0,0),123)
            old_job=ports.job
            reservoir=port_module.Reservoir.filled(20480)
            parent=port_module.Slot(reservoir,price=Q(20480),recharge_time=Q(1,4*2**26))
            need(not machine.launch(funded=False),'Unfunded bad IO launched')
            parent.recharge(parent.recharge_time)
            need(parent.offer(0,('physical-body',name),Q(3,4*2**26)),'Funded parent unavailable')
            need(machine.launch(funded=True),'Actual bad IO did not latch')
            machine.C[0]=isa.encode(isa.HALT);machine.R[3:3+arity]=[17]*arity
            machine.powered=False;machine.reset_entry();parent.digital_reset()
            need(parent.elapse(Q(1,2**26),lambda _:need(machine.complete(ports),'Latched parent erased')),'Paid completion absent')
            need(not machine.complete(ports) and not machine.launch(),'Parent replayed or unpowered relaunch')
            port_module.conservation(reservoir,[parent])
            need(len(ports.absent)==1 and ports.absent[0]['args']==args and machine.R[2]==0,'Captured absence result differs')
            need(ports.job==old_job and not ports.publications and not ports.offer_pending,'Removed IO created/cancelled child work')
            need(all(not hasattr(ports,a) for a in ('requests','replies','target_cells','own_bays')),'Legacy endpoint installed')
            need(ports.absent[0]['work']<=4096,'Absence decoder exceeds local allocation')
            reports.append(dict(opcode=name,malformed=malformed,latched_args=args,retired=machine.retired,
                                fragment_work=ports.absent[0]['work'],paid_parent=20480,children_created=0))
    missing=Ports(c);missing.fast[('head',2)]=123
    missing.perform('source_start_fast',(2,),None);missing.elapse(2)
    need(missing.I[1]==MASK and missing.job is None,'Uninstalled head2 created a nominal source')
    # Actual native STOREC survives. Subsequent ordinary LOADC drives the field.
    machine=program.initialized(isa,c);ports=Ports(c);address=100;word=c.image[address]^1
    machine.C[0]=isa.encode(isa.STOREC,3,4);machine.R[3]=word;machine.R[4]=address
    need(machine.step(ports) and machine.C[address]==word,'Removed-port map accidentally removed native STOREC')
    machine.W[c.constants['VECTOR_CURSOR']]=address*192
    machine.enter('refresh_fields');need(machine.run(ports,budget=b['instruction_upper_bounds']['refresh_fields']+10,until_yield=False)=='halt','Actual-C scanner stopped')
    need(ports.held_fields[(('body',0),0,address*192)]==2*(word&1)-1,'Field scanner read a protected image')
    parent=field_module.WorkCell(field_module.WORD_ENERGY,field_module.WORD_ENERGY)
    cells,steps,work,completed=field_module.native_word([Q(-1)]*192,word,address=address,parent=parent)
    need(completed and steps==2080 and all(v==2*((word>>i)&1)-1 for i,v in enumerate(cells)),'Native physical word fragment failed')
    # Ordinary present ports continue their actual implementation.
    ordinary=Ports(c);ordinary.fast[('head',0)]=450;ordinary.fast[('head',1)]=450
    published=program.call(isa,c,ordinary,'publish_plant',(),b['instruction_upper_bounds']['publish_plant']+10)
    need(ordinary.offers==160 and ordinary.samples==2,'Absence decoder stubbed present publication')
    # Actual producer records enter source-specific compartments; P's private
    # comparisons consume the new fixed group decoder.
    population=12*(6+2**98)+2;joined=Ports(c);producer_steps=0
    providers=set(incidence.plant_group(population,0,0))|set(incidence.plant_group(population,0,1))
    for provider in sorted(providers):
        sender=program.ports_class(isa)(c);value=(500,1000)[incidence.head_type(provider)]
        sender.fast[('head',0)]=value;sender.fast[('head',1)]=value
        pm=program.call(isa,c,sender,'publish_plant',(),b['instruction_upper_bounds']['publish_plant']+10)
        producer_steps+=pm.steps
        arrival=ArrivalDecoder(population,0,provider)
        sender.elapse(2)
        client=2*incidence.neighbors(population,provider).index(0)+1
        for _,kind,args,value in sender.delivered:
            if kind!='source_offer_fast' or args[0]!=client:continue
            destination=arrival.decode(args[1])
            expected=publication.route(c,population,provider,1,client,args[1],value)
            need((destination is None)==(expected is None),'Unselected producer row reached an endpoint')
            if destination is None:continue
            need(destination==('primary' if expected.slot==0 else 'auxiliary',expected.destination_key),'Fixed arrival decoder changed physical target')
            need(joined.physical_records.put((destination[0],provider,1,destination[1]),value),'Arrival selected an uninstalled physical record')
    joined.fast[('head',0)]=500;joined.fast[('head',1)]=500
    consumer=program.initialized(isa,c);consumer.W[c.constants['ENTRY']]=1;consumer.enter('frame')
    while not consumer.io_counts['world'] and consumer.steps<b['active_frame_upper']:
        need(consumer.step(joined),'New private-selector consumer stopped')
    poisoned=PhysicalRecords(joined.selector,[0]*60060)
    need(poisoned.values==[0]*60060,'Constructor supplied trusted initial raw words')
    fixed_cells=len(joined.physical_records.values)
    need(not joined.physical_records.put(('auxiliary',0,1,0),17) and len(joined.physical_records.values)==fixed_cells,'Malformed route allocated hardware')
    need(joined.world_latch==(60,60) and joined.selection_work>0,'P did not consume physical endpoint records')
    malformed_encodings=0
    for primitive,arity in ((len(isa.PRIMITIVES)+1,0),(isa.PRIM['write_own'],0),(isa.PRIM['own_equal'],3)):
        mm=program.initialized(isa,c);pp=Ports(c);mm.C[0]=isa.encode(isa.IO,2,3,arity,primitive);mm.R[2]=37
        need(mm.step(pp) and mm.R[2]==37 and not pp.absent,'Malformed IO created a removed endpoint')
        malformed_encodings+=1
    return dict(removed_opcode_cases=reports,removed_opcodes=sorted(program.FORBIDDEN),
                paid_parent_replay_rejected=True,unrelated_normal_conversion_retained=True,
                malformed_instruction_cases=malformed_encodings,uninstalled_head2_unavailable=True,
                fixed_receiver_record_cells=fixed_cells,invalid_record_allocation_rejected=True,arbitrary_initial_raw_words_retained=True,
                actual_native_STOREC=True,actual_C_field_read=True,
                native_fragment_steps=steps,native_fragment_physical_work=work,
                present_publish_instructions=published.steps,present_offers=ordinary.offers,
                private_selector_world=list(joined.world_latch),private_selector_work=joined.selection_work,
                producer_instructions=producer_steps,consumer_instructions=consumer.steps,
                scope='Actual mutable IO instructions and retained paid parents; full atomic native ISA refinement remains open')


def normalize(value):
    if isinstance(value,Q):return str(value)
    if isinstance(value,dict):return {k:normalize(v) for k,v in value.items()}
    if isinstance(value,(list,tuple)):return [normalize(v) for v in value]
    return value


def generate():
    source,core,ports,field,bindings,field_text=inputs()
    isa=program.load_isa();c=program.compile_program(isa,design.design(isa));b=program.bounds(isa,c)
    port_module,port_text=module_at(BASE,'local-control/port_model.py','_legacy_ports')
    field_module,field_code=module_at(FIELD,'portability/threshold_field_source.py','_legacy_native_field')
    print('checking complete finite owner boxes and private group wiring',flush=True)
    addresses=address_checks()
    arrival_cases=0
    for provider in incidence.neighbors(86,0):
        arrival=ArrivalDecoder(86,0,provider);client=2*incidence.neighbors(86,provider).index(0)
        for key in range(2003):
            found=arrival.decode(key);expected=publication.route(c,86,provider,0,client,key,17)
            need((found is None)==(expected is None),'Arrival validity mismatch')
            if found is not None:need(found==('primary' if expected.slot==0 else 'auxiliary',expected.destination_key),'Arrival role/target mismatch')
            arrival_cases+=1
    addresses['actual_arrival_table_cases']=arrival_cases
    point=inventory(c,b,source,core,ports,field)
    print('executing removed IO and retained native/ordinary operations',flush=True)
    decoder=decoder_checks(isa,c,b,port_module,field_module)
    names=('LEGACY-REALIZATION.md','legacy_realization.py','threshold_program_model.py','threshold_program_source.py',
           'threshold_design.py','threshold_incidence_model.py','threshold_publication_model.py')
    frozen={BASE+':local-control/'+n:program.hash_text(text_at(BASE,'local-control/'+n)) for n in
            ('RUNTIME-PORTS.md','PORT-SOURCE.md','PORT-RESOURCES.md','resource_model.py','port_model.py')}
    frozen[FIELD+':portability/threshold_field_source_results.json']=program.hash_text(field_text)
    frozen[FIELD+':portability/threshold_field_source.py']=program.hash_text(field_code)
    frozen[FIELD+':portability/THRESHOLD-FIELD-SOURCE.md']=program.hash_text(text_at(FIELD,'portability/THRESHOLD-FIELD-SOURCE.md'))
    return normalize(dict(scope='Constructed ordinary arrays/owner maps and absent-port law, with bounded independent source obligations',
        base=BASE,field_source=FIELD,python_version=sys.version,
        image_sha256=program.hash_text(json.dumps(c.image)),frozen_ISA_sha256=isa.source_hash,
        sources_sha256_lf={n:program.digest(HERE/n) for n in names},immutable_sha256_lf=frozen,
        old_resource_bindings=bindings,address_checks=addresses,inventory=point,decoder=decoder,
        residuals=['full parent fetch/operand/dispatch/return and native ISA observation map',
                   'physical fault containment and private-selector/common-primary source admission',
                   'timed source/head/command realization and same-history field/reset/retirement composition',
                   'complete positive-family and reusable-core mission proof'],
        full_source_admission=False,program_completion=False,independent_review_pending=True))


def main():
    parser=argparse.ArgumentParser(description=__doc__);g=parser.add_mutually_exclusive_group(required=True)
    g.add_argument('--write',action='store_true');g.add_argument('--check',action='store_true');args=parser.parse_args()
    result=generate();path=HERE/'legacy_realization_results.json'
    if args.write:path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n',encoding='utf-8',newline='\n')
    else:need(json.loads(path.read_text(encoding='utf-8'))==result,'Legacy-realization record differs')
    print('PASS owner-local inventory and absent-port construction; full source remains open')


if __name__=='__main__':main()

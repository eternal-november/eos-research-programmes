"""Paid retirement and token-entry refinement for the actual ordinary parent."""
from __future__ import annotations
import argparse
from dataclasses import dataclass, field as dcfield, replace
from fractions import Fraction as Q
from hashlib import sha256
import json
from math import ceil
from pathlib import Path
import sys
from types import GeneratorType
import parent_realization as parent
import threshold_field_source as field
import cam_reformation as cam

HERE=Path(__file__).resolve().parent
BASE='36d69bce7a4705fd54a915beb7c00cea55cce063'
CONTROL_BITS=4096
RESET_WORK=2*CONTROL_BITS+ceil(Q(CONTROL_BITS-1,2))+1409
SETTER_RESET_WORK=11393
CPU_CLEAR_TIME=Q(1,64)
LINK_TAIL=Q(1)
PARENT_DUMP_TIME=Q(100)
NATIVE_POWER=Q(512)
need=parent.need

def exact(x):
    if type(x) not in (int,Q):raise ValueError('Exact non-Boolean quantity required')
    return Q(x)

class RouteWait(Exception):pass

@dataclass
class RouteNode:
    header:int=(1<<128)-1
    busy:bool=True
    return_claim:object=None
    visits:int=0  # Analyst count.

@dataclass
class PhysicalToken:
    """Actual root work/authority claim; object identity is an analyst index.

    The physical primitive has one root ingress and one return cutset. Data
    writes cannot create that ingress event. A consumed claim has no supply
    connection when the same parent cell is later charged for a new arrival.
    """
    cell:object
    body:object
    live:bool=True
    position:tuple=('root',0)
    issued:bool=False

class RouteFabric:
    """One actual powered token, priority entry, and no epoch labels."""
    def __init__(self,cell,body):
        self.cell=cell;self.body=body;self.token=None
        self.nodes={};self.cut=False;self.return_cut=False
        self.links=[];self.front_work=0;self.rejected=0
        self.old_returns=[];self.clock=True
        self.header=0
        self.link_work_issued=Q(0)  # Analyst conservation total, not a runtime counter.
    def link_storage_busy(self):
        return any(x[2]>0 or x[3].stock>0 for x in self.links)
    def archive_empty_links(self):
        if self.link_storage_busy():return False
        self.old_returns.extend(self.links);self.links=[];return True
    def link_balance(self):
        records=self.links+self.old_returns
        need(len({id(x) for x in records})==len(records),'A private signal was counted twice')
        need(sum((x[3].stock+x[3].dumped+x[3].spent for x in records),Q(0))==self.link_work_issued,
             'Private signal work was dropped on reuse')
    def new_parent(self):
        if self.cut or self.token is not None or self.cell.stock!=parent.PARENT:return False
        self.token=PhysicalToken(self.cell,self.body)
        self.front_work=0;return True
    def access(self,kind,address):
        token=self.token
        if token is None or not token.live or self.cut or not self.clock or self.link_storage_busy():
            raise RouteWait('no live private route')
        if kind not in ('C','private'):raise ValueError('No such installed private tree')
        depth=13
        if type(address) is not int or not 0<=address<1<<depth:raise ValueError('Route address outside its wire')
        node_index=0;visited=[]
        for level in range(depth):
            key=(kind,node_index)
            node=self.nodes.setdefault(key,RouteNode())
            if not self.cell.debit(20):raise RouteWait('route work unavailable')
            self.front_work+=20
            # ENTRY is a physical energized arrival, independent of old data.
            # Revoke an old returning capability BEFORE interpreting headers.
            node.return_claim=None;node.busy=False
            self.header=(address | (level<<13));node.header=self.header
            node.return_claim=token;node.busy=True;node.visits+=1
            token.position=key;visited.append(node)
            bit=(node.header>>(depth-level-1))&1
            node_index=2*node_index+1+bit
        leaf=node_index-(1<<depth)+1
        need(leaf==address,'Priority routing changed the captured physical leaf')
        for node in reversed(visited):
            node.return_claim=None;node.busy=False
        token.position=('root',0)
        return leaf
    def offer(self,token):
        if self.cut or token is not self.token or not token.live or token.issued:return False
        token.issued=True;return True
    def retain_link(self,payload):
        if self.token is None or not self.token.live:raise ValueError('No actual route token')
        if type(payload) is not int or not 0<=payload<=parent.MASK:raise ValueError('Link payload exceeds its256-bit wire')
        if self.cut:return 'cut'
        if self.link_storage_busy():return 'link-busy'
        self.archive_empty_links()
        if not self.cell.debit(20):return 'link-unfunded'
        self.front_work+=20
        # This is a partition of delivered parent work, not a fresh reserve.
        signal=field.WorkCell(Q(20),Q(20))
        self.link_work_issued+=20
        self.links=[[self.token,payload,LINK_TAIL,signal]]
        self.token.position=('link',0)
        return self.links[0]
    def inhibit(self):
        self.cut=True;self.return_cut=True
    def flow_links(self,dt):
        dt=exact(dt)
        if dt<0:raise ValueError('Negative link flow')
        for link in self.links:
            link[2]=max(Q(0),link[2]-dt)
            loss=min(link[3].stock,Q(20)*dt/LINK_TAIL)
            link[3].stock-=loss;link[3].dumped+=loss
        self.link_balance()
        # Expired link signals lose their physical return authority; their
        # payload/owner is retained as audit residue, never rebound.
    def return_effect(self,claim):
        token=claim[0]
        if self.return_cut or claim[2]<=0 or claim[3].stock<=1 or not token.live or token is not self.token or token.cell.stock<16:
            self.rejected+=1;return 'inert-old-return'
        return 'current-return'
    def consume(self):
        if not self.cut or not self.return_cut or self.cell.stock>field.DUMP_FLOOR:
            return 'not-isolated-and-low'
        if self.link_storage_busy():return 'link-tail-wait'
        if self.token is not None:
            self.token.live=False
        self.archive_empty_links()
        self.token=None
        # No whole-array scrub: unvisited data stays arbitrary and powerless.
        return 'consumed'
    def normal_finish(self):
        if self.link_storage_busy():raise RouteWait('old private return retains storage or tail')
        self.archive_empty_links()
        if self.token is not None:self.token.live=False
        self.token=None

class RoutedBody(parent.Body):
    def __init__(self,c,initial_code=None):
        super().__init__(c,initial_code);self.fabric=None
    def path(self,kind,address):
        return self.fabric.access(kind,address) if self.fabric is not None else parent.routed_index(address,13)[0]
    def read_R(self,address):return self.R[self.path('private',address)] if 0<=address<len(self.R) else 0
    def write_R(self,address,value):
        if 0<=address<len(self.R):self.R[self.path('private',address)]=value
    def read_W(self,address):return self.W[self.path('private',2048+address)-2048] if 0<=address<len(self.W) else 0
    def write_W(self,address,value):
        if 0<=address<len(self.W):self.W[self.path('private',2048+address)-2048]=value
    def observe_word(self,address):
        address=self.path('C',address)
        return super().observe_word(address)
    def coordinates(self,address):
        address=self.path('C',address)
        return super().coordinates(address)

class GuardedNative(parent.NativeWrite):
    def __init__(self,machine,*args):
        super().__init__(*args);self.machine=machine;self.token=machine.fabric.token
        self.retired=False;self.drive_work=Q(0)
    def step(self,clock=True):
        if self.retired or not self.token.live:return 'retired'
        if not clock:return 'clock-wait'
        if self.machine.native_inhibit:return 'access-wait'
        if type(self.index) is not int or not 0<=self.index<4096:raise ValueError('Native index exceeds its12-bit wire')
        if not self.done and (self.index>=2080 or 704<=self.index<1856 and (not self.accepted or self.binding is None)):
            return 'control-wait'
        # Reserve the actual bounded drive work before a bit can move. The
        # original completion unit remains an additional dissipated margin.
        work=NATIVE_POWER/field.WORD_CLOCK if self.drive_bit is not None else Q(0)
        qualification=parent.QUALIFICATION_WORK if self.index==511 else 0
        if self.parent.stock<9+qualification+work:return 'work-wait'
        if work:
            self.parent.debit(work);self.drive_work+=work
        return super().step(clock)
    def flow(self,dt,external=Q(0)):
        dt=exact(dt);external=exact(external)
        if dt<0:raise ValueError('Negative native flow')
        if self.drive_bit is None or self.binding is None:return 'no-drive'
        if type(self.drive_bit) is not int or not 0<=self.drive_bit<192:return 'invalid-bit-disconnected'
        active=(not self.retired and self.token.live and not self.machine.native_inhibit
                and self.parent.stock>1)
        funded=min(dt,max(Q(0),(self.parent.stock-1)/NATIVE_POWER)) if active else Q(0)
        bit=self.drive_bit;sign=2*self.operand_bits[bit]-1
        target=self.binding.coordinates
        if funded:
            work=NATIVE_POWER*funded;need(self.parent.debit(work),'Native flow lacks actual parent work')
            self.drive_work+=work
            target[bit]=field.bit_flow(target[bit],external,sign*field.NATIVE_FORCE,funded,native_engaged=True)
        # Both force AND high mobility are disconnected without work/authority.
        if dt>funded:
            target[bit]=field.bit_flow(target[bit],external,Q(0),dt-funded,native_engaged=False)
        self.sync_target()
        return 'flowed' if funded else 'native-disconnected'

class SetterChild:
    """Actual immutable-operand child; literal payload plus paid control ticks."""
    def __init__(self,setter,token,args):
        self.setter=setter;self.token=token;self.args=args
        self.phase='entry';self.entry_remaining=2;self.control=0;self.cursor=0
        self.ticks=0;self.spent=Q(0);self.refill_input=Q(0)
        self.closed=False;self.done=False;self.result=None
        self.alias_read_open=True;self.abort_tail=None;self.abort_requested=False
        self.clock_enabled=True
        need(setter.issue(args)=='latched','Child admission did not capture')
        need(setter.parent_record is args,'Child copied or rebound parent operands')
    def tick(self,clock=True):
        if self.closed or not self.token.live:return 'retired'
        self.observe_abort()
        if not self.alias_read_open:return 'abort-draining'
        if not clock or not self.clock_enabled:return 'clock-wait'
        s=self.setter
        if s.native_inhibit:return 'inhibited-wait'
        if self.phase in ('refill','done'):return self.phase
        if self.phase=='entry':
            if s.energy<17:return 'unfunded-wait'
            s.energy-=16;self.spent+=16;self.ticks+=1
            if self.entry_remaining==2:self.cursor=0
            else:self.control=0
            self.entry_remaining-=1
            if self.entry_remaining==0:self.phase='payload'
            return 'entry-control'
        if self.phase=='payload':
            if s.generator is None and s.phase=='pending':return 'control-wait'
            old=s.energy;event=s.step();self.spent+=old-s.energy
            if event in ('unfunded-wait','inhibited-wait','retired-wait','wait'):return event
            if event!='recharging':
                self.ticks+=1;self.phase='cursor';return event
            self.phase='control';s.phase='control'
        if self.phase=='cursor' and self.cursor>=4095:return 'control-wait'
        if self.phase=='control' and self.control>=254:return 'control-wait'
        if s.energy<17:return 'unfunded-wait'
        s.energy-=16;self.spent+=16;self.ticks+=1
        if self.phase=='cursor':
            self.cursor+=1
            self.phase='payload'
        else:
            if self.control<12:self.cursor&=~(1<<self.control)
            self.control+=1
            if self.control==254:self.phase='refill';s.phase='recharging'
        return 'control'
    def recharge(self,dt):
        if self.closed:return 'retired'
        if self.phase!='refill':return 'busy'
        old=self.setter.energy;outcome=self.setter.recharge(dt)
        self.refill_input+=2*(self.setter.energy-old)
        if outcome=='done':
            self.result=bool(self.setter.returned);self.done=True;self.phase='done';self.alias_read_open=False
        return outcome
    def physical_completion(self):
        """Actual terminal child/alias/refill relation, never the done word.

        The exhausted generator denotes the native payload engine's terminal
        continuation. Ordinary counter/phase words alone cannot certify it.
        """
        s=self.setter
        return (isinstance(s.generator,GeneratorType) and s.generator.gi_frame is None
                and s.steps in (3584,3615) and self.control==254 and self.cursor==0
                and self.ticks==2*s.steps+256 and self.phase=='done'
                and s.phase=='ready' and s.energy==field.SET_ENERGY
                and not s.parent_live and s.parent_record is None and s.latched is None
                and type(s.returned) is bool)
    def observe_abort(self):
        # A real valid/read-enable or write-inhibit transition blocks further
        # alias reads. A forged clear cursor or returned bit alone proves none.
        if not self.setter.parent_live or self.setter.native_inhibit:
            self.alias_read_open=False;self.abort_requested=True
    def flow_abort_tail(self,dt):
        dt=exact(dt)
        if dt<0:raise ValueError('Negative child tail')
        self.observe_abort()
        if self.abort_tail is not None:self.abort_tail=max(Q(0),self.abort_tail-dt)
    def recognize_physical_abort(self,old_args):
        s=self.setter
        if (old_args is not self.args or s.parent_live or s.parent_record is not None
            or s.latched is not None or not s.native_inhibit
            or s.generator is not None or s.returned is not False
            or self.alias_read_open or self.abort_tail!=0):return 'child-not-closed'
        self.closed=True;self.done=False;return 'child-aborted'

@dataclass
class OrdinaryChild:
    name:str
    args:tuple
    result:object
    physical_ports:object
    return_consumed:bool=False

class RetirableParent(parent.ParentMachine):
    def __init__(self,isa,c,bank=None,body=None,targets=None):
        if bank is not None:
            if type(bank.capacity) is not int or bank.capacity<0 or not 0<=exact(bank.stock)<=bank.capacity:
                raise ValueError('Actual operating work exceeds its physical capacity')
        if body is not None and type(body) is not RoutedBody:raise ValueError('Actual routed body required')
        body=body if body is not None else RoutedBody(c)
        super().__init__(isa,c,bank,body)
        self.fabric=RouteFabric(self.cell,body);body.fabric=self.fabric
        self.setter=field.SettingWriter(tuple('fixed-target-'+str(i) for i in range(40)) if targets is None else targets)
        self.child=None;self.accepted_children=[];self.io_paid=False;self.io_args=None
        self.launch_inhibit=False;self.recharge_inhibit=False
        self.native_inhibit=False;self.offer_inhibit=False;self.return_inhibit=False
        self.capture_route_work=0;self.drive_work=Q(0);self.abort_count=0
        self.control_bits=[1]*CONTROL_BITS;self.parent_clear_index=0
        self.argument_slots=[parent.MASK]*5;self.destination_latch=0;self.returned_latch=0
        self.instruction_latch=0;self.captured_pc_latch=0
        self.io_strobe_word=0
    def recharge(self):
        if self.recharge_inhibit or self.pending is not None or self.fabric.token is not None:return False
        return super().recharge()
    def launch(self,funded=True):
        if self.launch_inhibit or self.pending is not None or not self.powered or self.halted:return False
        if not funded or self.cell.stock!=parent.PARENT:return False
        if not self.fabric.new_parent():return False
        self.cell.busy=True
        if not 0<=self.pc<len(self.C):
            self.cell.debit(16);self.cell.finish();self.fabric.normal_finish();self.halted=True
            self.nominal_work_time_upper+=Q(1,4*2**26)+Q(16)/parent.NATIVE_RATE
            self.rejected['invalid_pc']+=1;return False
        try:
            code=self._body.observe_word(self.pc)
            op,a,b,c,imm=self.isa.decode(code)
            indices=self.capture_indices(op,a,b,c,imm)
            operands=tuple((i,self._body.read_R(i)) for i in dict.fromkeys(indices) if 0<=i<len(self.R))
        except RouteWait:return False
        full=16+468+64+32+280*len(indices)
        need(self.cell.debit(full-self.fabric.front_work),'Capture leaf work unavailable')
        self.capture_route_work=self.fabric.front_work
        self.pending=parent.Capture(self._body,self.pc,code,operands,full)
        self.instruction_latch=code;self.captured_pc_latch=self.pc
        for j,(_index,value) in enumerate(operands):self.argument_slots[j]=value
        self.destination_latch=a
        self.child=None;self.io_paid=False;self.io_args=None
        return True
    def make_native_write(self,body,address,value,cell):
        return GuardedNative(self,body,address,value,cell)
    def finish_parent(self,extra_work,native=False):
        p=self.pending;need(p is not None,'Missing actual parent')
        if self.fabric.link_storage_busy():raise RouteWait('Old private return retains storage or tail')
        later_routes=self.fabric.front_work-self.capture_route_work
        remainder=parent.FRONT-p.launch_work-later_routes
        if remainder<0 or not self.cell.debit(remainder):raise RouteWait('Route work exceeded frontend allocation')
        native_steps=self.native.steps if self.native is not None else 0
        native_flow=self.native.drive_work if self.native is not None else Q(0)
        qualification=self.native.qualification_work if self.native is not None else Q(0)
        self.front_work+=parent.FRONT;self.body_work+=extra_work+native_flow
        self.max_total_work=max(self.max_total_work,parent.FRONT+extra_work+native_flow)
        self.cell.finish();self.fabric.normal_finish()
        self.pending=None;self.native=None;self.committing=False
        ordinary=Q(1,2**26)
        self.nominal_work_time_upper+=ordinary if not native else max(ordinary,ordinary/4+Q(parent.FRONT+qualification)/parent.NATIVE_RATE+Q(native_steps)/field.WORD_CLOCK)
        self.balance()
    def balance(self):
        need(self.bank.stock+self.cell.stock+self.cell.spent+self.cell.dumped==self.initial_bank,
             'Actual operating/parent work was created')
        self.fabric.link_balance()
        links=self.fabric.links+self.fabric.old_returns
        held_and_dissipated=sum((x[3].stock+x[3].dumped+x[3].spent for x in links),Q(0))
        need(self.bank.stock+self.cell.stock+self.cell.dumped+
             self.cell.spent-self.fabric.link_work_issued+held_and_dissipated==self.initial_bank,
             'Parent/link combined work was lost or counted twice')
    def _io_info(self):
        if self.pending is None:return None
        s=self.isa;op,a,b,c,imm=s.decode(self.pending.cell)
        if op!=s.IO or not 0<=imm<len(s.PRIMITIVES):return None
        name=s.PRIMITIVES[imm]
        if c!=s.PRIM_ARITY[name] or b+c>len(self.R):return None
        values=dict(self.pending.operands)
        return name,a,tuple(s.signed(values.get(i,0)) for i in range(b,b+c))
    def complete(self,ports,*,native_ticks=None,clock=True,pause_after_offer=False):
        if self.pending is None or self.committing:return False
        if not clock or self.return_inhibit:return 'waiting'
        info=self._io_info()
        if info is None:
            try:return super().complete(ports,native_ticks=native_ticks,clock=clock)
            except RouteWait:return 'waiting'
        name,dest,args=info;p=self.pending
        extra=(9184 if name in ('fast_cmp','fast_equal','fast_range') else
               12416 if name in ('source_idiv','source_imod') else
               326 if name in parent.program.FORBIDDEN else 4096)
        if not self.io_paid:
            if self.offer_inhibit or self.cell.stock<parent.FRONT-p.launch_work+extra:return 'waiting'
            if not self.fabric.offer(self.fabric.token):return 'waiting'
            need(self.cell.debit(extra),'IO admission lacks parent work')
            self.io_paid=True;self.io_args=args;self.io_counts[name]+=1;self.offers+=1
            self.io_strobe_word=self.isa.PRIM[name]|(len(args)<<8)
            self.committing=True
            if name=='set_field':
                s=self.setter
                if not s.cut and not s.native_inhibit and s.phase=='ready' and s.energy==field.SET_ENERGY:
                    self.child=SetterChild(s,self.fabric.token,args)
                else:self.child=OrdinaryChild(name,args,0,ports)
            elif name=='cpu_count':self.child=OrdinaryChild(name,args,None,ports)
            else:self.child=OrdinaryChild(name,args,ports.perform(name,args,self),ports)
            self.accepted_children.append(self.child);self.committing=False
            if pause_after_offer:return 'waiting'
        if isinstance(self.child,SetterChild):
            if not self.child.physical_completion():return 'waiting'
            result=self.child.result
        else:result=self.child.result
        # The ISA counter read observes the retirement of this instruction.
        # No counter update or result is published while a parent is blocked.
        if name=='cpu_count':result=(self.retired+1)%(1<<64)
        self.returned_latch=(0 if result is None else result)&parent.MASK
        if self.cell.stock<parent.FRONT-p.launch_work:return 'waiting'
        self.committing=True
        self.pc=p.address+1;self.retired=(self.retired+1)%(1<<64)
        self.steps+=1;self.word_work+=1;self.executed[self.isa.IO]+=1
        if 0<=dest<len(self.R):self._body.write_R(dest,(0 if result is None else result)&parent.MASK)
        if isinstance(self.child,OrdinaryChild):self.child.return_consumed=True
        if name=='yield_frame':self.yielded=True
        if name=='set_field':self.nominal_work_time_upper+=Q(1,64)
        ports.advance(self);self.finish_parent(extra);return True
    def step(self,ports):
        if self.pending is not None:return False
        if not self.recharge() or not self.launch():return False
        outcome=self.complete(ports)
        if outcome=='waiting' and isinstance(self.child,SetterChild):
            for _ in range(8193):
                event=self.child.tick()
                if event=='refill':break
                if event in ('unfunded-wait','inhibited-wait','retired','clock-wait','control-wait','abort-draining','wait'):return False
            self.child.recharge(field.SET_REFILL)
            outcome=self.complete(ports)
        return outcome is True
    def inhibit(self):
        # Actual physical cutset input. It also disconnects the high-mobility
        # path, not just the native controller clock or commanded force sign.
        self.launch_inhibit=True;self.recharge_inhibit=True
        self.native_inhibit=True;self.offer_inhibit=True;self.return_inhibit=True
        self.powered=False;self.fabric.inhibit();self.setter.cut=True
    def dump_parent(self,dt):
        dt=exact(dt)
        if dt<0:raise ValueError('Negative parent dump')
        if not (self.recharge_inhibit and self.native_inhibit and self.offer_inhibit and self.return_inhibit):
            return 'cutset-open'
        loss=min(max(Q(0),self.cell.stock-field.DUMP_FLOOR),Q(parent.PARENT)/PARENT_DUMP_TIME*dt)
        self.cell.stock-=loss;self.cell.dumped+=loss
        self.fabric.flow_links(dt);self.balance();return loss

def bitmap():
    fields=dict(captured_operands=1280,captured_instruction=192,captured_pc=14,
        result_destination=24,parent_phase=16,returned_word=256,architectural_pc=256,
        native_address_copy=256,native_operand_copy=192,native_index=12,
        native_address_order=2,native_acceptance=2,native_drive_bit=8,native_done=1,native_address_shadow=13,
        native_qualification_snapshot=256,native_qualification_nodes=parent.QUALIFICATION_NODE_BITS,native_qualification_valid=2,
        io_child_and_once_only_controls=64,root_token_route_controls=64,
        retired_instruction_counter=64)
    used=sum(fields.values());need(used<=CONTROL_BITS,'Parent reset bitmap exceeds physical allocation')
    return dict(fields=fields,used=used,padded=CONTROL_BITS,
        excluded=['C bit coordinates','architectural R/W data','inactive route/capture data overwritten at qualified entry',
                  'setter child operand bank, closed separately before parent operands','independent accepted ordinary children'])

class ControlView:
    """Fixed bit ports on existing CPU/native state, not another data copy."""
    def __init__(self,m):
        self.m=m;self.layout=[];start=0
        for name,width in bitmap()['fields'].items():
            self.layout.append((name,start,width));start+=width
        self.used=start
    def get(self,name):
        m=self.m;p=m.pending;n=m.native
        if name=='captured_operands':return sum(v<<(256*j) for j,v in enumerate(m.argument_slots))
        if name=='captured_instruction':return m.instruction_latch
        if name=='captured_pc':return m.captured_pc_latch
        if name=='result_destination':return m.destination_latch
        if name=='parent_phase':return int(m.committing)|(int(m.io_paid)<<1)|(int(m.cell.busy)<<2)|(int(m.halted)<<3)|(int(m.yielded)<<4)
        if name=='returned_word':return m.returned_latch
        if name=='architectural_pc':return m.pc&parent.MASK
        if name=='retired_instruction_counter':return m.retired
        if name=='io_child_and_once_only_controls':return m.io_strobe_word
        if name=='root_token_route_controls':return m.fabric.header
        if n is None:return 0
        if name=='native_address_copy':return sum(x<<j for j,x in enumerate(n.address_bits))
        if name=='native_operand_copy':return sum(x<<j for j,x in enumerate(n.operand_bits))
        if name=='native_index':return n.index
        if name=='native_address_order':return {-1:1,0:0,1:2}.get(n.address_order,3)
        if name=='native_acceptance':return 0 if n.accepted is None else 2 if n.accepted else 1
        if name=='native_drive_bit':return 0 if n.drive_bit is None else n.drive_bit+1
        if name=='native_done':return int(n.done)
        if name=='native_address_shadow':return 0 if n.target_address is None else n.target_address
        if name=='native_qualification_snapshot':return sum(x<<j for j,x in enumerate(n.qualification_bits))
        if name=='native_qualification_nodes':return sum(x<<j for j,x in enumerate(n.qualification_nodes))
        if name=='native_qualification_valid':return 0 if n.qualification_ok is None else 2 if n.qualification_ok else 1
        raise ValueError('Unknown fixed reset port')
    def put(self,name,value):
        m=self.m;p=m.pending;n=m.native
        if name=='captured_operands':
            m.argument_slots[:]=[(value>>(256*j))&parent.MASK for j in range(5)]
            if p is not None:m.pending=replace(p,operands=tuple((i,m.argument_slots[j]) for j,(i,_old) in enumerate(p.operands)))
            if m.io_args is not None:m.io_args=tuple(m.isa.signed(m.argument_slots[j]) for j in range(len(m.io_args)))
        elif name=='captured_instruction':
            m.instruction_latch=value
            if p is not None:m.pending=replace(p,cell=value)
        elif name=='captured_pc':
            m.captured_pc_latch=value
            if p is not None:m.pending=replace(p,address=value)
        elif name=='result_destination':m.destination_latch=value
        elif name=='parent_phase':
            m.committing=bool(value&1);m.io_paid=bool(value&2);m.cell.busy=bool(value&4)
            m.halted=bool(value&8);m.yielded=bool(value&16)
        elif name=='returned_word':m.returned_latch=value
        elif name=='architectural_pc':m.pc=value
        elif name=='retired_instruction_counter':m.retired=value
        elif name=='io_child_and_once_only_controls':m.io_strobe_word=value
        elif name=='root_token_route_controls':m.fabric.header=value
        elif n is not None:
            if name=='native_address_copy':n.address_bits[:]=[(value>>j)&1 for j in range(256)]
            elif name=='native_operand_copy':n.operand_bits[:]=[(value>>j)&1 for j in range(192)]
            elif name=='native_index':n.index=value
            elif name=='native_address_order':n.address_order={0:0,1:-1,2:1,3:0}[value]
            elif name=='native_acceptance':n.accepted={0:None,1:False,2:True,3:None}[value]
            elif name=='native_drive_bit':n.drive_bit=None if value==0 else value-1
            elif name=='native_done':n.done=bool(value)
            elif name=='native_address_shadow':n.target_address=value
            elif name=='native_qualification_snapshot':n.qualification_bits[:]=[(value>>j)&1 for j in range(256)]
            elif name=='native_qualification_nodes':n.qualification_nodes[:]=[(value>>j)&1 for j in range(parent.QUALIFICATION_NODE_BITS)]
            elif name=='native_qualification_valid':n.qualification_ok={0:None,1:False,2:True,3:None}[value]
    def clear(self,index):
        if type(index) is not int or not 0<=index<CONTROL_BITS:raise ValueError('Invalid physical reset bit')
        for name,start,width in self.layout:
            if start<=index<start+width:
                self.put(name,self.get(name)&~(1<<(index-start)));break
        self.m.control_bits[index]=0
    def all_zero(self):return all(self.get(name)==0 for name,_start,_width in self.layout)

class ParentRetirement:
    """Independently paid child-first retirement over the actual machine."""
    def __init__(self,machine):
        if type(machine) is not RetirableParent:raise ValueError('Actual retirable parent required')
        self.m=machine;self.reserve=machine.setter.reset_reserve
        self.capture=machine.pending;self.token=machine.fabric.token;self.native=machine.native
        self.child=machine.child;self.done=False;self.spent=Q(0);self.phase=Q(0)
        self.index=0;self.overhead_paid=False
        self.tail_funded=False
        self.view=ControlView(machine)
        self.setup_remaining=Q(1,256);self.terminal_remaining=Q(1,256)
    def pay(self,amount):
        if not self.reserve.debit(amount):return False
        self.spent+=amount;return True
    def child_closed(self):
        if isinstance(self.child,SetterChild):
            if self.child.physical_completion():
                self.child.closed=True;return True
            return self.child.recognize_physical_abort(self.child.args)=='child-aborted'
        return True
    def advance(self,dt):
        dt=exact(dt)
        if dt<0:raise ValueError('Negative retirement time')
        if self.done:return 'already-consumed'
        m=self.m
        if not (m.launch_inhibit and m.recharge_inhibit and m.native_inhibit and m.offer_inhibit and m.return_inhibit):
            return 'inhibition-required'
        if m.cell.stock>field.DUMP_FLOOR or m.fabric.link_storage_busy():return 'drain-wait'
        if isinstance(self.child,SetterChild) and not self.child.physical_completion():
            self.child.observe_abort()
            if not self.child.abort_requested:return 'child-wait'
            if not self.tail_funded:
                if not self.pay(512):return 'reset-work-wait'
                self.tail_funded=True;self.child.abort_tail=Q(1,64)
            used=min(dt,self.child.abort_tail)
            self.child.flow_abort_tail(used);dt-=used
        if not self.child_closed():return 'child-wait'
        if not self.overhead_paid:
            overhead=ceil(Q(CONTROL_BITS-1,2))+1409-(512 if self.tail_funded else 0)
            if not self.pay(overhead):return 'reset-work-wait'
            self.overhead_paid=True
        used=min(dt,self.setup_remaining);self.setup_remaining-=used;dt-=used
        if self.setup_remaining:return 'setting-up'
        edges,self.phase=cam.clock_opportunities(self.phase,dt)
        remaining_bits=CONTROL_BITS-self.index
        used_edges=min(edges,remaining_bits)
        for _ in range(min(edges,CONTROL_BITS-self.index)):
            if not self.pay(2):return 'reset-work-wait'
            self.view.clear(self.index);self.index+=1
        if self.index<CONTROL_BITS:return 'clearing'
        # Completion/descriptor release uses later control time, never the
        # same elapsed interval again. Phase credit remains bounded.
        leftover=max(Q(0),dt-Q(used_edges,2**20))
        used=min(leftover,self.terminal_remaining);self.terminal_remaining-=used
        if self.terminal_remaining:return 'closing'
        token_outcome=m.fabric.consume()
        if token_outcome!='consumed':return token_outcome
        if self.native is not None:self.native.retired=True;self.native.drive_bit=None
        if isinstance(self.child,OrdinaryChild):self.child.return_consumed=True
        # Physical descriptor consumption follows child closure and full clear.
        m.pending=None;m.native=None;m.child=None;m.committing=False;m.io_args=None
        m.cell.busy=False;m.abort_count+=int(self.capture is not None)
        self.done=True;m.balance();return 'retired'
    def fresh_entry(self):
        m=self.m
        if not self.done:return 'retirement-required'
        # Actual later power/entry contact. It is not permission to assume C=P.
        m.reset_entry();m.fabric.cut=False;m.fabric.return_cut=False
        m.launch_inhibit=False;m.recharge_inhibit=False;m.native_inhibit=False
        m.offer_inhibit=False;m.return_inhibit=False;m.powered=True
        return 'fresh-entry'

class JoinedCam(cam.CamBank):
    """The existing field cam, same setter/reset cell, plus CPU retirement."""
    def __init__(self,machine,**kwargs):
        self.machine=machine;machine.inhibit()
        pulse=field.PulseSelector(slots=[[1,field.PULSE_COUNTER_CAP],None,None],force=field.FORCE)
        native=machine.native
        address=native.address if native is not None and native.target is not None else 0
        coords=(list(native.target) if native is not None and native.target is not None else
                [Q(2*((machine.C[address]>>j)&1)-1) for j in range(192)])
        resident=cam.ResidentWord('actual-cpu-body',0,address,coords,('resident-cpu-parent',address))
        super().__init__(pulse,machine.setter,resident,**kwargs)
        self.retirement=ParentRetirement(machine)
        self.child_phase=Q(0);self.cpu_clear_slot=Q(0);self.early_abort_observations=[]
    def _arrive(self,code):
        super()._arrive(code)
        if code==0:
            # A real fresh CUT closes the stale scheduling episode. Preserve
            # every paid clear step/parent, but begin the later cam-slot budget
            # from this entry instead of banking an old failed mode8 wait.
            self.cpu_clear_slot=Q(0)
    def _child_flow(self,dt):
        child=self.machine.child
        if not isinstance(child,SetterChild) or child.closed or child.physical_completion():return
        child.observe_abort()
        if not child.alias_read_open:return
        before_spent=child.spent;before_input=child.refill_input
        edges,self.child_phase=cam.clock_opportunities(self.child_phase,dt)
        used=0
        for _ in range(min(edges,8193)):
            event=child.tick();used+=1
            if event in ('unfunded-wait','inhibited-wait','abort-draining','retired','clock-wait','control-wait','wait'):break
            if event=='refill':
                # Only remaining real flow time can recharge the same child.
                remaining=max(Q(0),dt-Q(used,2**20));child.recharge(remaining);break
        self.setter_spent+=child.spent-before_spent
        self.setter_delivered+=(child.refill_input-before_input)/2
    def _consume(self,dt):
        dt=exact(dt);self._child_flow(dt)
        if self.mode==4:self.machine.dump_parent(dt)
        if self.mode==8 and not self.retirement.done:
            # Hold off THIS shared reset recharge while CPU cleanup spends it.
            # The remaining>100000q idle interval supplies the full refill.
            active=min(dt,max(Q(0),Q(1,32)-self.cpu_clear_slot))
            if active:
                old_cap=self.s.reset_reserve.input_cap;self.s.reset_reserve.input_cap=Q(0)
                self.retirement.advance(active)
                super()._consume(active)
                self.s.reset_reserve.input_cap=old_cap;self.cpu_clear_slot+=active;dt-=active
            if not self.retirement.done:
                old_cap=self.s.reset_reserve.input_cap;self.s.reset_reserve.input_cap=Q(0)
                self.retirement.advance(dt);super()._consume(dt);self.s.reset_reserve.input_cap=old_cap
                dt=Q(0)
        if dt:super()._consume(dt)
        child=self.machine.child
        if isinstance(child,SetterChild):
            child.observe_abort()
            if child.abort_requested and self.q<cam.BANDS[6]['left']:
                self.early_abort_observations.append(dict(time=self.time,clamp=self.q,
                    alias_read_open=child.alias_read_open,parent_retained=self.machine.pending is self.retirement.capture,
                    child_closed=child.closed,tail=child.abort_tail))
    def certificate(self):return super().certificate() and self.retirement.done and self.retirement.view.all_zero()
    def activation_to(self,to_position,duration):
        before=self.activation;outcome=super().activation_to(to_position,duration)
        if before<cam.POWER<=self.activation:self.retirement.fresh_entry()
        return outcome

def make_machine(isa,c,Ports,kind='set_field',*,starved=False):
    m=RetirableParent(isa,c);ports=Ports(c)
    if kind=='set_field':
        m.C[0]=isa.encode(isa.IO,2,3,4,isa.PRIM['set_field'])
        m.R[3:7]=[0,0,9,1]
    elif kind=='native':
        m.C[0]=isa.encode(isa.STOREC,3,4);m.R[3]=(1<<192)-1;m.R[4]=100;m.C[100]=0
    else:
        m.C[0]=isa.encode(isa.IO,2,3,2,isa.PRIM['world']);m.R[3:5]=[(-100)&parent.MASK]*2
    need(m.recharge() and m.launch(),'Actual parent capture failed')
    if kind=='native':need(m.complete(ports,native_ticks=705)=='waiting','Native parent did not pause')
    else:need(m.complete(ports,pause_after_offer=True)=='waiting','Actual child offer did not block parent')
    m.test_link=m.fabric.retain_link(123)
    need(type(m.test_link) is list,'Old physically paid link was not captured')
    if starved:
        if isinstance(m.child,SetterChild):
            for _ in range(20):m.child.tick()
            loss=m.setter.energy-17;m.setter.energy-=loss;m.child.spent+=loss
        else:m.cell.debit(m.cell.stock-1)
    return m,ports

def checks(isa,c,Ports):
    rows=[]
    for kind,starved in (('native',False),('native',True),('set_field',False),('set_field',True),('world',False)):
        m,ports=make_machine(isa,c,Ports,kind,starved=starved)
        original=m.pending;native=m.native;old_child=m.child
        before_C=list(m.C);before_W=list(m.W);before_R=list(m.R)
        if native is not None:
            before=native.target[native.drive_bit]
            native.flow(Q(1,2**30))
            need(starved or native.target[native.drive_bit]!=before,'Clock stop was mistaken for frozen C')
            before_C=list(m.C)
        token=m.fabric.token;link=m.test_link
        controller=JoinedCam(m)
        need(controller.s.reset_reserve is m.setter.reset_reserve,'Shared reset store was copied')
        need(not m.recharge() and not m.launch() and m.complete(ports)=='waiting','Cut did not stop parent/offer/recharge')
        controller.advance(cam.PREPARED_AT,cam.PREPARED_AT/cam.VMAX)
        controller.advance(cam.PREPARED_AT,cam.CONTROL_DELAY)
        need(controller.certificate(),'Joint field/CPU reformation failed')
        prepared_time=controller.time
        need(m.pending is None and not token.live and m.fabric.return_effect(link)=='inert-old-return',
             'Old parent/route remained rearmable')
        need(m.C==before_C and m.W==before_W and m.R==before_R,'Retirement rewrote C or architectural data')
        if kind=='world':need(ports.world_latch==(-100,-100),'Parent reset erased an accepted ordinary effect')
        if isinstance(old_child,SetterChild):
            held=dict(m.setter.held)
            need(old_child.tick()=='retired' and m.setter.held==held,'Retired child resumed on the reused stock')
        old_spent=controller.s.reset_reserve.spent
        need(controller.retirement.advance(1)=='already-consumed' and controller.s.reset_reserve.spent==old_spent,
             'Descriptor retirement replayed')
        controller.activation_to(cam.POWER,cam.POWER/cam.VMAX)
        need(m.pc==0 and m.pending is None and not m.return_inhibit,'Actual fresh entry failed')
        need(m.recharge(),'Fresh physical parent did not recharge')
        if native is not None:need(native.step()=='retired','New parent work rearmed an old native handle')
        m.balance();controller.conservation()
        rows.append(dict(kind=kind,starved=starved,retired_once=m.abort_count,
            CPU_reset_work=controller.retirement.spent,shared_reset_spent=old_spent,
            parent_dumped=m.cell.dumped,actual_prepared_time=prepared_time,
            C_and_RW_preserved=True,ordinary_effect_preserved=kind=='world'))
    # Valid stale mode7 and a forged finished clear cursor: an abort request
    # may occur early, but it cannot close the actual CPU argument ownership.
    m,ports=make_machine(isa,c,Ports,'set_field')
    for _ in range(20):m.child.tick()
    m.child.clock_enabled=False
    saved_setting=field.Destination(m.setter.targets[1],1,13)
    m.setter.held[saved_setting]=-1
    args=m.child.args;capture=m.pending
    m.setter.reset_reserve.charge(100000)
    ghost=JoinedCam(m,control_words=[7]*8,control_valid=[True]*8,controller_residue=4096<<11)
    ghost.advance(Q(1),Q(1))
    need(ghost.early_abort_observations and m.pending is capture and m.io_args is args,
         'Early controller abort erased CPU alias ownership')
    need(not m.child.alias_read_open and not m.child.closed and not ghost.retirement.done,
         'Corrupt clear cursor was mistaken for native child quiescence')
    need(m.setter.held[saved_setting]==-1,'Early abort erased an already applied setting')
    ghost.advance(cam.PREPARED_AT,(cam.PREPARED_AT-ghost.q)/cam.VMAX)
    ghost.advance(cam.PREPARED_AT,cam.CONTROL_DELAY)
    need(ghost.certificate(),'Correct CUT/clear did not recover the early-abort state')
    # A new energized token overwrites stale local metadata before use; the
    # unvisited state remains arbitrary. No whole-array reset is performed.
    simple=RetirableParent(isa,c);pp=Ports(c);simple.C[0]=isa.encode(isa.LI,3,0,0,7)
    stale=RouteNode(header=(1<<128)-1,busy=True,return_claim=token)
    simple.fabric.nodes[('C',0)]=stale
    need(simple.step(pp) and simple.R[3]==7 and stale.visits==1 and stale.return_claim is None,
         'Stale node state blocked or redirected a fresh physical arrival')
    # Execute the real current-C scanner through the qualified parent/child.
    scanner=RetirableParent(isa,c);sp=Ports(c);scanner.enter('refresh_fields')
    limit=parent.program.bounds(isa,c)['instruction_upper_bounds']['refresh_fields']+10
    need(scanner.run(sp,limit,until_yield=False)=='halt','Actual scanner failed through live setter children')
    need(scanner.io_counts['set_field']==7 and len(scanner.setter.held)==7,'Scanner did not use actual setters')
    scanner.balance()
    return dict(retirement_cases=rows,early_mode7_probe=dict(count=len(ghost.early_abort_observations),
            first=ghost.early_abort_observations[0],last=ghost.early_abort_observations[-1]),
        early_mode7_CPU_alias_preserved=True,stale_node_priority_entry=True,
        scanner_instructions=scanner.steps,scanner_actual_setter_offers=scanner.io_counts['set_field'],
        full_paced_frame_executed=False)

def correspondence_checks(isa,c,Ports):
    count=0
    for op in range(0,26):
        for x,y in ((0,0),(1,2),(parent.MASK,1),(1,parent.MASK),(2**255,parent.MASK),(8191,8192)):
            m=RetirableParent(isa,c);ref=parent.program.initialized(isa,c)
            a=Ports(c);b=Ports(c)
            for machine in (m,ref):
                machine.C[0]=isa.encode(op,3,4,5,0);machine.C[1]=isa.encode(isa.HALT)
                machine.R[3]=x;machine.R[4]=y;machine.R[5]=x;machine.R[1]=x
                machine.W[0]=7;machine.W[31]=9
            need(m.step(a)==ref.step(b) and parent.snapshot(m)==parent.snapshot(ref),
                 'Qualified token parent changed an ordinary opcode: '+str((op,x,y)))
            m.balance();count+=1
    io_count=0
    for name in isa.PRIMITIVES:
        arity=isa.PRIM_ARITY[name]
        m=RetirableParent(isa,c);ref=parent.program.initialized(isa,c)
        a=Ports(c);b=Ports(c)
        args=(0,0,0,1) if name=='set_field' else (0,)*arity
        for machine in (m,ref):
            machine.C[0]=isa.encode(isa.IO,2,3,arity,isa.PRIM[name])
            machine.R[3:3+arity]=list(args)
        need(m.step(a)==ref.step(b) and parent.snapshot(m)==parent.snapshot(ref),
             'Qualified parent changed IO semantics: '+name)
        if name!='set_field':need(a.events==b.events and a.I==b.I,'Ordinary accepted effects differ')
        m.balance();io_count+=1
    return dict(ordinary_cases=count,IO_cases=io_count,includes_cpu_count_commit_semantics=True,
                includes_actual_setter_completion=True)

def boundary_checks(isa,c,Ports):
    m,ports=make_machine(isa,c,Ports,'set_field',starved=True)
    old=m.pending;m.cell.busy=False
    need(not m.recharge() and m.pending is old,'A forged busy bit minted root work')
    old_bank=m.bank.stock
    controller=JoinedCam(m,reset_charging=False)
    controller.advance(cam.PREPARED_AT,cam.PREPARED_AT/cam.VMAX)
    controller.advance(cam.PREPARED_AT,cam.CONTROL_DELAY)
    need(not controller.certificate() and not controller.retirement.done
         and m.pending is old and m.bank.stock==old_bank,'Unfunded maintenance silently retired the parent')
    partial=m.C[:];need(controller.retirement.fresh_entry()=='retirement-required' and m.C==partial,
                        'Failed retirement rearmed the processor')
    n=RetirableParent(isa,c);np=Ports(c)
    n.C[0]=isa.encode(isa.STOREC,3,4);n.R[3]=parent.MASK;n.R[4]=100;n.C[100]=0;n.C[101]=0
    n.recharge();n.launch();n.complete(np,native_ticks=256)
    n.native.address_bits[:]=[(101>>j)&1 for j in range(256)]  # Explicit address-copy fault.
    need(n.complete(np) is True and n.C[100]==0 and n.C[101]==(1<<192)-1,
         'Actual selected native word was hidden by the requested-address cache')
    q=RetirableParent(isa,c);qp=Ports(c)
    q.C[0]=isa.encode(isa.STOREC,3,4);q.R[3]=1;q.R[4]=20;q.recharge();q.launch()
    q.native=q.make_native_write(q._body,20,1,q.cell);q.native.index=704
    need(q.complete(qp)=='waiting' and q.pending is not None,'Unformed native selector caused an undefined effect')
    bad=0
    for action in (lambda:RetirableParent(isa,c,targets=()),
                   lambda:RetirableParent(isa,c,bank=parent.BankWork(10,Q(11))),
                   lambda:cam.clock_opportunities(True,1),
                   lambda:controller.retirement.advance(-1)):
        try:action()
        except (ValueError,AssertionError):bad+=1
        else:raise AssertionError('Malformed physical constructor was accepted')
    return dict(forged_busy_cannot_recharge=True,unfunded_parent_retained=True,
        failed_cleanup_does_not_rearm=True,actual_native_address_fault_observed=True,
        unformed_native_phase_waits=True,malformed_rejected=bad)

def repair_checks(isa,c,Ports):
    # A bounded poisoned comparison residue cannot route beyond8191.
    a=RetirableParent(isa,c);ap=Ports(c)
    a.C[0]=isa.encode(isa.STOREC,3,4);a.R[3]=1;a.R[4]=100
    a.recharge();a.launch();a.native=a.make_native_write(a._body,100,1,a.cell)
    bad_native=a.native;bad_native.index=511;bad_native.address_order=-1
    bad_native.address_bits[:]=[(8192>>j)&1 for j in range(256)]
    before=a.C[:]
    rejected=a.complete(ap,native_ticks=1)
    need(rejected is True and bad_native.accepted is False and bad_native.binding is None
         and a.C==before,'Bounded invalid native route did not reject without a write')
    a.balance()
    # Once selected, the physical word stays bound despite a changed shadow.
    b=RetirableParent(isa,c);bp=Ports(c)
    b.C[0]=isa.encode(isa.STOREC,3,4);b.R[3]=parent.MASK;b.R[4]=100;b.C[100]=0;b.C[101]=0
    b.recharge();b.launch();b.complete(bp,native_ticks=705)
    native=b.native;bound=native.binding;native.target_address=101
    need(b.complete(bp,native_ticks=1)=='waiting' and native.binding is bound
         and bound.address==100,'A mutable shadow rebound the native target')
    native.flow(Q(1,2**30))
    need(b.C[100]!=0 and b.C[101]==0 and bound.coordinates is b._body.physical[100],
         'Physical coordinates and word observation diverged')
    b.balance()
    # Forged completion cannot release a live aliased child, even with work.
    m,mp=make_machine(isa,c,Ports,'set_field')
    child=m.child;capture=m.pending;args=m.io_args
    m.inhibit();m.dump_parent(100);m.setter.reset_reserve.charge(100000)
    child.done=True
    retirement=ParentRetirement(m);outcome=retirement.advance(1)
    need(outcome=='child-wait' and not retirement.done and m.pending is capture
         and m.io_args is args and m.setter.parent_live and child.alias_read_open,
         'Forged child.done released a live CPU operand owner')
    # The same residue on a stale refill mode cannot bypass actual closure.
    j,jp=make_machine(isa,c,Ports,'set_field')
    j.inhibit();j.dump_parent(100);j.setter.reset_reserve.charge(100000)
    live=j.child;live.done=True;live.clock_enabled=False;owner=j.pending;operand=j.io_args
    joined=JoinedCam(j,control_words=[8]*8,control_valid=[True]*8)
    joined.advance(Q(0),Q(1,32))
    need(not joined.retirement.done and j.pending is owner and j.io_args is operand
         and j.setter.parent_live and live.alias_read_open,
         'Stale mode8 plus forged done cleared live operands')
    # A subsequent genuine cut/sweep can close the same retained child.
    joined.advance(cam.PREPARED_AT,cam.PREPARED_AT/cam.VMAX)
    joined.advance(cam.PREPARED_AT,cam.CONTROL_DELAY)
    need(joined.certificate(),'Real child cutoff/tail did not recover the forged-done state')
    joined.conservation();j.balance()
    # Conversely, a false diagnostic done word does not suppress an actual
    # completed native engine and full-refill return relation.
    good=RetirableParent(isa,c);gp=Ports(c)
    good.C[0]=isa.encode(isa.IO,2,3,4,isa.PRIM['set_field']);good.R[3:7]=[0,0,0,1]
    good.recharge();good.launch();good.complete(gp,pause_after_offer=True)
    while good.child.phase!='refill':good.child.tick()
    good.child.recharge(field.SET_REFILL);good.child.done=False
    need(good.child.physical_completion() and good.complete(gp) is True,
         'An untrusted diagnostic done word replaced the actual completion relation')
    good.balance()
    # Dead authority at one work unit does not imply an empty link slot.
    r=RetirableParent(isa,c);r.C[0]=isa.encode(isa.LI,3,0,0,7)
    r.recharge();r.launch();old=r.fabric.retain_link(11)
    r.fabric.flow_links(Q(19,20));stock=r.cell.stock;issued=r.fabric.link_work_issued
    need(old[3].stock==1 and old[2]==Q(1,20) and r.fabric.return_effect(old)=='inert-old-return',
         'Missing dead-authority/positive-storage boundary')
    need(r.fabric.retain_link(22)=='link-busy' and r.cell.stock==stock
         and r.fabric.link_work_issued==issued and r.fabric.links[0] is old,
         'Reuse dropped positive residual work or charged another link')
    try:r.fabric.normal_finish()
    except RouteWait:pass
    else:raise AssertionError('Normal finish freed a positive residual link')
    r.fabric.flow_links(Q(1,20));new=r.fabric.retain_link(22)
    need(type(new) is list and new is not old and old in r.fabric.old_returns
         and old[3].stock==0 and old[3].dumped==20 and new[3].stock==20,
         'Actual drain/archive/reuse lost a physical compartment')
    r.balance()
    return dict(invalid_native_address8192='paid reject, no write',
        target_shadow101_retains_physical_word100=True,
        forged_done_standalone=outcome,forged_done_stale_mode8_blocks_reuse=True,
        actual_completion_ignores_false_diagnostic_done=True,
        forged_done_recovers_only_after_actual_cut_tail_clear=True,
        residual_link_work_before_drain=1,residual_link_tail=Q(1,20),
        residual_blocks_reuse_and_finish=True,actual_link_dissipation=20,
        combined_parent_and_link_conservation=True)

def resource_checks():
    source=json.loads((HERE/'cam_reformation_results.json').read_text(encoding='utf-8-sig'))['arithmetic']
    need(RESET_WORK==11649 and RESET_WORK+SETTER_RESET_WORK+1<field.SETTER_RESET_ENERGY,
         'The one shared reset cell is overspent')
    clear_time=Q(12288,2**20)
    need(clear_time<CPU_CLEAR_TIME,'Complete CPU clear/return controller is too slow')
    final=cam.BANDS[-1]['minimum_dwell']-cam.CONTROL_DELAY
    need(final-Q(1,32)>100000,'CPU cleanup consumes the idle full-refill interval')
    # These bits belong to the cold parent/engine, not the keeper or all nodes.
    need(bitmap()['used']<=CONTROL_BITS,'Actual bitmap does not fit')
    remaining=Q(source['resources']['usable_reserve_lower'])
    need(remaining>1,'Current common reserve is unavailable')
    pcost=parent.cost_bounds()
    old=json.loads((HERE/'legacy_realization_results.json').read_text(encoding='utf-8-sig'))['inventory']
    _src,core,_ports,fpoint,_bindings,_text=parent.legacy.inputs()
    # Dedicated cold-side reset/fanout controls are added conservatively; the
    # reset bitmap itself is existing parent/native state, not new C storage.
    added_bits=2*CONTROL_BITS
    bank_rate=Q(pcost['new_actual_bank_rate_upper'])+Q(added_bits,2048)
    external_rate=Q(pcost['new_external_owner_rate_upper'])+added_bits*Q(core['background_clock_rate'])+Q(added_bits,1024)
    need(pcost['old_metadata_slack_after_route']>=added_bits
         and bank_rate<=Q(old['retained_downrated_bank_allowance'])
         and external_rate<=Q(core['external_rate']),'Reset control work/holding lacks its actual old owner row')
    added_reaction=2*field.U_BIT/1000
    complete_reaction=Q(source['resources']['complete_joint_reaction'])+added_reaction
    need(complete_reaction<field.REACTION,'Actual parent cut poles exceed the retained mechanical bound')
    speed=field.BIT_SPEED+22*Q(fpoint['point']['mechanics']['W_over_tau'])+cam.VMAX
    needed_power=field.NATIVE_FORCE*speed
    need(needed_power<NATIVE_POWER,'Stopped native drive has unpaid physical power')
    nominal_flow=NATIVE_POWER*Q(2080,field.WORD_CLOCK)
    need(nominal_flow<1 and 16641+parent.QUALIFICATION_WORK+parent.FRONT+1<parent.PARENT,
         'Qualified native flow loses the existing parent capacity')
    return dict(parent_control_bits=bitmap()['used'],padded_parent_control_bits=CONTROL_BITS,
        CPU_reset_work=RESET_WORK,existing_setter_reset_work=SETTER_RESET_WORK,
        combined_shared_reset_work=RESET_WORK+SETTER_RESET_WORK,
        one_actual_reset_capacity=field.SETTER_RESET_ENERGY,
        reset_capacity_margin=field.SETTER_RESET_ENERGY-RESET_WORK-SETTER_RESET_WORK,
        CPU_complete_control_time=clear_time,CPU_clear_allocation=CPU_CLEAR_TIME,
        alias_tail_and_CPU_slot=Q(1,32),final_idle_refill_slack=final-Q(1,32)-100000,
        unchanged_cam_prepared_upper=Q(source['physical_prepared_upper']),
        unchanged_U_capacity=Q(source['resources']['unchanged_upstream_capacity']),
        inherited_reserve_lower=remaining,new_reset_capacity=0,new_reset_charger_cap=0,
        added_reset_fanout_control_bits=added_bits,
        updated_actual_bank_rate=bank_rate,updated_external_owner_rate=external_rate,
        old_external_rate_slack=Q(core['external_rate'])-external_rate,
        old_metadata_slack=pcost['old_metadata_slack_after_route']-added_bits,
        added_parent_gate_reaction=added_reaction,complete_joint_reaction=complete_reaction,
        gate_work_over_full_cut=added_reaction*60000,
        native_drive_power=NATIVE_POWER,native_drive_required_power=needed_power,
        nominal_additional_native_flow_work=nominal_flow,qualified_native_parent_upper=16641+parent.QUALIFICATION_WORK+parent.FRONT+1,
        reset_rate_paid_by_existing_installed_shared_charger=True,
        all_node_reset_required=False,token_entry_and_return_cutset_are_explicit_source_laws=True)

def serial(x):
    if isinstance(x,Q):return str(x)
    if isinstance(x,dict):return {str(k):serial(v) for k,v in x.items()}
    if isinstance(x,(tuple,list)):return [serial(v) for v in x]
    return x

def source_inputs():
    isa=parent.program.load_isa();compiled=parent.program.compile_program(isa,parent.design.design(isa))
    return isa,compiled,parent.legacy.absence_ports_class(isa)

def generate():
    need(not sys.flags.optimize and sys.version_info[:2]==(3,12),'Unoptimized Python3.12 required')
    for name in ('parent_realization_results.json','threshold_field_source_results.json',
                 'cam_reformation_results.json','legacy_realization_results.json'):
        record=json.loads((HERE/name).read_text(encoding='utf-8-sig'))
        for source,expected in record['sources_sha256_lf'].items():
            need(parent.program.digest(HERE/source)==expected,'Current supplier binding differs: '+source)
    isa,c,Ports=source_inputs()
    return serial(dict(scope='candidate paid token/child/parent retirement construction',base=BASE,
        reset_bitmap=bitmap(),checks=checks(isa,c,Ports),correspondence=correspondence_checks(isa,c,Ports),
        boundaries=boundary_checks(isa,c,Ports),repairs=repair_checks(isa,c,Ports),resources=resource_checks(),
        sources_sha256_lf={n:sha256((HERE/n).read_text(encoding='utf-8-sig').replace('\r\n','\n').encode()).hexdigest()
            for n in ('PARENT-RETIREMENT.md','parent_retirement.py','PARENT-REALIZATION.md','parent_realization.py',
                      'parent_realization_results.json','threshold_field_source.py','threshold_field_source_results.json',
                      'cam_reformation.py','cam_reformation_results.json','legacy_realization.py','legacy_realization_results.json')},
        full_source_admitted=False,program_completion=False))

def main():
    parser=argparse.ArgumentParser(description=__doc__);g=parser.add_mutually_exclusive_group(required=True)
    g.add_argument('--write',action='store_true');g.add_argument('--check',action='store_true');args=parser.parse_args()
    result=generate();path=HERE/'parent_retirement_results.json'
    if args.write:path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n',encoding='utf-8',newline='\n')
    else:need(json.loads(path.read_text(encoding='utf-8-sig'))==result,'Parent retirement binding differs')
    print('PASS candidate paid parent retirement; source and interrupted-state admission remain open')

if __name__=='__main__':main()

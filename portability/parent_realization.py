"""Finite paid ordinary-ISA parent leaf and qualified source refinement.

Fixed local transition/cost laws, executable correspondence checks, and retained
native partial effects. This is not a full physical-source or recurrent theorem.
"""
from __future__ import annotations
import argparse
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import random
import sys
import threshold_program_model as program
import threshold_design as design
import legacy_realization as legacy
import threshold_field_source as field

HERE=Path(__file__).resolve().parent
BASE="dce234d340bc68d9621654658a52ac2593596c96"
MASK=(1<<256)-1
LIMB=(1<<64)-1
PARENT=20480
FRONT=2816
NATIVE_RATE=F(4,3)*16384*2**27
DELTA=F(1,2**30)
need=program.need

def limbs(value):
    return [(value>>(64*j))&LIMB for j in range(4)]

def word(values):
    return sum(v<<(64*j) for j,v in enumerate(values))&MASK

def negate(values):
    out=[];carry=1
    for value in values:
        t=(value^LIMB)+carry
        out.append(t&LIMB);carry=t>>64
    return out

def plus_one(values):
    out=[];carry=1
    for value in values:
        t=value+carry
        out.append(t&LIMB);carry=t>>64
    return out

def subtract(left,right):
    out=[];borrow=0
    for a,b in zip(left,right):
        t=a-b-borrow
        out.append(t&LIMB);borrow=int(t<0)
    return out,borrow

def unsigned_divide(left,right):
    """256 fixed restoring rounds over four native64 registers.

    SBB64 returns a64-bit word and its one carry/borrow flag; native shifts,
    selects and fixed-register transfers have the declared local unit price.
    The32-operation round allowance includes bit selection and finite control.
    """
    a=limbs(left);b=limbs(right)
    if not any(b):return 0,0,128
    r=[0]*4;q=[0]*4
    for index in range(255,-1,-1):
        incoming=(a[index//64]>>(index%64))&1
        for j in range(4):
            high=r[j]>>63
            r[j]=((r[j]<<1)&LIMB)|incoming
            incoming=high
        trial,borrow=subtract(r,b)
        take=bool(incoming or not borrow)
        for j in range(4):r[j]=trial[j] if take else r[j]
        if take:q[index//64]|=1<<(index%64)
    return word(q),word(r),8320

def signed_divmod(a,b):
    """Python/frozen-ISA floor convention, including zero and wraparound."""
    sa=bool(a>>255);sb=bool(b>>255)
    aa=word(negate(limbs(a))) if sa else a
    bb=word(negate(limbs(b))) if sb else b
    q,r,cost=unsigned_divide(aa,bb)
    if bb==0:return 0,0,cost
    if sa!=sb:
        if r:
            q=word(negate(plus_one(limbs(q))))
            r=word(subtract(limbs(bb),limbs(r))[0])
        else:q=word(negate(limbs(q)))
    if sb:r=word(negate(limbs(r)))
    return q,r,cost

def multiply_limbs(a,b):
    left=limbs(a);right=limbs(b);out=[0]*4
    for i in range(4):
        carry=0
        for j in range(4-i):
            product=left[i]*right[j]  # MULLO64/MULHI64, two native operations.
            total=out[i+j]+(product&LIMB)+carry
            out[i+j]=total&LIMB
            carry=(product>>64)+(total>>64)
            need(carry<=LIMB,"Native multiplication carry overflow")
    return word(out)

def routed_index(address,depth):
    """One active fixed path; no data-selected origin or global search."""
    need(type(address) is int and 0<=address<1<<depth,"Unrouted address")
    node=0;leaf=0;work=0
    for bit in range(depth-1,-1,-1):
        direction=(address>>bit)&1
        node=2*node+1+direction
        leaf=(leaf<<1)|direction
        # Eight forward/token operations, eight limb transfers, four return/
        # scrub operations. This is the declared local hop-transition leaf.
        work+=20
    need(leaf==address and node==(1<<depth)-1+address,"Physical path aliases")
    return leaf,work

def route_checks():
    cases=0
    for depth in (3,13):
        seen=set()
        for address in range(1<<depth):
            leaf,work=routed_index(address,depth)
            need(work==20*depth and leaf not in seen,"Routed local word aliases")
            seen.add(leaf);cases+=1
    need(set(range(1804)).isdisjoint(range(2048,2048+2304)),"Private arrays alias")
    return dict(exhaustive_local_paths=cases,private_R_leaves=[0,1803],
                private_W_leaves=[2048,4351],code_word_leaves=[0,8191],
                every_word_route_has_one_parent_token=True)

def alu(isa,op,a=0,b=0):
    x=isa.signed(a);y=isa.signed(b)
    if op==isa.ADD:return (a+b)&MASK,128
    if op==isa.SUB:return (a-b)&MASK,128
    if op==isa.MUL:return multiply_limbs(a,b),256
    if op in (isa.DIV,isa.MOD):
        q,r,cost=signed_divmod(a,b)
        return (q if op==isa.DIV else r),cost
    if op==isa.SHL:return (a<<min(max(y,0),256))&MASK,128
    if op==isa.AND:return int(bool(x) and bool(y)),128
    if op==isa.OR:return int(bool(x) or bool(y)),128
    if op==isa.EQ:return int(x==y),128
    if op==isa.LT:return int(x<y),128
    if op==isa.LE:return int(x<=y),128
    if op==isa.NOT:return int(not a),128
    raise ValueError("Unknown local ALU selection")

@dataclass
class BankWork:
    capacity: int
    stock: F
    supplied: F=F(0)
    def transfer(self,cell):
        amount=min(F(PARENT)-cell.stock,self.stock)
        if amount<=0:return F(0)
        self.stock-=amount;self.supplied+=amount
        cell.stock+=amount
        return amount

class ParentCell:
    def __init__(self):
        self.capacity=F(PARENT);self.stock=F(0)
        self.spent=F(0);self.dumped=F(0);self.busy=False
    def debit(self,amount):
        amount=F(amount)
        if amount<0 or self.stock<amount:return False
        self.stock-=amount;self.spent+=amount
        return True
    def finish(self):
        self.dumped+=self.stock;self.stock=F(0);self.busy=False

@dataclass(frozen=True)
class Capture:
    body: object
    address: int
    cell: int
    operands: tuple
    launch_work: int

class CodeArray(list):
    """Fixed C words; explicit test/fault writes update the same bit cells."""
    def __init__(self,owner,values):
        self.owner=owner
        need(len(values)==8192 and all(type(v) is int and 0<=v<(1<<192) for v in values),
             "C must contain8192 actual192-bit words")
        super().__init__(values)
    def __setitem__(self,index,value):
        if isinstance(index,slice):
            indices=list(range(*index.indices(len(self))));values=list(value)
            need(len(indices)==len(values),"A code write cannot allocate another cell")
            for address,word_value in zip(indices,values):self[address]=word_value
            return
        need(type(index) is int and 0<=index<len(self) and type(value) is int
             and 0<=value<(1<<192),"Code intervention exceeds its actual wire/cell")
        list.__setitem__(self,index,value)
        if index in self.owner.physical:
            # In-place update preserves every already captured physical cell reference.
            self.owner.physical[index][:]=[F(2*((value>>j)&1)-1) for j in range(192)]
        self.owner.external_word_updates+=1

class Body:
    """Fixed arrays; sparse physical coordinates represent existing C cells."""
    def __init__(self,c,initial_code=None):
        self.physical={};self.external_word_updates=0
        self.C=CodeArray(self,c.image if initial_code is None else initial_code)
        self.R=[MASK]*c.next_register
        self.W=[0]*c.constants["DATA_WORDS"]
    def read_R(self,address):
        leaf,_=routed_index(address,13)
        return self.R[leaf]
    def write_R(self,address,value):
        leaf,_=routed_index(address,13)
        self.R[leaf]=value
    def read_W(self,address):
        leaf,_=routed_index(2048+address,13)
        return self.W[leaf-2048]
    def write_W(self,address,value):
        leaf,_=routed_index(2048+address,13)
        self.W[leaf-2048]=value
    def coordinates(self,address):
        if address not in self.physical:
            self.physical[address]=[F(2*((self.C[address]>>j)&1)-1) for j in range(192)]
        return self.physical[address]
    def observe_word(self,address):
        address,_=routed_index(address,13)
        if address in self.physical:
            list.__setitem__(self.C,address,sum(int(v>=0)<<j for j,v in enumerate(self.physical[address])))
        return self.C[address]
    def sync_word(self,address):
        list.__setitem__(self.C,address,sum(int(v>=0)<<j for j,v in enumerate(self.physical[address])))

class NativeWrite:
    """A paused2080-step native child, using the SAME paid CPU parent."""
    def __init__(self,body,address,value,parent):
        self.body=body;self.address=address;self.value=value&MASK
        self.parent=parent;self.index=0;self.done=False
        self.address_bits=[0]*256;self.operand_bits=[0]*192
        self.accepted=None;self.address_order=0
        self.target=None
        self.steps=0;self.bit_work=F(0);self.drive_bit=None
    def step(self,clock=True):
        if self.done:return "done"
        if not clock:return "clock-wait"
        if self.parent.stock<9:return "work-wait"
        need(self.parent.debit(8),"Native work duplicated")
        i=self.index
        if i<256:self.address_bits[i]=(self.address>>i)&1
        elif i<512:
            j=511-i
            limit=(8192>>j)&1
            if self.address_order==0 and self.address_bits[j]!=limit:
                self.address_order=-1 if self.address_bits[j]<limit else 1
            if i==511:
                self.accepted=self.address_order<0
                if self.accepted:
                    # These are the captured address wires, not a new caller.
                    observed=sum(v<<j for j,v in enumerate(self.address_bits))
                    self.target=self.body.coordinates(routed_index(observed,13)[0])
                else:self.done=True
        elif i<704:self.operand_bits[i-512]=(self.value>>(i-512))&1
        elif i<1856:
            bit,phase=divmod(i-704,6)
            sign=2*self.operand_bits[bit]-1
            if phase==0:self.drive_bit=bit
            if phase==5:self.drive_bit=None
            if 1<=phase<=4:
                before=self.target[bit]
                self.target[bit]=field.bit_flow(before,-sign*field.Z_MAX,
                    sign*field.NATIVE_FORCE,F(0) if phase==1 else F(100,101)/field.WORD_CLOCK,
                    native_engaged=True)
                self.bit_work+=abs(field.NATIVE_FORCE*(self.target[bit]-before))
                self.body.sync_word(self.address)
        elif i<2048:self.operand_bits[i-1856]=0
        # Last32 fixed completion/control steps are included and paid.
        self.index+=1;self.steps+=1
        if self.accepted and self.index==2080:
            need(self.parent.debit(1),"Native mechanical envelope unpaid")
            self.done=True
        return "done" if self.done else "step"

class ParentMachine:
    """Finite source leaf; no intended-image or ready predicate is consulted.

    Coherent local C/R/W capture/commit and fixed address routing are the
    elementary leaves. A failed leaf may wait or expose partial physical state;
    it does not receive nominal ISA/refill service by its name.
    """
    def __init__(self,isa,c,bank=None,body=None):
        self.isa=isa;self.compiled=c
        self._body=body if body is not None else Body(c)
        self.bank=bank if bank is not None else BankWork(2**60,F(2**60))
        self.initial_bank=self.bank.stock
        self.cell=ParentCell();self.pending=None;self.native=None
        self.pc=0;self.powered=True;self.halted=False;self.yielded=False
        self.steps=0;self.retired=0;self.word_work=0;self.io_counts=Counter()
        self.executed=Counter();self.code_writes=0;self.faults=[]
        self.front_work=0;self.body_work=0;self.offers=0;self.committing=False
        self.max_total_work=0;self.max_native_steps=0;self.rejected=Counter()
        self.nominal_work_time_upper=F(0)
    @property
    def C(self):return self._body.C
    @property
    def R(self):return self._body.R
    @property
    def W(self):return self._body.W
    @property
    def pending_instruction(self):return self.pending
    def rebind(self,body):
        return "busy" if self.pending is not None else "fixed-body"
    def recharge(self):
        if self.cell.busy or not self.powered:return False
        self.bank.transfer(self.cell)
        return self.cell.stock==PARENT
    def capture_indices(self,op,a,b,c,imm):
        s=self.isa
        if op in (s.MOV,s.NOT,s.LOAD,s.LOADC):return (b,)
        if op in (s.ADD,s.SUB,s.MUL,s.DIV,s.MOD,s.SHL,s.AND,s.OR,s.EQ,s.LT,s.LE):return (b,c)
        if op in (s.STORE,s.STOREC):return (a,b)
        if op==s.JZ:return (a,)
        if op in (s.CALL,s.RET):return (1,)
        if op==s.IO and 0<=imm<len(s.PRIMITIVES):
            name=s.PRIMITIVES[imm]
            if c==s.PRIM_ARITY[name] and b+c<=len(self.R):return tuple(range(b,b+c))
        return ()
    def launch(self,funded=True):
        if self.pending is not None:self.rejected["busy"]+=1;return False
        if not self.powered or self.halted:self.rejected["closed"]+=1;return False
        if not funded or self.cell.stock<PARENT:self.rejected["unfunded"]+=1;return False
        self.cell.busy=True
        if not 0<=self.pc<len(self.C):
            self.cell.debit(16);self.cell.finish();self.halted=True
            self.nominal_work_time_upper+=F(1,4*2**26)+F(16)/NATIVE_RATE
            self.rejected["invalid_pc"]+=1;return False
        code=self._body.observe_word(self.pc)
        op,a,b,c,imm=self.isa.decode(code)
        indices=self.capture_indices(op,a,b,c,imm)
        operands=tuple((i,self._body.read_R(i)) for i in dict.fromkeys(indices) if 0<=i<len(self.R))
        launch_work=16+468+64+32+280*len(indices)
        need(launch_work<=FRONT and self.cell.debit(launch_work),"Parent capture exceeded reserve")
        self.pending=Capture(self._body,self.pc,code,operands,launch_work)
        return True
    def reset_entry(self):
        # Reset neither cancels nor rebinds a captured parent/native child.
        self.pc=0;self.halted=False;self.yielded=False
    def finish_parent(self,extra_work,native=False):
        capture=self.pending
        need(capture is not None,"No parent to finish")
        remainder=FRONT-capture.launch_work
        need(self.cell.debit(remainder),"Complete opcode exceeded actual parent")
        used=FRONT+extra_work
        self.front_work+=FRONT;self.body_work+=extra_work
        self.max_total_work=max(self.max_total_work,used)
        native_steps=self.native.steps if self.native is not None else 0
        self.cell.finish();self.pending=None;self.native=None;self.committing=False
        # This bounds uninterrupted nominal work, never arbitrary wait time.
        ordinary=F(1,2**26)
        duration=ordinary if not native else max(ordinary,ordinary/4+F(FRONT)/NATIVE_RATE+F(native_steps)/field.WORD_CLOCK)
        self.nominal_work_time_upper+=duration
        need(self.bank.stock+self.cell.stock+self.cell.spent+self.cell.dumped==self.initial_bank,
             "Parent/operating work was created")
    def complete(self,ports,*,native_ticks=None,clock=True):
        p=self.pending
        if p is None or self.committing:return False
        if not clock:return "waiting"
        s=self.isa;op,a,b,c,imm=s.decode(p.cell)
        values=dict(p.operands)
        def get(i):return values.get(i,0)
        def put(i,value):
            if 0<=i<len(p.body.R):p.body.write_R(i,value&MASK)
        if op==s.STOREC:
            if self.native is None:self.native=NativeWrite(p.body,get(b),get(a),self.cell)
            native_was_done=self.native.done
            limit=2080 if native_ticks is None else native_ticks
            for _ in range(limit):
                result=self.native.step(clock=clock)
                if result in ("clock-wait","work-wait"):return "waiting"
                if result=="done":break
            if not self.native.done:return "waiting"
            extra=self.native.steps*8+(1 if self.native.accepted else 0)
            self.max_native_steps=max(self.max_native_steps,self.native.steps)
            if self.native.accepted and not native_was_done:self.code_writes+=1
        else:
            extra=8320 if op in (s.DIV,s.MOD) else 256 if op==s.MUL else 128
            if op==s.IO and 0<=imm<len(s.PRIMITIVES):
                name=s.PRIMITIVES[imm]
                if c==s.PRIM_ARITY[name] and b+c<=len(p.body.R):
                    extra=(9184 if name in ("fast_cmp","fast_equal","fast_range") else
                           12416 if name in ("source_idiv","source_imod") else
                           326 if name in program.FORBIDDEN else 4096)
            # Actual work is unavailable after a physical loss: no effect is
            # issued first and financed retroactively by completion.
            if self.cell.stock<FRONT-p.launch_work+extra:return "waiting"
            need(self.cell.debit(extra),"Unfunded ordinary effect")
        if self.cell.stock<FRONT-p.launch_work:return "waiting"
        # Consume the completion strobe before calling any external port leaf.
        self.committing=True
        # Atomic architectural completion is ordered after any native write.
        self.pc=p.address+1;self.retired=(self.retired+1)%(1<<64)
        self.steps+=1;self.word_work+=1;self.executed[op]+=1
        if op==s.LI:put(a,imm)
        elif op==s.MOV:put(a,get(b))
        elif op in (s.ADD,s.SUB,s.MUL,s.DIV,s.MOD,s.SHL,s.AND,s.OR,s.EQ,s.LT,s.LE):
            result,_body_cost=alu(s,op,get(b),get(c));put(a,result)
        elif op==s.NOT:put(a,int(not get(b)))
        elif op==s.LOAD:
            put(a,p.body.read_W(get(b)) if get(b)<len(p.body.W) else 0)
        elif op==s.STORE:
            if get(b)<len(p.body.W):p.body.write_W(get(b),get(a))
        elif op==s.LOADC:
            put(a,p.body.observe_word(get(b)) if get(b)<len(p.body.C) else 0)
        elif op==s.JMP:self.pc=imm
        elif op==s.JZ:
            if not get(a):self.pc=imm
        elif op==s.CALL:
            sp=get(1)
            if sp>=self.compiled.constants["STACK_WORDS"]:self.halted=True
            else:p.body.write_W(sp,self.pc);put(1,sp+1);self.pc=imm
        elif op==s.RET:
            sp=get(1)
            if not 0<sp<=self.compiled.constants["STACK_WORDS"]:self.halted=True
            else:put(1,sp-1);self.pc=p.body.read_W(sp-1)
        elif op==s.IO and 0<=imm<len(s.PRIMITIVES):
            name=s.PRIMITIVES[imm]
            if c==s.PRIM_ARITY[name] and b+c<=len(p.body.R):
                args=tuple(s.signed(get(i)) for i in range(b,b+c))
                self.io_counts[name]+=1
                # The actual port leaf returns0/unavailable/reject or offers
                # its captured descriptor. Existing children are not canceled.
                self.offers+=1
                result=ports.perform(name,args,self)
                put(a,0 if result is None else result)
                if name=="yield_frame":self.yielded=True
                if name=="set_field":
                    # Complete child/refill bound; no intervening retirement.
                    self.nominal_work_time_upper+=F(1,64)
        elif op==s.HALT:self.halted=True
        ports.advance(self)
        self.finish_parent(extra,native=op==s.STOREC)
        return True
    def step(self,ports):
        if self.pending is not None:return False
        if not self.recharge() or not self.launch():return False
        return self.complete(ports) is True
    def enter(self,name,args=()):
        need(self.pending is None,"Harness cannot bypass a pending parent")
        self.pc=self.compiled.labels[name];self.R[1]=1;self.W[0]=len(self.C)
        self.halted=False;self.yielded=False
        for reg,value in zip(self.compiled.formals[name],args):self.R[reg]=value&MASK
    def run(self,ports,budget,until_yield=True):
        self.yielded=False;start=self.steps
        while self.steps-start<budget and not self.halted:
            if not self.step(ports):return "halt" if self.halted else "blocked"
            if until_yield and self.yielded:return "yield"
        return "halt" if self.halted else "timeout"
    def result(self):return self.isa.signed(self.R[2])

def setter_control_checks():
    """Execute the literal child plus explicit paid cursor/control ticks.

    Payload ticks use the existing bounded bit-port law. The added control
    tick is a finite cursor/phase update, not an instruction or image oracle.
    """
    targets=tuple("parent-target-"+str(i) for i in range(40))
    rows=[]
    for args in ((0,0,0,1),(39,1,field.L-1,-1),(-1,0,0,1),(0,0,field.L,1)):
        setter=field.SettingWriter(targets)
        original=args
        need(setter.issue(args)=="latched","Fixed child did not capture")
        ticks=0;events=Counter();cursor=0
        while setter.phase=="pending":
            event=setter.step()
            if event=="recharging":break
            need(event not in ("wait","unfunded-wait","inhibited-wait","retired-wait"),
                 "Nominal complete child lost work")
            events[event]+=1
            # A12-bit finite controller cursor, updated after each payload
            # event. Its one tick includes increment/test/phase/loop control.
            need(cursor<4095 and setter.energy>=17,"Control tick unfunded")
            cursor+=1;setter.energy-=16;ticks+=2
        literal=sum(events.values())
        need(literal==setter.steps and literal in (3584,3615),"Literal child count changed")
        # Six answer flags12, bounded validity fold7, address decoding60,
        # return/control16, and at most96 used control bits to clear.
        control_items=dict(answer_flags=12,validity_fold=7,address_decode=60,
                           return_control=16,used_control_clear=96)
        need(sum(control_items.values())<=256,"Fixed stage/control budget omitted work")
        control=[1]*96
        for step in range(256):
            need(setter.energy>=17,"Stage/control tick unfunded")
            setter.energy-=16;ticks+=1
            if step<96:control[step]=0
        need(not any(control) and setter.parent_record is original,
             "Control clear erased/rebound the captured parent")
        need(ticks==2*literal+256<=8192 and field.SET_ENERGY-setter.energy==16*ticks,
             "Child/loop work was not actually paid")
        held=dict(setter.held);spent=field.SET_ENERGY-setter.energy
        # Idle capped refill: there is no further child tick expenditure.
        # The caller's already paid return transition observes the full cell.
        upstream=2*spent
        setter.recharge(field.SET_REFILL)
        need(setter.energy==field.SET_ENERGY and setter.phase=="ready"
             and setter.held==held and not setter.parent_live,
             "Actual idle refill did not precede release")
        rows.append(dict(arguments=list(args),literal_ticks=literal,complete_ticks=ticks,
                         actual_child_work=spent,actual_refill_upstream=upstream,
                         conversion_heat=spent,held_effects=len(held),
                         complete_control_items=control_items))
    return dict(cases=rows,maximum_ticks=max(r["complete_ticks"] for r in rows),
                maximum_work=max(r["actual_child_work"] for r in rows),
                native_tick_work_ceiling=16,source_clock_min=2**20,
                immutable_parent_retained_until_refill=True,
                refill_has_no_competing_child_draw=True,
                scope="Executed finite cursor/control expansion under bounded local bit-port/control laws; physical clock/containment admission remains")

def cost_bounds():
    c_read=13*20+208
    r_access=13*20+12
    common=16+c_read+64+32+64+128+32
    cases=dict(ALU=common+2*(r_access+8)+r_access,
        IO5=common+5*(r_access+8)+r_access,
        LOAD=common+(r_access+8)+2*r_access,
        LOADC=common+(r_access+8)+c_read+r_access,
        STORE=common+2*(r_access+8)+r_access,
        STOREC=common+2*(r_access+8)+13*20,
        CALL_RET=common+(r_access+8)+2*r_access)
    need(max(cases.values())<=FRONT,"Shared frontend bound failed")
    # Explicit native64 restoring-division round profile, not a bulk256 opcode.
    round_work=dict(input_bit_selection=4,four_limb_shift=12,four_SBB=4,
                    take_predicate=2,four_selects=4,quotient_bit=3,round_control=3)
    need(sum(round_work.values())==32 and 256*32+128==8320,"Division count changed")
    mu=F(101,100)*2**26
    slow_cycle=F(1,2**26);fast_cycle=1/mu
    need(slow_cycle-fast_cycle==F(1,101*2**26)>0,
         'Fastest-cycle countercase to a uniform upper bound disappeared')
    suffix=F(604,100)*DELTA+F(928+6976+256+FRONT)/NATIVE_RATE
    native_total=16641+FRONT
    need(9184+FRONT<=PARENT and native_total<PARENT,"Parent work does not fit")
    need(8320+4096+FRONT<16384,"ALU plus ordinary I admission/native budget exceeded")
    need(suffix<F(3,4)/mu and suffix+F(1,4*2**27)<1/mu,"Private timing failed")
    need(F(2080)/field.WORD_CLOCK+F(FRONT)/NATIVE_RATE<F(1,64),"Native suffix exceeds old drain allowance")
    # One code tree and one padded private-word tree per CPU, plus I-address tree.
    route_nodes=2*(2*(8192-1)*128+7*128)
    capture_buffers=2*(8192+1804+2304+8)*256
    route_bits=route_nodes+capture_buffers
    old=json.loads((HERE/"legacy_realization_results.json").read_text())
    meta=old["inventory"]["memory_by_owner"]["local_route_metadata"]
    need(meta["new_owner_upper"]+route_bits<=meta["old_owner_allocation"],"Actual route controls lack a memory owner")
    source,core,_ports,_field,_bindings,_text=legacy.inputs()
    execution=source["parameters"]["execution"]
    need(F(execution["private_native_work_rate_capacity"])==NATIVE_RATE
         and F(execution["nominal_instruction_rate_max"])==mu,
         "Parent clock/work source changed")
    need(old["inventory"]["private_IO_work_with_selector"]==9184
         and field.WORD_ENERGY==PARENT and field.WORD_CLOCK==2**30,
         "Captured port/native parent interface changed")
    need(F(_field["point"]["mechanics"]["native_word_mechanical_work_upper"])<1,
         "Native write needs a larger mechanical parcel")
    need(3*F(100,101)/field.WORD_CLOCK>F(2)/field.BIT_SPEED,
         "Native held-bit interval no longer reaches the endpoint")
    new_bank=F(old["inventory"]["actual_ordinary_bank_rate_upper"])+F(route_bits,2048)
    new_external=F(old["inventory"]["external_rate_upper"])+route_bits*F(core["background_clock_rate"])+F(route_bits,1024)
    need(new_bank<=F(old["inventory"]["retained_downrated_bank_allowance"]),"Added route holding breaks bank allocation")
    need(new_external<=F(core["external_rate"]),"Added route clocks break source-owner allocation")
    need(F(2**60)<=F(core["per_bank_capacity"]),"Finite test payer exceeds actual bank capacity")
    # A literal setter event and one cursor/control event, plus complete fixed
    # stage transitions; no new work parcel is inferred from unused steps.
    setter_steps=2*3615+256
    need(setter_steps<=8192 and setter_steps*16<2**20,"Setter control schedule exceeds its existing envelope")
    return dict(nominal_retirement_duration_upper=slow_cycle,
        fastest_cycle_not_uniform_upper=fast_cycle,
        omitted_slow_clock_duration=slow_cycle-fast_cycle,
        time_accumulator_scope='upper bound on completed uninterrupted nominal work; excludes stalled/unfunded time',
        frontend_cases=cases,frontend_reserved=FRONT,frontend_unused_margin=FRONT-max(cases.values()),
        routed_access_work=r_access,code_capture_work=c_read,route_hop_work=20,
        route_node_bits=128,new_private_routing_bits=route_bits,
        route_node_control_bits=route_nodes,local_capture_buffer_bits=capture_buffers,
        old_metadata_slack_after_route=meta["old_owner_allocation"]-meta["new_owner_upper"]-route_bits,
        new_actual_bank_rate_upper=new_bank,new_external_owner_rate_upper=new_external,
        external_owner_rate_slack=F(core["external_rate"])-new_external,
        actual_bank_capacity=core["per_bank_capacity"],finite_test_payer_initial=2**60,
        parent_descriptor_bits=5*256+192+14+24+16+256,
        division_round_work=round_work,division_rounds=256,division_work=8320,
        ordinary_IO_admission_envelope=4096,raw_I_division_total=8320+4096+FRONT,
        private_IO_total=9184+FRONT,private_suffix=suffix,private_nominal_slack=F(3,4)/mu-suffix,
        parent_reuse_slack=1/mu-suffix-F(1,4*2**27),
        native_STOREC_total=native_total,native_parent_floor_margin=PARENT-1-native_total,
        native_complete_tail=F(2080)/field.WORD_CLOCK+F(FRONT)/NATIVE_RATE,
        setter_literal_and_cursor_steps=2*3615,setter_stage_control_steps=256,
        setter_complete_ticks=setter_steps,setter_complete_work=setter_steps*16,
        setter_schedule_status="executed payload/cursor/control expansion under declared elementary tick law",
        setter_time_upper=F(setter_steps,2**20),setter_existing_time_allocation=F(1,128),
        leaf_scope="Declared bounded local routing/capture/native64/fixed-control laws; not fabrication validation")

def alu_checks(isa):
    values=[0,1,2,3,2**63-1,2**63,2**64-1,2**64,2**127,2**128-1,
            2**255-1,2**255,2**255+1,MASK-1,MASK]
    rng=random.Random(20261114)
    pairs=[(a,b) for a in values for b in values]+[(rng.getrandbits(256),rng.getrandbits(256)) for _ in range(500)]
    for a,b in pairs:
        q,r,cost=signed_divmod(a,b);x=isa.signed(a);y=isa.signed(b)
        need(q==(x//y if y else 0)&MASK and r==(x%y if y else 0)&MASK,
             "Signed floor division/modulo mismatch")
        need(cost<=8320,"Division exceeded its counted rounds")
        ua=word(negate(limbs(a))) if a>>255 else a
        ub=word(negate(limbs(b))) if b>>255 else b
        uq,ur,_=unsigned_divide(ua,ub)
        need((ub==0 and uq==ur==0) or (ub>0 and ur<ub and uq*ub+ur==ua),
             "Independent quotient/remainder identity failed")
        need(multiply_limbs(a,b)==(a*b)&MASK,"Four-limb multiplication differs")
    return dict(signed_DIV_MOD_pairs=len(pairs),boundary_values=[str(x) for x in values],
                divisor_zero_total=True,min_signed_over_minus_one_wraps=True,
                algorithm="four-limb restoring division plus explicit floor/sign correction")

def snapshot(machine):
    return (machine.C,machine.R,machine.W,machine.pc,machine.retired,
            machine.halted,machine.yielded,machine.code_writes)

def instruction_checks(isa,c):
    Ports=legacy.absence_ports_class(isa)
    report=[];value_cases=((0,0),(1,2),(MASK,1),(1,MASK),(2**255,MASK),
                         (2**255,2),(8191,8192),(32,0))
    for op in range(0,26):
        for x,y in value_cases:
            pm=ParentMachine(isa,c);ref=program.initialized(isa,c)
            pp=Ports(c);rp=Ports(c)
            cell=isa.encode(op,3,4,5,0)
            for m in (pm,ref):
                m.C[0]=cell;m.C[1]=isa.encode(isa.HALT)
                m.R[3]=x;m.R[4]=y;m.R[5]=x;m.R[1]=x
                m.W[0]=7;m.W[31]=9
            need(pm.step(pp)==ref.step(rp),"Single-step stop differs")
            need(snapshot(pm)==snapshot(ref),"Ordinary instruction differs: "+str((op,x,y)))
            report.append(op)
    # Out-of-range register/PC/W/C addresses remain charged, total outcomes.
    rejected=0
    for op in (isa.MOV,isa.LOAD,isa.LOADC,isa.STORE,isa.STOREC,isa.CALL,isa.RET):
        for mfield in (0,(1<<24)-1):
            pm=ParentMachine(isa,c);ref=program.initialized(isa,c)
            pp=Ports(c);rp=Ports(c)
            for m in (pm,ref):
                m.C[0]=isa.encode(op,mfield,mfield,mfield,0)
                m.R[0]=MASK;m.R[1]=MASK
            need(pm.step(pp)==ref.step(rp) and snapshot(pm)==snapshot(ref),"Invalid indexed outcome differs")
            rejected+=1
    pc_outcomes=[]
    for pc in (-1,8192,2**111-1,MASK):
        m=ParentMachine(isa,c);p=Ports(c);m.pc=pc
        before=m.bank.stock
        need(not m.step(p) and m.halted and m.cell.stock==0 and m.steps==0,
             "Invalid PC did not take finite paid halt")
        need(before-m.bank.stock==PARENT,"Invalid attempt was free")
        pc_outcomes.append(str(pc))
    io_cases=0
    for primitive in list(range(len(isa.PRIMITIVES)))+[len(isa.PRIMITIVES),100]:
        for arity in (0,isa.PRIM_ARITY.get(isa.PRIMITIVES[primitive],0) if primitive<len(isa.PRIMITIVES) else 5):
            pm=ParentMachine(isa,c);ref=program.initialized(isa,c)
            pp=Ports(c);rp=Ports(c)
            for m in (pm,ref):
                m.C[0]=isa.encode(isa.IO,2,3,arity,primitive)
                m.R[3:8]=[MASK]*5
            need(pm.step(pp)==ref.step(rp) and snapshot(pm)==snapshot(ref),
                 "Malformed/absent IO changed ISA outcome")
            need(pp.events==rp.events and pp.I==rp.I,"IO effect or input handling differs")
            io_cases+=1
    return dict(ordinary_boundary_steps=len(report),opcodes=sorted(set(report)),invalid_index_steps=rejected,
                invalid_PC_values=pc_outcomes,IO_arity_and_absence_cases=io_cases,
                observer="Frozen ordinary interpreter, compared with independent dispatcher")

def retention_checks(isa,c):
    Ports=legacy.absence_ports_class(isa)
    m=ParentMachine(isa,c);p=Ports(c)
    m.C[0]=isa.encode(isa.IO,2,3,2,isa.PRIM["world"])
    m.R[3]=(-100)&MASK;m.R[4]=(-100)&MASK
    need(not m.launch(funded=False),"Unfunded capture occurred")
    m.recharge();need(m.launch(),"Parent capture failed")
    captured=m.pending
    need(not m.launch() and not m.recharge(),"Busy parent acquired another token")
    m.C[0]=isa.encode(isa.HALT);m.R[3]=100;m.R[4]=100
    m.powered=False;m.reset_entry()
    need(m.pending is captured and m.complete(p) is True and p.world_latch==(-100,-100),
         "Reset/power loss changed captured IO identity")
    need(not m.complete(p) and not m.launch(),"Parent completion replayed")
    # A hostile completion callback cannot recursively mint another offer.
    class Reentrant(Ports):
        def perform(self,name,args,machine):
            need(machine.complete(self) is False,"Completion strobe was reusable")
            return super().perform(name,args,machine)
    m2=ParentMachine(isa,c);p2=Reentrant(c)
    m2.C[0]=isa.encode(isa.IO,2,3,2,isa.PRIM["world"])
    need(m2.step(p2) and m2.offers==1,"Once-only external delivery failed")
    before_closed=(m.bank.stock,m.cell.stock)
    need(not m.recharge() and before_closed==(m.bank.stock,m.cell.stock),
         "Power loss left a fresh parent recharge route")
    # LOADC captures its addressed memory at the operation's actual read, not
    # from a launch-time template or an earlier snapshot of that code word.
    late=ParentMachine(isa,c);lp=Ports(c)
    late.C[0]=isa.encode(isa.LOADC,3,4);late.R[4]=100;late.C[100]=7
    late.recharge();late.launch();late.C[100]=13
    need(late.complete(lp) is True and late.R[3]==13,"LOADC used an early/template word")
    # Work-starved parent cannot become full by a digital reset.
    poor=ParentMachine(isa,c,BankWork(100,F(100)));poor.recharge()
    poor.reset_entry()
    need(not poor.launch() and poor.cell.stock==100 and poor.bank.stock==0,
         "Reset invented parent charge")
    ordinary=ParentMachine(isa,c);ordinary_ports=Ports(c)
    ordinary.C[0]=isa.encode(isa.IO,2,3,2,isa.PRIM["world"])
    ordinary.R[3]=(-100)&MASK;ordinary.R[4]=(-100)&MASK
    ordinary.recharge();ordinary.launch()
    before=(ordinary.steps,ordinary.cell.stock,ordinary_ports.world_latch)
    need(ordinary.complete(ordinary_ports,clock=False)=="waiting"
         and before==(ordinary.steps,ordinary.cell.stock,ordinary_ports.world_latch),
         "Stopped ordinary clock produced an effect")
    ordinary.cell.debit(ordinary.cell.stock-1)
    need(ordinary.complete(ordinary_ports)=="waiting" and ordinary.steps==0
         and ordinary_ports.world_latch==before[2] and not ordinary_ports.events,
         "Ordinary effect preceded its work debit")
    # Actual serial physical effects remain visible during a paused native write.
    n=ParentMachine(isa,c);np=Ports(c);address=100
    n.C[address]=0;n.C[0]=isa.encode(isa.STOREC,3,4)
    n.R[3]=(1<<192)-1;n.R[4]=address
    n.recharge();need(n.launch(),"Native parent did not latch")
    need(n.complete(np,native_ticks=704+6)=="waiting","Partial native write disappeared")
    partial=n.C[address]
    need(partial==1 and n.steps==0 and n.native.body is n.pending.body,"Partial bits/identity lost")
    saved=(n.native.index,n.C[address],n.cell.stock)
    need(n.complete(np,native_ticks=8,clock=False)=="waiting"
         and saved==(n.native.index,n.C[address],n.cell.stock),"Clock wait created work/progress")
    n.powered=False;n.reset_entry()
    need(n.rebind(Body(c))=="busy" and not n.launch(),"Old parent rebound or allowed an overlapping read")
    need(n.complete(np) is True and n.C[address]==(1<<192)-1 and n.code_writes==1,
         "Old native suffix did not complete on its actual body")
    need(not n.complete(np),"Native parent replayed")
    # Exposing physical C during this interval defeats a stronger atomic-state claim.
    need(partial not in (0,(1<<192)-1),"Atomic-observation counterexample missing")
    driven=ParentMachine(isa,c);dp=Ports(c)
    driven.C[20]=0;driven.C[0]=isa.encode(isa.STOREC,3,4)
    driven.R[3]=MASK;driven.R[4]=20;driven.recharge();driven.launch()
    need(driven.complete(dp,native_ticks=705)=="waiting" and driven.native.drive_bit==0,
         "Native energized mode was dropped")
    # A no-clock-edge call is NOT a physical flow interval. If real time
    # elapses with this mode held, its paid native bit law may still move C.
    before=driven.native.target[0]
    flowed=field.bit_flow(before,-field.Z_MAX,field.NATIVE_FORCE,F(1,2**30),native_engaged=True)
    need(flowed!=before and abs(field.NATIVE_FORCE*(flowed-before))<1,
         "Clock-stop/physical-freeze countercase disappeared")
    # A later direct C intervention must not be hidden by a cached physical
    # projection; these are source interventions, not a free runtime opcode.
    n.C[address]=7
    need(n._body.observe_word(address)==7 and sum(int(v>=0)<<j for j,v in enumerate(n._body.physical[address]))==7,
         "Physical code materialization hid a later word intervention")
    # No arrival/direct-input outcome is granted nominal service when a leaf stalls.
    stalled=ParentMachine(isa,c);sp=Ports(c)
    stalled.C[0]=isa.encode(isa.STOREC,3,4);stalled.R[3]=MASK;stalled.R[4]=10
    stalled.recharge();stalled.launch();stalled.complete(sp,native_ticks=710)
    stalled.cell.debit(stalled.cell.stock-1)
    state=(stalled.native.index,stalled.C[10])
    need(stalled.complete(sp)=="waiting" and state==(stalled.native.index,stalled.C[10]),
         "Physically lost parent work was replaced")
    # Native completion and architectural retirement are separate events.
    # The final native step may spend the last work while frontend return waits.
    final_wait=ParentMachine(isa,c);fp=Ports(c)
    final_wait.C[0]=isa.encode(isa.STOREC,3,4);final_wait.R[3]=MASK;final_wait.R[4]=21
    final_wait.recharge();need(final_wait.launch(),"Final native test did not capture")
    need(final_wait.complete(fp,native_ticks=2079)=="waiting","Native prefix completed too soon")
    need(final_wait.cell.debit(final_wait.cell.stock-9),"Could not construct retained low-work case")
    for _ in range(3):
        need(final_wait.complete(fp)=="waiting" and final_wait.native.done
             and final_wait.code_writes==1 and final_wait.retired==0,
             "Waiting frontend counted one native completion repeatedly")
    return dict(captured_world=list(p.world_latch),reset_preserved_pending=True,
                replay_rejected=True,recursive_offer_rejected=True,partial_native_word=str(partial),
                native_completed_steps=n.max_native_steps,old_body_retained=True,
                intermediate_C_is_observable_physically=True,blocked_local_read=True,
                clock_wait_retains_state=True,unfunded_wait_retains_partial_effect=True,
                ordinary_unfunded_effect_withheld=True,power_cut_blocks_recharge=True,
                LOADC_uses_current_addressed_C=True,
                clock_wait_is_not_a_frozen_physical_flow=True,
                driven_native_mode_retained=True,
                post_native_C_intervention_preserved=True,
                native_completion_counted_once_while_frontend_waits=True)

def port_fixture(isa,c,load=125):
    Ports=legacy.absence_ports_class(isa);p=Ports(c)
    view=isa.populated_view(c,0,10)
    p.set_view(0,view)
    program.fill_permission(c,p,0,load)
    for key,value in list(p.fast.items()):
        if len(key)==3 and all(type(v) is int for v in key):
            slot,bank,k=key
            selected,_=p.selector.select(k,slot,bank)
            if selected is not None:
                need(p.physical_records.put((selected[2],selected[0],bank,k),value&MASK),"Fixture endpoint absent")
    return p

def program_checks(isa,c,b):
    cases=[]
    for name,args,limit in (("refresh_fields",(),b["instruction_upper_bounds"]["refresh_fields"]+10),
                            ("helper",(0,),b["instruction_upper_bounds"]["helper"]+100)):
        actual=ParentMachine(isa,c);reference=program.initialized(isa,c)
        pp=port_fixture(isa,c);rp=port_fixture(isa,c)
        if name=="refresh_fields":
            for m in (actual,reference):
                m.C[100]^=1;m.W[c.constants["VECTOR_CURSOR"]]=100*192
        else:
            base=c.constants["TARGET_BASE"]
            for m in (actual,reference):
                for key,value in (("STAGE_ID",11),("WATCH_HALF",1),("LAST_PHASE",10),
                                  ("HIGH",250162000),("TIMER",2300000000),("RANK_VALID",1)):
                    m.W[base+c.constants[key]]=value
        actual.enter(name,args);reference.enter(name,args)
        need(actual.run(pp,limit,False)==reference.run(rp,limit,False)=="halt",
             "Consumed routine did not finish")
        need(snapshot(actual)==snapshot(reference) and pp.events==rp.events
             and pp.held_fields==rp.held_fields,"Consumed actual-C routine diverged")
        cases.append(dict(routine=name,instructions=actual.steps,paid_parent_work=actual.cell.spent,
            actual_operating_transfer=actual.bank.supplied,unused_work_dissipated=actual.cell.dumped,
            highest_instruction_work=actual.max_total_work,offered_operations=actual.offers,
            actual_C_scan=(name=="refresh_fields"),no_full_paced_frame=True))
    return cases

def normalize(value):
    if isinstance(value,F):return str(value)
    if isinstance(value,dict):return {k:normalize(v) for k,v in value.items()}
    if isinstance(value,(tuple,list)):return [normalize(v) for v in value]
    return value

def generate():
    need(sys.version_info[:2]==(3,12) and not sys.flags.optimize,"Unoptimized Python3.12 required")
    isa=program.load_isa();c=program.compile_program(isa,design.design(isa));b=program.bounds(isa,c)
    need(len(c.image)==8192 and c.next_register==1804 and len(Body(c).W)==2304,
         "This parent address tree requires its declared fixed array shape")
    print("checking parent transitions, signed limbs and retained native writes",flush=True)
    costs=cost_bounds();routes=route_checks();arithmetic=alu_checks(isa);setter=setter_control_checks()
    instructions=instruction_checks(isa,c);retained=retention_checks(isa,c)
    print("executing actual scanner/helper through the paid parent",flush=True)
    routines=program_checks(isa,c,b)
    names=("PARENT-REALIZATION.md","parent_realization.py","legacy_realization.py",
        "legacy_realization_results.json","LEGACY-REALIZATION.md","threshold_program_model.py",
        "threshold_program_source.py","threshold_design.py","threshold_incidence_model.py",
        "threshold_publication_model.py","constructors.py","threshold_field_source.py",
        "threshold_field_source_results.json","THRESHOLD-FIELD-SOURCE.md")
    for record in ("legacy_realization_results.json","threshold_field_source_results.json"):
        r=json.loads((HERE/record).read_text())
        for name,expected in r["sources_sha256_lf"].items():
            need(program.digest(HERE/name)==expected,"Current executable input binding differs: "+name)
    return normalize(dict(scope="Constructed paid finite parent leaf and qualified local ISA observation refinement",
        base=BASE,python_version=sys.version,image_sha256=program.hash_text(json.dumps(c.image)),
        frozen_ISA_sha256=isa.source_hash,sources_sha256_lf={n:program.digest(HERE/n) for n in names},
        cost_bounds=costs,routed_memory_checks=routes,arithmetic=arithmetic,setter_control_checks=setter,instruction_checks=instructions,
        retained_parent_checks=retained,consumed_routines=routines,
        source_leaf_primitives=["bounded native64 ALU with carry","fixed active-path address routing",
            "coherent local fixed-word capture/commit","nonrearming paid parent token",
            "actual port outcomes and retained child descriptors","finite native word bit flow"],
        residuals=["instantiate local capture/commit and routing laws in the admitted source/fault map",
            "join actual setter complete control/refill leaf to the parent timing path",
            "ordinary remaining port micro-operations retain their explicit bounded elementary laws",
            "physical observation of partial C is retained; only blocked program observers receive atomic quotient",
            "all-history entry, power, writer exclusion, retirement, resource and common-core composition"],
        full_physical_hybrid_trace=False,full_source_admission=False,program_completion=False,
        independent_review_pending=True))

def main():
    ap=argparse.ArgumentParser(description=__doc__);g=ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--write",action="store_true");g.add_argument("--check",action="store_true")
    args=ap.parse_args();result=generate();path=HERE/"parent_realization_results.json"
    if args.write:path.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n",encoding="utf-8",newline="\n")
    else:need(json.loads(path.read_text(encoding="utf-8"))==result,"Parent realization record differs")
    print("PASS finite paid parent/ISA leaf; source and recurrent admission remain open")

if __name__=="__main__":main()

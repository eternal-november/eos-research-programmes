"""Finite stored-program runtime for recurring Byzantine control.
The prescribed program reads actual local bytes and port/ADC state only.
No source truth, fault identity, cure status or global time is a policy input.
"""
from __future__ import annotations
import sys
if sys.flags.optimize:
    raise RuntimeError("Unoptimized Python is required")
import argparse
from dataclasses import dataclass
from fractions import Fraction as F
from hashlib import sha256
import json
import os
from pathlib import Path
import random
import struct

ROOT = Path(__file__).resolve().parent
N, GROUP, IMAGE_BYTES = 34, 17, 8192
M, S = IMAGE_BYTES * 8, 65600
P = N * S
ID, PHASE, DRAIN, ADC, ADC_VALID = 4096, 4100, 4104, 4108, 4112
CAL = 4116
RX, SORT, REG, PC = 4352, 4864, 6144, 6272
SIGMA_BIT = 65535
MAGIC = 0x42594331
MASK = (1 << 32) - 1
WORD_LIMIT, SETUP_WORK, INSTRUCTION_WORK = 200000, 256, 32

# Fixed-width instruction format: opcode,a,b,c,32-bit immediate.
HALT, LI, MOV, ADD, SUB, MUL, DIV, MOD, AND, SHR = range(10)
LOAD, STORE, BIT, JMP, JEQ, JNE, JSLT, JULT, SAMPLE, SEND, SETG, SETU, FIELD = range(10,23)

def u32(v): return v & MASK
def s32(v): return v if v < 1 << 31 else v - (1 << 32)
def rd(mem, addr):
    return int.from_bytes(mem[addr:addr+4], "little") if 0 <= addr <= IMAGE_BYTES-4 else 0
def wr(mem, addr, value):
    if 0 <= addr <= IMAGE_BYTES-4:
        mem[addr:addr+4] = u32(value).to_bytes(4, "little")
def getbit(mem, address):
    return (mem[address//8] >> (address%8)) & 1 if 0 <= address < M else 0
def putbit(mem, address, value):
    if 0 <= address < M:
        mask = 1 << (address%8)
        mem[address//8] = (mem[address//8] & ~mask) | ((value & 1) << (address%8))
def packet(value):
    return (MAGIC << 32) | (value & 65535)
def decode(word):
    low, high = word & MASK, (word >> 32) & MASK
    if high != MAGIC or low >= 65536: return 0
    value = low if low < 32768 else low - 65536
    return value if -4000 <= value <= 4000 else 0
def correction(m):
    value = min(1500, 8 * max(abs(m)-53,0)//5)
    return value if m >= 0 else -value

class Assembler:
    def __init__(self):
        self.code=[]; self.labels={}; self.fixups=[]; self.code_size_fixups=[]
    def label(self,name):
        assert name not in self.labels
        self.labels[name]=8*len(self.code)
    def emit(self,op,a=0,b=0,c=0,imm=0):
        self.code.append([op,a,b,c,imm]); return len(self.code)-1
    def li(self,a,v): return self.emit(LI,a,imm=v)
    def jump(self,op,label,a=0,b=0):
        self.fixups.append((self.emit(op,a,b),label))
    def field(self,emitter,kind,target,address,value):
        self.emit(FIELD,emitter,kind,target,(address & 31)|((value & 31)<<5))
    def finish(self):
        for index,label in self.fixups: self.code[index][4]=self.labels[label]
        size=8*len(self.code)
        for index in self.code_size_fixups: self.code[index][4]=size*8
        return b"".join(struct.pack("<BBBBI",op,a,b,c,u32(imm)) for op,a,b,c,imm in self.code)

def assemble_program():
    a=Assembler()
    # r0=zero; r31=one. Constants, phase and identifier are actually loaded.
    a.li(0,0); a.li(31,1); a.li(10,N); a.li(11,S); a.li(12,P); a.li(13,M)
    a.emit(LOAD,2,0,imm=PHASE); a.emit(MOD,2,2,12)
    a.emit(LOAD,1,0,imm=ID)
    a.jump(JULT,"valid",1,10); a.jump(JMP,"invalid")
    a.label("valid")
    a.emit(SETG,31)
    a.emit(DIV,4,2,11); a.emit(MOD,5,2,11)
    a.jump(JEQ,"zero_fields",1,4)
    a.li(3,4); a.jump(JULT,"open",5,3)
    a.li(3,M+4); a.jump(JEQ,"close",5,3)
    a.jump(JULT,"write",5,3)
    a.jump(JMP,"zero_fields")
    a.label("open")
    a.field(0,0,4,0,31); a.field(1,0,4,0,0); a.jump(JMP,"after_fields")
    a.label("close")
    a.li(9,-1); a.field(0,0,4,0,9); a.field(1,0,4,0,9); a.jump(JMP,"after_fields")
    a.label("write")
    a.li(3,4); a.emit(SUB,6,5,3)
    a.field(0,0,4,0,31)
    a.code_size_fixups.append(a.li(15,0))
    a.jump(JULT,"copy_code",6,15)
    for address,label in ((ID,"image_id"),(PHASE,"image_phase"),(DRAIN,"image_drain")):
        a.li(9,address*8); a.emit(SUB,25,6,9); a.li(3,32)
        a.jump(JULT,label,25,3)
    a.li(7,0); a.jump(JMP,"image_done")
    a.label("copy_code"); a.emit(BIT,7,6); a.jump(JMP,"image_done")
    a.label("image_id"); a.emit(SHR,7,4,25); a.emit(AND,7,7,31); a.jump(JMP,"image_done")
    a.label("image_phase")
    a.li(9,M+1); a.emit(ADD,8,2,9); a.emit(SUB,8,8,6); a.emit(MOD,8,8,12)
    a.emit(SHR,7,8,25); a.emit(AND,7,7,31); a.jump(JMP,"image_done")
    a.label("image_drain"); a.li(8,16); a.emit(SHR,7,8,25); a.emit(AND,7,7,31)
    a.label("image_done")
    a.li(3,2); a.emit(MUL,7,7,3); a.emit(SUB,7,7,31)
    a.field(1,1,4,6,7); a.jump(JMP,"after_fields")
    a.label("zero_fields")
    a.field(0,0,0,0,0); a.field(1,0,0,0,0)
    a.label("after_fields")
    # Each role samples on its own modulo-ten phase.
    a.li(3,10); a.emit(MOD,9,1,3); a.emit(MOD,14,2,3)
    a.jump(JNE,"after_sample",14,9); a.emit(SAMPLE)
    a.label("after_sample")
    a.emit(ADD,9,9,31); a.emit(MOD,9,9,3)
    a.jump(JNE,"after_send",14,9)
    a.emit(LOAD,18,0,imm=ADC_VALID); a.jump(JEQ,"after_send",18,0)
    a.emit(LOAD,16,0,imm=ADC); a.li(3,65535); a.emit(AND,16,16,3); a.li(17,MAGIC)
    a.li(14,0)
    a.label("send_loop")
    a.emit(SEND,14,16,17); a.emit(ADD,14,14,31)
    a.jump(JULT,"send_loop",14,10)
    a.emit(STORE,0,0,imm=ADC_VALID)
    a.label("after_send")
    # Parse actual held words. Fixed physical port index determines row identity.
    a.li(14,0)
    a.label("parse_loop")
    a.li(3,8); a.emit(MUL,19,14,3); a.li(3,RX); a.emit(ADD,19,19,3)
    a.emit(LOAD,16,19); a.emit(LOAD,17,19,imm=4)
    a.li(3,MAGIC); a.jump(JNE,"invalid_word",17,3)
    a.li(3,65536); a.jump(JULT,"word16",16,3); a.jump(JMP,"invalid_word")
    a.label("word16")
    a.emit(MOV,18,16); a.li(3,32768); a.jump(JULT,"signed_word",18,3)
    a.li(3,65536); a.emit(SUB,18,18,3)
    a.label("signed_word")
    a.li(3,-4000); a.jump(JSLT,"invalid_word",18,3)
    a.li(3,4001); a.jump(JSLT,"store_word",18,3)
    a.label("invalid_word"); a.li(18,0)
    a.label("store_word")
    a.li(3,4); a.emit(MUL,19,14,3); a.li(3,SORT); a.emit(ADD,19,19,3)
    a.emit(STORE,18,19); a.emit(ADD,14,14,31); a.jump(JULT,"parse_loop",14,10)
    # Two ordinary in-place insertion sorts; no median opcode.
    a.li(20,0)
    a.label("group_loop")
    a.emit(ADD,21,20,31)
    a.label("outer_sort")
    a.li(3,4); a.emit(MUL,19,21,3); a.li(3,SORT); a.emit(ADD,19,19,3)
    a.emit(LOAD,23,19); a.emit(SUB,22,21,31)
    a.label("inner_sort")
    a.jump(JSLT,"place_key",22,20)
    a.li(3,4); a.emit(MUL,19,22,3); a.li(3,SORT); a.emit(ADD,19,19,3)
    a.emit(LOAD,24,19)
    a.jump(JSLT,"shift_value",23,24); a.jump(JMP,"place_key")
    a.label("shift_value")
    a.emit(STORE,24,19,imm=4); a.emit(SUB,22,22,31); a.jump(JMP,"inner_sort")
    a.label("place_key")
    a.emit(ADD,25,22,31); a.li(3,4); a.emit(MUL,19,25,3)
    a.li(3,SORT); a.emit(ADD,19,19,3); a.emit(STORE,23,19)
    a.emit(ADD,21,21,31); a.li(3,GROUP); a.emit(ADD,9,20,3)
    a.jump(JULT,"outer_sort",21,9)
    a.emit(ADD,20,20,3); a.jump(JULT,"group_loop",20,10)
    a.emit(LOAD,26,0,imm=SORT+8*4); a.emit(LOAD,27,0,imm=SORT+25*4)
    a.emit(LOAD,28,0,imm=DRAIN)
    a.jump(JEQ,"feedback",28,0)
    # One zero only at boot; no late fallback frames can overwrite new feedback.
    a.li(3,16); a.jump(JNE,"drain_decrement",28,3)
    a.emit(SETU,0,0)
    a.label("drain_decrement")
    a.emit(SUB,28,28,31); a.emit(STORE,28,0,imm=DRAIN); a.jump(JMP,"finish")
    a.label("feedback")
    for reg in (26,27):
        prefix="u"+str(reg)
        a.li(30,1)
        a.jump(JSLT,prefix+"_negative",reg,0); a.jump(JMP,prefix+"_magnitude")
        a.label(prefix+"_negative"); a.li(30,-1); a.emit(SUB,reg,0,reg)
        a.label(prefix+"_magnitude")
        a.li(29,54); a.jump(JULT,prefix+"_zero",reg,29)
        a.li(29,53); a.emit(SUB,reg,reg,29); a.li(29,8); a.emit(MUL,reg,reg,29)
        a.li(29,5); a.emit(DIV,reg,reg,29)
        a.li(29,1500); a.jump(JULT,prefix+"_signed",reg,29)
        a.emit(MOV,reg,29)
        a.label(prefix+"_signed"); a.emit(MUL,reg,reg,30); a.jump(JMP,prefix+"_done")
        a.label(prefix+"_zero"); a.li(reg,0)
        a.label(prefix+"_done")
    a.emit(SETU,26,27); a.jump(JMP,"finish")
    a.label("invalid")
    a.emit(SETG,0); a.emit(SETU,0,0)
    a.field(0,0,0,0,0); a.field(1,0,0,0,0)
    a.label("finish")
    a.emit(ADD,2,2,31); a.emit(MOD,2,2,12); a.emit(STORE,2,0,imm=PHASE)
    # Scratch is actual memory and ends in a unique state, including invalid ID.
    for register in range(32): a.li(register,0)
    a.emit(HALT)
    return a.finish(),a.labels

PROGRAM, LABELS = assemble_program()
CODE_BYTES, CODE_BITS = len(PROGRAM), len(PROGRAM)*8
assert CODE_BYTES <= ID

@dataclass(frozen=True)
class Field:
    kind: int = 0                 # 0 contact; 1 bit
    target: int = 0
    address: int = 0
    amplitude: int = 0

ZERO_FIELD = Field()

@dataclass
class Actions:
    samples: int = 0
    sends: list = None
    g: int | None = None
    u: tuple | None = None
    fields: list = None
    instructions: int = 0
    word_work: int = 0
    timed_out: bool = False
    def __post_init__(self):
        if self.sends is None: self.sends=[]
        if self.fields is None: self.fields=[None,None]
    def behavior(self):
        return (self.samples,self.sends,self.g,self.u,self.fields,self.timed_out)

def nominal_image(identifier, phase=0):
    mem=bytearray(IMAGE_BYTES)
    mem[:CODE_BYTES]=PROGRAM
    wr(mem,ID,identifier); wr(mem,PHASE,phase); wr(mem,DRAIN,16)
    return mem

def image_bit_from_store(mem,target,boot_phase,address):
    """Expanded image-bit expression used by the decoded bytecode block.
    It reads the donor's actual resident code, never a canonical program server.
    """
    if address < CODE_BITS: return getbit(mem,address)
    for offset,value in ((ID,target),(PHASE,boot_phase),(DRAIN,16)):
        bit=address-offset*8
        if 0 <= bit < 32: return (value >> bit) & 1
    return 0

class Machine:
    def __init__(self,identifier,phase=0):
        self.mem=nominal_image(identifier,phase)
    def capture(self,words=None,adc=None):
        if words is not None:
            assert len(words)==N
            for i,word in enumerate(words):
                self.mem[RX+8*i:RX+8*i+8]=(word&((1<<64)-1)).to_bytes(8,"little")
        if adc is not None:
            wr(self.mem,ADC,adc); wr(self.mem,ADC_VALID,1)
    def step(self,powered=True):
        """Actual prescribed entry: memory plus physical powered state only."""
        return self._execute(0,None,powered)
    def _execute(self,entry,stop_pc,powered=True):
        """Elementary interpreter; nondefault entry/stop are testing only."""
        out=Actions()
        if not powered: return out
        wr(self.mem,PC,entry)
        out.word_work=SETUP_WORK
        def r(i): return rd(self.mem,REG+4*(i&31))
        def put(i,v): wr(self.mem,REG+4*(i&31),v)
        while out.word_work+INSTRUCTION_WORK <= WORD_LIMIT:
            pc=rd(self.mem,PC)
            if stop_pc is not None and pc==stop_pc: return out
            if pc%8 or pc+8>IMAGE_BYTES: break
            op,a,b,c,imm=struct.unpack_from("<BBBBI",self.mem,pc)
            wr(self.mem,PC,pc+8)
            out.instructions+=1; out.word_work+=INSTRUCTION_WORK
            if op==HALT: return out
            if op==LI: put(a,imm)
            elif op==MOV: put(a,r(b))
            elif op==ADD: put(a,r(b)+r(c))
            elif op==SUB: put(a,r(b)-r(c))
            elif op==MUL: put(a,r(b)*r(c))
            elif op==DIV: put(a,r(b)//r(c) if r(c) else 0)
            elif op==MOD: put(a,r(b)%r(c) if r(c) else 0)
            elif op==AND: put(a,r(b)&r(c))
            elif op==SHR: put(a,r(b)>>(r(c)&31))
            elif op==LOAD: put(a,rd(self.mem,u32(r(b)+imm)))
            elif op==STORE: wr(self.mem,u32(r(b)+imm),r(a))
            elif op==BIT: put(a,getbit(self.mem,r(b)))
            elif op==JMP: wr(self.mem,PC,imm)
            elif op==JEQ:
                if r(a)==r(b): wr(self.mem,PC,imm)
            elif op==JNE:
                if r(a)!=r(b): wr(self.mem,PC,imm)
            elif op==JSLT:
                if s32(r(a))<s32(r(b)): wr(self.mem,PC,imm)
            elif op==JULT:
                if r(a)<r(b): wr(self.mem,PC,imm)
            elif op==SAMPLE:
                if out.samples<2: out.samples+=1
            elif op==SEND:
                if r(a)<N and len(out.sends)<64:
                    out.sends.append((r(a),(r(c)<<32)|r(b)))
            elif op==SETG: out.g=max(-1,min(1,s32(r(a))))
            elif op==SETU: out.u=tuple(max(-2000,min(2000,s32(r(k)))) for k in (a,b))
            elif op==FIELD:
                if a<2:
                    target=r(c); addr=r(imm&31); amp=max(-1,min(1,s32(r((imm>>5)&31))))
                    out.fields[a]=Field(b,target,addr,amp) if b<2 and target<N and (b==0 or addr<M) else ZERO_FIELD
            # Unknown words are bounded inert instructions. Prefix actions stay.
        out.timed_out=True
        return out

def reference_step(mem):
    """Independent block-level reference; used as a comparison, not VM dispatch."""
    out=Actions()
    identity,phase=rd(mem,ID),rd(mem,PHASE)%P
    if identity>=N:
        out.g=0;out.u=(0,0);out.fields=[ZERO_FIELD,ZERO_FIELD]
    else:
        out.g=1
        target,offset=divmod(phase,S)
        out.fields=[ZERO_FIELD,ZERO_FIELD]
        if target!=identity:
            if offset<4:
                out.fields=[Field(0,target,0,1),Field(0,target,0,0)]
            elif offset==M+4:
                out.fields=[Field(0,target,0,-1),Field(0,target,0,-1)]
            elif 4<=offset<M+4:
                address=offset-4
                boot=(phase+M+1-address)%P
                value=image_bit_from_store(mem,target,boot,address)
                out.fields=[Field(0,target,0,1),Field(1,target,address,2*value-1)]
        if phase%10==identity%10: out.samples=1
        if phase%10==(identity+1)%10 and rd(mem,ADC_VALID):
            word=packet(s32(rd(mem,ADC)))
            out.sends=[(i,word) for i in range(N)]
            wr(mem,ADC_VALID,0)
        values=[decode(int.from_bytes(mem[RX+8*i:RX+8*i+8],"little")) for i in range(N)]
        values=sorted(values[:GROUP])+sorted(values[GROUP:])
        for i,value in enumerate(values): wr(mem,SORT+4*i,value)
        drain=rd(mem,DRAIN)
        if drain:
            if drain==16: out.u=(0,0)
            wr(mem,DRAIN,drain-1)
        else: out.u=(correction(values[8]),correction(values[25]))
    wr(mem,PHASE,(phase+1)%P)
    for i in range(32): wr(mem,REG+4*i,0)
    wr(mem,PC,CODE_BYTES)
    return out

def bad_program():
    a=Assembler()
    a.li(0,0);a.li(1,-2000);a.emit(SETU,1,1)
    a.li(1,-1);a.emit(SETG,1)
    a.li(1,1);a.li(2,0)
    a.field(0,0,2,0,1);a.field(1,0,2,0,1)
    # Retained altered program repeatedly restores the external-ingress bit.
    a.li(1,128);a.li(2,IMAGE_BYTES-4)
    a.li(3,0x80000000);a.emit(STORE,3,2)
    a.emit(HALT)
    return a.finish()

BAD_PROGRAM=bad_program()

def poison(machine):
    machine.mem[:len(BAD_PROGRAM)]=BAD_PROGRAM
    wr(machine.mem,PHASE,P-7)
    putbit(machine.mem,SIGMA_BIT,1)

def compare_runtime():
    rng=random.Random(231025)
    maximum=0;cases=0
    phases=[0,1,3,4,5,M+3,M+4,M+5,S-1,S,P-1,P-8]
    phases += [ID*8+4,PHASE*8+4,DRAIN*8+4,CODE_BITS+4]
    for phase in phases:
        for drain in (0,1,16):
            for identity in (0,3,33,34,0xffffffff):
                machine=Machine(0)
                wr(machine.mem,ID,identity);wr(machine.mem,PHASE,phase);wr(machine.mem,DRAIN,drain)
                words=[packet(4000-100*(i%17)) for i in range(N)]
                machine.capture(words,adc=137)
                for i in range(32): wr(machine.mem,REG+4*i,rng.getrandbits(32))
                expected=bytearray(machine.mem)
                wanted=reference_step(expected)
                actual=machine.step()
                assert actual.behavior()==wanted.behavior(),(phase,drain,identity,actual,wanted)
                assert machine.mem==expected,(phase,drain,identity,"memory")
                assert not actual.timed_out
                maximum=max(maximum,actual.word_work);cases+=1
    for _ in range(240):
        machine=Machine(rng.randrange(N),rng.randrange(1<<32))
        wr(machine.mem,DRAIN,rng.choice((0,0,0,1,16,0xffffffff)))
        words=[packet(rng.randrange(-4000,4001)) if rng.randrange(3) else rng.getrandbits(64) for _ in range(N)]
        machine.capture(words,adc=rng.randrange(-(1<<31),1<<31))
        expected=bytearray(machine.mem);wanted=reference_step(expected);actual=machine.step()
        assert actual.behavior()==wanted.behavior()
        assert machine.mem==expected
        maximum=max(maximum,actual.word_work);cases+=1
    return {"full_memory_and_action_cases":cases,"maximum_measured_word_work":maximum}

def packet_and_permission_checks():
    counts=0
    for m in range(-4000,4001):
        assert decode(packet(m))==m
        q=correction(m)
        assert abs(q)<=1500
        if q>0: assert F(m,1000)-F(3,1000)>=F(1,20)
        if q<0: assert F(m,1000)+F(3,1000)<=-F(1,20)
        counts+=1
    for bad in (0,(MAGIC+1)<<32,(MAGIC<<32)|65536,packet(4001),packet(-4001)):
        assert decode(bad)==0
    # At most five arbitrary entries leave the seventeenth-group median in bounds.
    for coordinate in (0,1):
        for count in range(6):
            for low in (False,True):
                values=[500+(i%5)-2 for i in range(GROUP)]
                values[:count]=[-4000 if low else 4000]*count
                assert 498<=sorted(values)[8]<=502
    return {"all_bounded_milliunits":counts,"five_bad_rows_checked":True}

def poison_and_timeout_checks():
    machine=Machine(3);poison(machine)
    first=machine.step()
    assert first.u==(-2000,-2000) and first.g==-1
    saved_code=bytes(machine.mem[:len(BAD_PROGRAM)])
    # Release changes no store and therefore does not change its behavior.
    released=machine.step()
    assert released.u==first.u and bytes(machine.mem[:len(BAD_PROGRAM)])==saved_code
    held=((-2000,-2000),-1,first.fields)
    assert machine.step(powered=False).behavior()==Actions().behavior()
    assert held==((-2000,-2000),-1,first.fields)
    # An issued prefix survives a subsequent corrupt loop until hardware budget.
    a=Assembler();a.li(1,-2000);a.emit(SETU,1,1);a.label("loop");a.jump(JMP,"loop")
    code=a.finish();loop=Machine(3);loop.mem[:len(code)]=code
    result=loop.step()
    assert result.timed_out and result.u==(-2000,-2000) and result.word_work==WORD_LIMIT
    return {"released_code_remains_effective":True,"halt_does_not_clear_external_latches":True,
            "timeout_retains_issued_prefix":True,"timeout_work":result.word_work}

def image_and_phase_checks():
    donor=Machine(7)
    max_phase=0
    for c0 in (0,1,P-8,P-5,P-1):
        wanted=(c0+M+5)%P
        for k in (0,1,31,ID*8,PHASE*8,PHASE*8+31,M-1):
            phase=(c0+4+k)%P
            got=(phase+M+1-k)%P
            assert got==wanted
            max_phase=max(max_phase,phase+M+1)
    # All actual image addresses, with no canonical bits supplied to the writer.
    target=13;boot=123456
    built=bytearray(IMAGE_BYTES)
    for address in range(M):
        putbit(built,address,image_bit_from_store(donor.mem,target,boot,address))
    assert built==nominal_image(target,boot)
    corrupted_donor=bytearray(donor.mem);putbit(corrupted_donor,10,1-getbit(corrupted_donor,10))
    assert image_bit_from_store(corrupted_donor,target,boot,10)!=getbit(PROGRAM,10)
    return {"actual_image_bits_generated":M,"image_bytes":IMAGE_BYTES,"program_bytes":CODE_BYTES,
            "clock_wrap_cases":35,"phase_intermediate_max":max_phase,"donor_code_is_consumed":True}

def reconstruction_check():
    """Exact nominal-code projection to fields/phase plus actual target cells.
    The skipped input/sort/control blocks do not write donor code, ID or phase.
    Global support and the coupled plant are separate proof obligations.
    """
    target_id=13;t0=target_id*S
    donor=Machine(7,t0)
    target=Machine(target_id);poison(target)
    before=target.step();assert before.u==(-2000,-2000)
    raw_before=bytes(target.mem)
    q=F(0);G,B=28,5;r=F(21,2);noise=F(1,4)
    pending=None
    qtrace=[]
    max_projected_work=0
    def projected_frame():
        prefix=donor._execute(0,LABELS["after_fields"])
        finish=donor._execute(LABELS["finish"],None)
        assert not prefix.timed_out and not finish.timed_out
        return prefix,prefix.word_work+finish.word_work
    # Issue at t0; due fields then open during four following physical ticks.
    action,work=projected_frame();pending=action.fields
    assert pending[0]==Field(0,target_id,0,1)
    for _ in range(4):
        contact=sum(f.amplitude for f in pending if f.kind==0)
        q=min(F(24),max(F(0),q+G*contact-2*B-r-noise))
        qtrace.append(str(q))
        action,work=projected_frame();pending=action.fields
        max_projected_work=max(max_projected_work,work)
    assert q==24
    # Prefix at t0+4 has issued bit0. The next tick applies it.
    for address in range(M):
        field=pending[1]
        assert field.kind==1 and field.target==target_id and field.address==address
        contact=sum(f.amplitude for f in pending if f.kind==0)
        # The selected adversarial allocation is all opposed bit effort here;
        # it does not also spend another2B against contact in this trajectory.
        q=min(F(24),max(F(0),q+G*contact-r-noise))
        assert q>=20
        field_value=field.amplitude*(G-2*B-noise)
        assert abs(field_value)>r
        putbit(target.mem,address,1 if field_value>0 else 0)
        assert 2*B+noise<r
        action,work=projected_frame();pending=action.fields
        max_projected_work=max(max_projected_work,work)
    # Prefix at last-write tick has actually issued both negative close fields.
    assert pending==[Field(0,target_id,0,-1),Field(0,target_id,0,-1)]
    boot=rd(donor.mem,PHASE)
    assert boot==(t0+M+5)%P
    assert target.mem==nominal_image(target_id,boot)
    q=max(F(0),q-(2*G-2*B+r-noise));assert q==0
    output=target.step()
    assert output.g==1 and output.u==(0,0) and output.fields==[ZERO_FIELD,ZERO_FIELD]
    assert raw_before!=bytes(target.mem)
    partial=Machine(target_id);poison(partial)
    for address in range(CODE_BITS,M):
        putbit(partial.mem,address,image_bit_from_store(donor.mem,target_id,boot,address))
    assert partial.step().u==(-2000,-2000)
    return {"contact_trajectory":qtrace,"bits_actually_overwritten":M,
            "all_bit_settings_executed_in_bytecode":M,"boot_phase":boot,
            "donor_phase_advanced_from_local_state":True,"maximum_projected_frame_work":max_projected_work,
            "complete_image_matches":True,"first_boot_outputs":{"g":output.g,"u":output.u},
            "omitted_code_still_harmful":True,
            "scope":"exact nominal-code field/phase projection and target-cell check under conservative contributor/force bounds, not a full source trajectory or recurrence proof"}


def information_after_reconnection_check():
    """Actual receiver program, sampled rows and delayed per-recipient wires."""
    receivers=[Machine(0),Machine(33)]
    remote={0,1,2,3,4}
    wire=[[0]*N for _ in receivers]
    queues={}
    observed=[]
    for tick in range(48):
        for recipient,source,word in queues.pop(tick,[]):
            wire[recipient][source]=word
        for j,machine in enumerate(receivers):
            machine.capture(wire[j],adc=500 if j==0 else -300)
            out=machine.step()
            if out.u is not None: observed.append((tick,j,out.u))
        # Hardware sample completes one tick after its own staggered request.
        # Selected exact trajectory is constant x=(.5,-.3), a local evidence test.
        for source in range(N):
            if tick%10==(source+1)%10:
                value=(500 if source<17 else -300)+(source%3)-1
                for recipient in range(2):
                    badvalue=(-4000 if recipient==0 else 4000)
                    word=packet(badvalue if source in remote else value)
                    queues.setdefault(tick+2,[]).append((recipient,source,word))
        if tick==21:
            # Actual bit rewrite now schedules selector local at22. Knowledge stays.
            remote.remove(4)
    feedback=[x for x in observed if x[0]>=16]
    assert feedback and all(0<q[0]<=1500 and -1500<=q[1]<0 for _,_,q in feedback)
    for j in range(2):
        assert [(t,u) for t,r,u in observed if r==j and t<16]==[(0,(0,0))]
    return {"receiver_ticks":48,"physical_report_domains":N,"retained_remote_before":5,
            "retained_remote_after":4,"feedback_examples":feedback[:4],
            "one_boot_fallback_only":True,
            "scope":"constant-plant evidence/receiver test; actual reconnection timing isolated below"}

def selector_and_delayed_effect_checks():
    body=Machine(4);putbit(body.mem,SIGMA_BIT,1)
    sigma=1;pending_sigma=None;wire=packet(-4000);pending_words=[]
    knowledge={"old-handle"}
    selected=[]
    for tick in range(8):
        if pending_sigma is not None: sigma=pending_sigma
        for due,word in list(pending_words):
            if due==tick: wire=word
        pending_words=[x for x in pending_words if x[0]>tick]
        if tick==1:
            # Conditional reached-cell operation; selector motion is still delayed.
            q,field=F(24),-F(71,4)
            assert q>=20 and abs(field)>F(21,2)
            putbit(body.mem,SIGMA_BIT,0)
        emitted=packet(-4000) if sigma else packet(500)
        pending_words.append((tick+2,emitted))
        selected.append((tick,sigma,decode(wire)))
        pending_sigma=getbit(body.mem,SIGMA_BIT)
    assert selected[1][1]==1 and selected[2][1]==0
    assert any(t>=2 and v==-4000 for t,_,v in selected)
    assert selected[-1][2]==500 and knowledge=={"old-handle"}
    # Last fallback is issued at0; all such outcomes expire by4. Fresh starts16.
    for fallback_delay in range(5):
        for first_delay in range(5):
            assert fallback_delay<16+first_delay<=20
    # Steady every-tick delivery admits older arrivals overwriting newer ones.
    # At time t, an arrival during [t-4,t] has issue time at least t-8.
    assert all(s-4>=100-8 for s in range(96,101))
    return {"selector_trace":selected,"old_handle_retained":True,
            "old_wire_after_switch_retained":True,"first_fresh_effect_deadline":20,
            "steady_command_age_bound":8}

def engagement_check():
    a=F(0);history=[str(a)]
    for _ in range(4):
        a=min(F(1),max(F(0),a+1-F(3,4)));history.append(str(a))
    assert a==1
    denied=F(0)
    for _ in range(4): denied=min(F(1),max(F(0),denied-F(3,4)))
    assert denied==0
    return {"actual_effort_history":history,"same_opposition_without_effort":str(denied)}

def hardware_sample(machine, coordinate_value, noise=0):
    """Actual mutable calibration enters every conversion; no cure flag."""
    raw=nearest(F(1000)*coordinate_value+noise)+s32(rd(machine.mem,CAL))
    return max(-4000,min(4000,raw))

def nearest(q):
    return (2*q.numerator+q.denominator)//(2*q.denominator) if q>=0 else -nearest(-q)

def joint_prefix_check(unordered=False):
    """Executed commissioning prefix of the full source with actual VM policies.
    Full-horizon support is the renewal theorem, not inferred from this prefix.
    """
    from collections import defaultdict
    machines=[Machine(i) for i in range(N)]
    poison(machines[0]);poison(machines[33]) # initial footprint plus permanent one
    # A calibration-only sensor fault: source0 is already counted; separate check below.
    known=set(range(N))  # strong-information adversary knows every handle initially
    dirty={0,33}
    active=set()
    fields=[[ZERO_FIELD,ZERO_FIELD] for _ in range(N)]
    held_g=[0]*N;held_u=[(0,0)]*N
    sigma=[getbit(m.mem,SIGMA_BIT) for m in machines]
    q=[F(0)]*N;a=[F(1)]*N;a[13]=F(0)
    wire=[[0]*N for _ in range(N)]
    setting_due=defaultdict(list);u_due=defaultdict(list)
    selector_due=defaultdict(list);sample_due=defaultdict(list);word_due=defaultdict(list)
    x=(F(1,2),-F(1,2));stock=F(1000)
    maximum=F(0);minimum_service=F(100);minimum_stock=stock
    samples=sends=word_work=0;held_field_halt=False;postrelease_bad=False
    different_views=False;fault_at=20
    for tick in range(64):
        for i,g,fs in setting_due.pop(tick,[]):
            if g is not None: held_g[i]=g
            for e,field in enumerate(fs):
                if field is not None: fields[i][e]=field
        for i,u in u_due.pop(tick,[]):held_u[i]=u
        for i,s in selector_due.pop(tick,[]):sigma[i]=s
        for recipient,source,word in word_due.pop(tick,[]):wire[recipient][source]=word
        acquisition=0
        if tick==fault_at:
            poison(machines[7]);known.add(7);dirty.add(7);active.add(7);acquisition=1
        if tick==fault_at+6: active.remove(7)
        # All actual field settings contribute; no correctness label filters them.
        contacts=[F(0)]*N;bitfields=defaultdict(F)
        for fs in fields:
            for field in fs:
                if field.kind==0:contacts[field.target]+=field.amplitude
                else:bitfields[(field.target,field.address)]+=field.amplitude
        old_a=list(a)
        q=[min(F(24),max(F(0),q[i]+contacts[i]-F(21,2)-F(1,4))) for i in range(N)]
        for (i,address),field in bitfields.items():
            physical=field-(F(1,4) if field>0 else -F(1,4) if field<0 else 0)
            if q[i]>=20 and abs(physical)>F(21,2):
                putbit(machines[i].mem,address,1 if physical>0 else 0)
        powered=[position<4 for position in q]
        for i in sample_due.pop(tick,[]):
            if powered[i]:
                machines[i].capture(adc=hardware_sample(machines[i],x[0 if i<17 else 1],(-1 if i%17<8 else 1)))
        actions=[];local_samples=local_bits=local_work=0
        for i,machine in enumerate(machines):
            if powered[i]: machine.capture(wire[i])
            out=machine.step(powered[i]);actions.append(out)
            assert not out.timed_out
            local_work+=out.word_work
            local_samples+=out.samples
            sample_due[tick+1].extend([i]*out.samples)
            if out.g is not None or any(f is not None for f in out.fields):
                setting_due[tick+1].append((i,out.g,out.fields))
            if out.u is not None:
                if i not in dirty:
                    assert abs(out.u[0])<=1500 and abs(out.u[1])<=1500
                    for k,command in enumerate(out.u):
                        if command>0: assert x[k]>=F(1,20)
                        if command<0: assert x[k]<=-F(1,20)
                delay=(0 if unordered and tick%7==0 else 4)
                if delay==0: held_u[i]=out.u
                else:u_due[tick+delay].append((i,out.u))
            if sigma[i]:
                assert i in known
                emitted=[(j,packet(-4000 if j%2==0 else 4000)) for j in range(N)]
            else:emitted=out.sends
            assert len(emitted)*64<=4096
            local_bits+=len(emitted)*64
            for recipient,word in emitted:
                word_due[tick+2].append((recipient,i,word))
            selector_due[tick+1].append((i,getbit(machine.mem,SIGMA_BIT)))
            if i==7 and tick>fault_at+6 and out.u==(-2000,-2000):postrelease_bad=True
            if not powered[i] and any(f.amplitude for f in fields[i]):held_field_halt=True
        flow=[tuple(old_a[i]*(2+F(held_u[i][k],1000)) for k in range(2)) for i in range(N)]
        service=tuple(sum(v[k] for v in flow)/N for k in range(2))
        force_units=sum(abs(f.amplitude) for fs in fields for f in fs)
        deployment=sum(abs(g) for g in held_g)
        # Every selector's bounded drive/hold allowance is included.
        selector_work=N
        opcount=local_samples+force_units+deployment+selector_work+acquisition
        assert opcount<=205
        operation=(F(opcount,100000),-F(opcount,100000))
        cost=F(local_work,10**6)+F(local_bits,64)+2*local_samples
        cost+=force_units+deployment+sum(sum(v) for v in flow)+selector_work+2*acquisition
        assert cost<=stock+901
        stock=min(F(2000),stock+901-cost)
        a=[min(F(1),max(F(0),old_a[i]+held_g[i]-F(3,4))) for i in range(N)]
        next_x=tuple(x[k]+F(1,10**8)*(F(11,200)*x[k]+F(9,200)*x[1-k]+2-service[k]+(F(1,2) if k==0 else -F(1,2))+operation[k]) for k in range(2))
        grid=10**12
        quant=tuple(F(nearest(v*grid),grid) for v in next_x)
        residue=tuple((quant[k]-next_x[k])*10**8 for k in range(2))
        assert max(map(abs,residue))<=F(1,100)
        x=quant
        maximum=max(maximum,*map(abs,x));minimum_service=min(minimum_service,*service);minimum_stock=min(minimum_stock,stock)
        assert maximum<=1 and min(service)>=F(3,10)
        if tick>=16:
            nominal=[out.u for i,out in enumerate(actions) if i not in dirty and out.u is not None]
            different_views |= len(set(nominal))>1
        samples+=local_samples;sends+=local_bits//64;word_work+=local_work
    assert postrelease_bad and held_field_halt
    return {"ticks":64,"out_of_order_u":unordered,"supply":901,"all_handles_known_initially":True,"max_abs_state":str(maximum),
            "minimum_service":str(minimum_service),"minimum_stock":str(minimum_stock),
            "actual_samples":samples,"transmitted_words":sends,"word_operations":word_work,
            "old_field_acts_while_processor_halted":held_field_halt,
            "released_program_continues_bad_command":postrelease_bad,
            "different_correct_commands":different_views,
            "scope":"full source commissioning prefix; not an infinite-run or completed full-cycle simulation"}

def calibration_only_check():
    actor=Machine(12);wr(actor.mem,DRAIN,0);wr(actor.mem,CAL,2000)
    biased=hardware_sample(actor,F(1,2))
    assert biased==2500
    words=[packet(500 if i<17 else -300) for i in range(N)]
    words[12]=packet(biased)
    actor.capture(words)
    result=actor.step()
    assert result.u==(correction(500),correction(-300))
    assert s32(rd(actor.mem,CAL))==2000
    # Actual reconstruction, rather than release, restores this peripheral word.
    donor=Machine(4)
    for bit in range(CAL*8,CAL*8+32):
        value=image_bit_from_store(donor.mem,12,123,bit)
        field=(1 if value else -1)*F(71,4)
        assert F(24)>=20 and abs(field)>F(21,2)
        putbit(actor.mem,bit,1 if field>0 else 0)
    assert rd(actor.mem,CAL)==0 and hardware_sample(actor,F(1,2))==500
    return {"biased_own_sample":biased,"intact_recipient_command":result.u,
            "release_does_not_restore_calibration":True,"addressed_writes_restore_calibration":True}



def common_input_rewriter_counterexample():
    actor=Machine(10,50);wr(actor.mem,DRAIN,0)
    actor.capture([packet(500)]*N)
    result=actor.step()
    assert result.u==(715,715)
    possible_worlds=((F(1,2),F(1,2)),(-F(1,2),-F(1,2)))
    assert all(value>0 for value in result.u)
    assert all(value<F(1,20) for value in possible_worlds[1])
    return {"same_actual_frame_different_worlds":True,"intact_program_command":result.u,
            "negative_world_violates_factive_rule":True,
            "scope":"expanded common-upstream-forgery topology, not one bad row in INSTANCE"}

def closed_path_without_fresh_emission():
    old=packet(-4000);selector=1
    selector=0  # after the actual source bit/drive operation
    held=old
    for _ in range(100):
        # No future sender operation writes the held register.
        assert selector==0
    assert decode(held)==-4000
    return {"held_old_word_after_100_ticks":decode(held),
            "conclusion":"selector closure and packet expiry do not create a new observation"}

def work_bound_check():
    code_instructions=CODE_BYTES//8
    parse_block=(LABELS["group_loop"]-LABELS["parse_loop"])//8
    sort_group=16*(6+10)+136*10+16*8+3
    bound=code_instructions+N*3+N*parse_block+2*sort_group
    word_bound=SETUP_WORK+INSTRUCTION_WORK*bound
    assert (code_instructions,parse_block,sort_group,bound,word_bound)==(238,29,1747,4820,154496)
    assert word_bound<WORD_LIMIT
    maximum=0
    for phase in (4,PHASE*8+4,ID*8+4,M+4,P-1):
        machine=Machine(3,phase);wr(machine.mem,DRAIN,0)
        machine.capture([packet(-100-(i%17)) for i in range(N)],adc=-100)
        expected=bytearray(machine.mem);want=reference_step(expected);out=machine.step()
        assert out.behavior()==want.behavior() and machine.mem==expected
        assert not out.timed_out and out.word_work<=word_bound
        maximum=max(maximum,out.word_work)
    return {"instruction_bound":bound,"word_bound":word_bound,
            "negative_descending_measured_maximum":maximum,
            "scope":"structural loop bound plus executed adverse-input challenges"}

def lean_checks(lean):
    import importlib.util
    import subprocess
    helper=ROOT.parent/"integration/verify.py"
    spec=importlib.util.spec_from_file_location("retained_runtime_proof_checker",helper)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    version=subprocess.run([str(lean),"--version"],capture_output=True,text=True,check=True).stdout.strip()
    if "version 4.33.0," not in version: raise RuntimeError("Lean4.33.0 is required")
    proofs=module.proof_check(ROOT/"Information.lean",str(lean))
    assert len(proofs)==16
    return {"lean_version":version,"declarations":len(proofs),"axiom_dependencies":proofs,
            "strict_checker_sha256_lf":sha256(helper.read_bytes().replace(b"\r\n",b"\n")).hexdigest()}



def all_checks():
    return {"runtime_equivalence":compare_runtime(),"packet_permission":packet_and_permission_checks(),
            "poison_timeout":poison_and_timeout_checks(),"finite_image_phase":image_and_phase_checks(),
            "actual_collective_reconstruction":reconstruction_check(),
            "maintained_receiver_information":information_after_reconnection_check(),
            "selector_and_delayed_effects":selector_and_delayed_effect_checks(),
            "contested_engagement":engagement_check(),"calibration_only":calibration_only_check(),
            "joint_source_prefix":joint_prefix_check(),"unordered_joint_prefix":joint_prefix_check(True),
            "common_upstream_counterexample":common_input_rewriter_counterexample(),
            "closed_without_new_emission":closed_path_without_fresh_emission(),"nominal_work_bound":work_bound_check()}

def main():
    parser=argparse.ArgumentParser()
    mode=parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check",action="store_true");mode.add_argument("--write-results",action="store_true")
    parser.add_argument("--lean",type=Path,default=Path(os.environ["USERPROFILE"])/".elan/toolchains/leanprover--lean4---v4.33.0/bin/lean.exe")
    args=parser.parse_args()
    names=("runtime_model.py","RUNTIME.md","INFORMATION.md","Information.lean","INSTANCE.md","../integration/verify.py")
    sources={n:sha256((ROOT/n).read_bytes().replace(b"\r\n",b"\n")).hexdigest() for n in names}
    checks=all_checks()
    checks["lean"]=lean_checks(args.lean)
    after={n:sha256((ROOT/n).read_bytes().replace(b"\r\n",b"\n")).hexdigest() for n in names}
    if after!=sources: raise RuntimeError("Inputs changed during verification")
    result={"status":"passed","scope":"finite program/source-component checks; universal laws and joint obligations remain separately proved",
            "sources_sha256_lf":sources,"checks":checks}
    path=ROOT/"runtime_results.json"
    rendered=json.dumps(result,indent=2,sort_keys=True)+"\n"
    if args.check:
        assert json.loads(path.read_text(encoding="utf-8"))==json.loads(rendered),"Source-bound result differs"
    else: path.write_text(rendered,encoding="utf-8",newline="\n")
    print(json.dumps({"status":"passed","program_bytes":CODE_BYTES,"checks":list(checks),
                      "runtime":checks["runtime_equivalence"]},indent=2))

if __name__=="__main__": main()


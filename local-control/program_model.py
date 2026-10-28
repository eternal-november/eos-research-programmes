"""Ordinary finite instruction semantics and bank-program compilation/checks.

The compiler runs only off line. Every runtime decision fetches actual C.
No run path recognizes the intended program or calls a host-language helper.
"""
from __future__ import annotations
import argparse, ast, hashlib, json, math, sys
from fractions import Fraction as F
from dataclasses import dataclass
from pathlib import Path
from collections import Counter

HERE=Path(__file__).resolve().parent
SOURCE=HERE/'program_source.py'
WORD_BITS=256; WORD_MASK=(1<<WORD_BITS)-1; SIGN=1<<(WORD_BITS-1)
CELL_BITS=192; CELL_MASK=(1<<CELL_BITS)-1
FIELD_BITS=24; FIELD_MASK=(1<<FIELD_BITS)-1; IMM_BITS=112; IMM_MASK=(1<<IMM_BITS)-1
LI,MOV,ADD,SUB,MUL,DIV,MOD,SHL,AND,OR,EQ,LT,LE,NOT,LOAD,STORE,LOADC,STOREC,JMP,JZ,CALL,RET,IO,HALT=range(1,25)
OPNAMES={v:k for k,v in list(globals().items()) if isinstance(v,int) and k in ('LI','MOV','ADD','SUB','MUL','DIV','MOD','SHL','AND','OR','EQ','LT','LE','NOT','LOAD','STORE','LOADC','STOREC','JMP','JZ','CALL','RET','IO','HALT')}
PRIMITIVES=('fast_cmp','request','reply_equal','source_start_fast','source_ready','source_iadd_constant','source_offer_fast','source_capture_request','source_ilt','source_idiv','source_imod','source_start_cell','source_ishl','source_iadd','source_offer_reply','source_offer_missing','source_invalidate','send_command','world','yield_frame','own_equal','write_own','cpu_count','fast_equal','source_iconstant','source_icopy','source_ilt_register','source_isub_constant','source_start_functional','fast_range','source_ieq')
PRIM={name:i for i,name in enumerate(PRIMITIVES)}
PRIM_ARITY=dict(zip(PRIMITIVES,(4,4,4,1,0,3,2,2,2,3,3,1,3,3,2,2,0,2,2,0,4,4,0,4,2,2,2,3,4,5,2)))
PRIM_WORD_COST={name:1 for name in PRIMITIVES}



def require(ok,message):
    if not ok: raise RuntimeError(message)
def signed(value):
    value &= WORD_MASK
    return value-(1<<WORD_BITS) if value&SIGN else value
def encode(op,a=0,b=0,c=0,immediate=0):
    require(0<=op<256 and all(0<=x<=FIELD_MASK for x in (a,b,c)),'Instruction field overflow')
    require(-(1<<(IMM_BITS-1))<=immediate<(1<<(IMM_BITS-1)),'Immediate overflow')
    return op|(a<<8)|(b<<32)|(c<<56)|((immediate&IMM_MASK)<<80)
def decode(cell):
    op=cell&255;a=(cell>>8)&FIELD_MASK;b=(cell>>32)&FIELD_MASK;c=(cell>>56)&FIELD_MASK
    imm=(cell>>80)&IMM_MASK
    if imm&(1<<(IMM_BITS-1)):imm-=1<<IMM_BITS
    return op,a,b,c,imm


@dataclass(frozen=True)
class Design:
    degree:int=2
    bays:int=3
    origins:int=3
    image_cells:int=8192
    fast_batch:int=2
    query_batch:int=2
    maintenance_batch:int=1
    entry_frames:int=2
    read_wait_frames:int=2
    watch_frames:int=40
    conversion_polls:int=8
    pad_iterations:int=4
    frame_steps:int=262144
    boot_drain_steps:int=0
    connectors_a:int=2
    connectors_b:int=2
    post_stage_frames:int=0
    plant_entry_frames:int=2
    own_bay:int=1
    physical_parameters:tuple=()

    def constants(self):
        d,b=self.degree,self.bays
        require(d>0 and b>0 and self.origins>0 and self.origins%2==1 and self.connectors_a>0 and self.connectors_b>0,'Invalid finite design')
        require(0<=self.own_bay<b,'Own physical bay outside layout')
        v={'CAM':0,'ANCHOR':1,'MODE':2,'BLEND':3,'CUT_A':4,'CLAMP_A':6,'RESET_A':8,'ISO_DEF_A':10,'SHUNT_DEF_A':12,'ENERGY_A':14,'ACT_A':16,'SEAT_A':16+2*b}
        pose_words=16+4*b
        v.update(CUT_OPEN_A=pose_words,CLAMP_OPEN_A=pose_words+2,RESET_OPEN_A=pose_words+4,POWER_OFF_A=pose_words+6,ACT_ZERO_A=pose_words+8,ACT_POWER_A=pose_words+8+2*b,ISO_SEATED_A=pose_words+8+4*b,SHUNT_SEATED_A=pose_words+10+4*b,SHUNT_OPEN_A=pose_words+12+4*b,BLEND_AT_A=pose_words+14+4*b,CAM_ENTRY_A=pose_words+16+4*b,ANCHOR_IS_A=pose_words+18+4*b,ANCHOR_IS_B=pose_words+19+4*b)
        v.update(NORMAL_STOP=36+8*b,ABORT_FULL=37+8*b)
        view_words=38+8*b
        state={'CURSOR':0,'COMPLETED':1,'JOINED':2,'SCAN_BAY':3,'SCAN_ADDRESS':4,'SCAN_MATCH':5,'SELECTED':6,'VERIFY_ADDRESS':7,'PENDING':8,'CELL_KEY':9,'CELL_WAIT':10,'ABORT':11,'TIMER':12,'WATCH_HALF':13,'LAST_PHASE':14,'HIGH':15,'ACCEPTED':16,'VIEW':16+b}
        target_words=16+b+pose_words+19
        state.update({name:16+b+pose_words+k for k,name in enumerate(("CMD_ROUTE","CMD_CAM","CMD_MODE","CMD_ACTION","CMD_SIDE","CMD_INDEX","CMD_AMPLITUDE"))})
        state.update(STAGE_ID=target_words-12,STAGE_WAIT=target_words-11,VIEW_VALID=target_words-10,ABORT_SIGNATURE=target_words-9,ABORT_WAIT=target_words-8,CAM_VALID=target_words-7,CLAMP_VALID_A=target_words-6,RANK_VALID=target_words-4,EXITING_ABORT=target_words-3,EXIT_OBSERVED=target_words-2,EXIT_WAIT=target_words-1)
        c=dict(STACK_WORDS=32,ENTRY=32,FAST_CURSOR=33,QUERY_CURSOR=34,MAINT_CURSOR=35,FOLD_FAILED=36,EST_VALID=37,PLANT_ENTRY=38,TARGET_BASE=64,TARGET_WORDS=target_words,DATA_WORDS=64+d*target_words,
               DEGREE=d,BAYS=b,ORIGINS=self.origins,QUORUM=self.origins//2+1,IMAGE_CELLS=self.image_cells,SYMBOL_BITS=CELL_BITS,CODE_KEYS=2*b*self.image_cells,
               FAST_BATCH=self.fast_batch,QUERY_BATCH=self.query_batch,MAINT_BATCH=self.maintenance_batch,ENTRY_FRAMES=self.entry_frames,PLANT_ENTRY_FRAMES=self.plant_entry_frames,ROW_VERIFY_RADIUS=40,POSE_VERIFY_RADIUS=100,CAM_VERIFY_RADIUS=1,CLAMP_VERIFY_RADIUS=100,READ_WAIT_FRAMES=self.read_wait_frames,WATCH_FRAMES=self.watch_frames,CONVERSION_POLLS=self.conversion_polls,PAD_ITERATIONS=self.pad_iterations,FRAME_STEPS=self.frame_steps,BOOT_DRAIN_STEPS=self.boot_drain_steps,COUNTER_MOD=1<<64,OWN_BAY=self.own_bay,
               POSE_WORDS=pose_words,VIEW_WORDS=view_words,FAST_TARGET_KEYS=view_words+4,FAST_KEYS=3+d*(view_words+4),CONNECTORS_A=self.connectors_a,CONNECTORS_B=self.connectors_b,RAW_TARGET_HEADS=view_words+2*(self.connectors_a+self.connectors_b),RAW_MAINT_HEADS=d*(view_words+2*(self.connectors_a+self.connectors_b)),POST_STAGE_FRAMES=self.post_stage_frames,CAM_ERROR=0,LOAD_SENSOR_CAP=3000,SENSE_BIAS=32,SENSE_ERROR=10,HIGH_STEP=10,LOAD_MARGIN=100,ISOLATION_MARGIN=100,POSE_MAX=1000000,PHASES=13,GUARD=22,SEGMENT=23,CLAMP_LIMIT=300,RESET_LIMIT=160,CUT_LIMIT=60,BLEND_LIMIT=20000,WARM_AT=50000,POWER_AT=10000,RESERVE_CAP=50000,PROGRESS_ERROR=100,SHUNT_MARGIN=50,ISO_MARGIN=50,JOIN_ERROR=22,JOIN_MARK=5,FORCE=20,
               NEUTRAL_COMMAND=32*64+32*4096+32*(1<<40),PORTS=11,MODE_PORT=0,CAM_PORT=1,BLEND_PORT=2,ISO_PORT=3,SHUNT_PORT=4,CUT_PORT=5,ACT_PORT=6,CLAMP_PORT=7,RESET_PORT=8,INSERT_PORT=9,REWIND_PORT=10)
        c.update(v);c.update(state)
        for name,value in self.physical_parameters:
            require(name in c and isinstance(value,int),"Unknown design parameter override")
            c[name]=value
        require(c["POSE_MAX"]>=max(c["WARM_AT"],c["RESERVE_CAP"],c["BLEND_LIMIT"]),"Pose encoding excludes a consumed coordinate")
        require(c['DATA_WORDS']<1<<FIELD_BITS and c['CODE_KEYS']*(1<<CELL_BITS)<1<<WORD_BITS,'Finite address/record width insufficient')
        return c


class Compiler:
    """Compositional elaboration of finite imperative syntax to ordinary code.

    Static nonrecursive functions use disjoint register intervals. CALL/RET use
    actual bounded W stack words; no Python function runs after compilation.
    """
    def __init__(self,design):
        self.design=design;self.constants=design.constants();self.nodes=[];self.labels={};self.fixups=[];self.registers={};self.next_register=3;self.line_spans={};self.calls={};self.counter=0
        self.tree=ast.parse(SOURCE.read_text(encoding='utf-8-sig'))
        self.functions={n.name:n for n in self.tree.body if isinstance(n,ast.FunctionDef)}
        self.formals={name:[self.reg(name,a.arg) for a in node.args.args] for name,node in self.functions.items()}
    def reg(self,scope,name):
        key=(scope,name)
        if key not in self.registers:self.registers[key]=self.next_register;self.next_register+=1
        return self.registers[key]
    def temp(self):
        r=self.next_register;self.next_register+=1;return r
    def fresh(self,prefix):
        self.counter+=1;return f'{prefix}.{self.counter}'
    def mark(self,name):
        require(name not in self.labels,'Duplicate label');self.labels[name]=len(self.nodes)
    def emit(self,op,a=0,b=0,c=0,imm=0):
        self.nodes.append([op,a,b,c,imm]);return len(self.nodes)-1
    def jump(self,op,label,a=0):self.fixups.append((self.emit(op,a),label))
    def literal(self,value):
        r=self.temp();self.emit(LI,r,imm=value);return r
    def expr(self,node,scope):
        if isinstance(node,ast.Constant):return self.literal(int(node.value))
        if isinstance(node,ast.Name):
            if node.id in self.constants:return self.literal(self.constants[node.id])
            return self.reg(scope,node.id)
        if isinstance(node,ast.Subscript):
            address=self.expr(node.slice,scope);r=self.temp()
            require(isinstance(node.value,ast.Name) and node.value.id in ('w','code'),'Only actual W/C arrays are accessible')
            self.emit(LOAD if node.value.id=='w' else LOADC,r,address);return r
        if isinstance(node,ast.BinOp):
            left=self.expr(node.left,scope);right=self.expr(node.right,scope);r=self.temp()
            op={ast.Add:ADD,ast.Sub:SUB,ast.Mult:MUL,ast.FloorDiv:DIV,ast.Mod:MOD,ast.LShift:SHL}.get(type(node.op))
            require(op is not None,'Unsupported binary expression');self.emit(op,r,left,right);return r
        if isinstance(node,ast.UnaryOp):
            value=self.expr(node.operand,scope);r=self.temp()
            if isinstance(node.op,ast.Not):self.emit(NOT,r,value)
            elif isinstance(node.op,ast.USub):zero=self.literal(0);self.emit(SUB,r,zero,value)
            else:raise RuntimeError('Unsupported unary operation')
            return r
        if isinstance(node,ast.Compare):
            require(len(node.ops)==1,'Chained comparison not in source subset')
            left=self.expr(node.left,scope);right=self.expr(node.comparators[0],scope);r=self.temp();op=node.ops[0]
            if isinstance(op,(ast.Gt,ast.GtE)):left,right=right,left
            self.emit(EQ if isinstance(op,(ast.Eq,ast.NotEq)) else LE if isinstance(op,(ast.LtE,ast.GtE)) else LT,r,left,right)
            if isinstance(op,ast.NotEq):self.emit(NOT,r,r)
            return r
        if isinstance(node,ast.BoolOp):
            # Short-circuiting is explicit ordinary control flow.
            r=self.temp();end=self.fresh('boolean_end');first=self.expr(node.values[0],scope);self.emit(MOV,r,first)
            for value in node.values[1:]:
                if isinstance(node.op,ast.And):self.jump(JZ,end,r)
                else:
                    neg=self.temp();self.emit(NOT,neg,r);self.jump(JZ,end,neg)
                other=self.expr(value,scope);self.emit(MOV,r,other)
            self.mark(end);return r
        if isinstance(node,ast.Call):
            require(isinstance(node.func,ast.Name),'Only named procedures/raw operations allowed')
            name=node.func.id;args=[self.expr(x,scope) for x in node.args];r=self.temp()
            if name in PRIM:
                require(len(args)==PRIM_ARITY[name],'Primitive arity mismatch')
                base=self.next_register;self.next_register+=len(args)
                for i,arg in enumerate(args):self.emit(MOV,base+i,arg)
                self.emit(IO,r,base,len(args),PRIM[name])
            else:
                require(name in self.functions and len(args)==len(self.formals[name]),'Unknown procedure/arity')
                self.calls.setdefault(scope,set()).add(name)
                for formal,arg in zip(self.formals[name],args):self.emit(MOV,formal,arg)
                self.jump(CALL,name);self.emit(MOV,r,2)
            return r
        raise RuntimeError('Unsupported source expression '+ast.dump(node))
    def assign(self,target,value,scope):
        if isinstance(target,ast.Name):self.emit(MOV,self.reg(scope,target.id),value)
        elif isinstance(target,ast.Subscript):
            require(isinstance(target.value,ast.Name) and target.value.id=='w','Nominal program may write only W')
            address=self.expr(target.slice,scope);self.emit(STORE,value,address)
        else:raise RuntimeError('Unsupported assignment')
    def statements(self,nodes,scope):
        for node in nodes:
            begin=len(self.nodes)
            if isinstance(node,ast.Assign):
                require(len(node.targets)==1,'Parallel assignment unsupported');self.assign(node.targets[0],self.expr(node.value,scope),scope)
            elif isinstance(node,ast.AugAssign):
                left=self.expr(node.target,scope);right=self.expr(node.value,scope);result=self.temp()
                self.emit(ADD if isinstance(node.op,ast.Add) else SUB,result,left,right);self.assign(node.target,result,scope)
            elif isinstance(node,ast.Expr):self.expr(node.value,scope)
            elif isinstance(node,ast.If):
                otherwise=self.fresh('else');end=self.fresh('endif');test=self.expr(node.test,scope);self.jump(JZ,otherwise,test)
                self.statements(node.body,scope);self.jump(JMP,end);self.mark(otherwise);self.statements(node.orelse,scope);self.mark(end)
            elif isinstance(node,ast.While):
                start=self.fresh('while');end=self.fresh('endwhile');self.mark(start);test=self.expr(node.test,scope);self.jump(JZ,end,test)
                self.statements(node.body,scope);self.jump(JMP,start);self.mark(end)
            elif isinstance(node,ast.Return):
                value=self.expr(node.value,scope) if node.value else self.literal(0);self.emit(MOV,2,value);self.emit(RET)
            elif isinstance(node,ast.Pass):pass
            else:raise RuntimeError('Unsupported source statement '+ast.dump(node))
            self.line_spans[f'{scope}:{node.lineno}']=[begin,len(self.nodes)]
    def compile(self):
        self.emit(LI,1,imm=0);self.jump(JMP,'main')
        for name,node in self.functions.items():
            self.mark(name);self.statements(node.body,name);self.emit(LI,2,imm=0);self.emit(RET)
        for index,label in self.fixups:self.nodes[index][4]=self.labels[label]
        def depth(name,path):
            require(name not in path,'Recursive call graph would require a new stack bound')
            return 1+max([depth(x,path+(name,)) for x in self.calls.get(name,())] or [0])
        self.stack_depth=depth('main',())
        require(self.stack_depth<self.constants['STACK_WORDS'],'Call depth exceeds W stack')
        require(self.next_register<1<<FIELD_BITS,'Register index encoding overflow')
        require(len(self.nodes)<=self.design.image_cells,'Complete program does not fit the chosen image')
        self.image=[encode(*node) for node in self.nodes]+[0]*(self.design.image_cells-len(self.nodes))
        return self


class Machine:
    def __init__(self,compiled,poison=123):
        self.compiled=compiled;self.C=compiled.image[:];self.R=[poison]*compiled.next_register;self.W=[poison]*compiled.constants['DATA_WORDS'];self.pc=0;self.halted=False;self.yielded=False
        self.powered=True;self.pending_instruction=None;self.retired=0;self.steps=0;self.word_work=0;self.io_counts=Counter();self.executed=Counter();self.faults=[];self.code_writes=0
    def reset_entry(self):
        self.pc=0;self.halted=False;self.yielded=False
    def launch(self,funded=True):
        if self.halted or not self.powered or self.pending_instruction is not None or not funded:return False
        if not 0<=self.pc<len(self.C):self.halted=True;return False
        cell=self.C[self.pc];op,a,b,c,imm=decode(cell)
        indices={a,b,c,1}
        if op==IO and 0<=imm<len(PRIMITIVES) and c==PRIM_ARITY[PRIMITIVES[imm]]:indices.update(range(b,min(b+c,len(self.R))))
        operands={i:self.R[i] for i in indices if 0<=i<len(self.R)}
        # This is one funded ordinary instruction's private operand latch. I is
        # sampled only at its actual I/O completion strobe, never bulk-copied here.
        self.pending_instruction=(self.pc,cell,operands)
        return True
    def complete(self,ports):
        if self.pending_instruction is None:return False
        latched=self.pending_instruction;self.pending_instruction=None
        return self._complete(ports,latched)
    def step(self,ports):
        return self.launch() and self.complete(ports)
    def _complete(self,ports,latched):
        address,cell,operands=latched;self.pc=address+1;self.retired=(self.retired+1)%(1<<64);self.steps+=1;self.word_work+=1
        if not 0<=cell<=CELL_MASK:return True
        op,a,b,c,imm=decode(cell);self.executed[op]+=1
        def get(i):return operands.get(i,self.R[i] if 0<=i<len(self.R) else 0)
        def put(i,value):
            if 0<=i<len(self.R):self.R[i]=value&WORD_MASK
        if op==LI:put(a,imm)
        elif op==MOV:put(a,get(b))
        elif op in (ADD,SUB,MUL,DIV,MOD,SHL,AND,OR,EQ,LT,LE):
            x,y=signed(get(b)),signed(get(c))
            value=(x+y if op==ADD else x-y if op==SUB else x*y if op==MUL else x//y if op==DIV and y else 0 if op==DIV else x%y if op==MOD and y else 0 if op==MOD else get(b)<<min(max(y,0),WORD_BITS) if op==SHL else int(bool(x) and bool(y)) if op==AND else int(bool(x) or bool(y)) if op==OR else int(x==y) if op==EQ else int(x<y) if op==LT else int(x<=y))
            put(a,value)
        elif op==NOT:put(a,int(not get(b)))
        elif op==LOAD:put(a,self.W[get(b)] if get(b)<len(self.W) else 0)
        elif op==STORE:
            if get(b)<len(self.W):self.W[get(b)]=get(a)
        elif op==LOADC:put(a,self.C[get(b)] if get(b)<len(self.C) else 0)
        elif op==STOREC:
            if get(b)<len(self.C):self.C[get(b)]=get(a)&CELL_MASK;self.code_writes+=1
        elif op==JMP:self.pc=imm
        elif op==JZ:
            if not get(a):self.pc=imm
        elif op==CALL:
            sp=get(1)
            if sp>=self.compiled.constants['STACK_WORDS']:self.halted=True
            else:self.W[sp]=self.pc;put(1,sp+1);self.pc=imm
        elif op==RET:
            sp=get(1)
            if not 0<sp<=self.compiled.constants['STACK_WORDS']:self.halted=True
            else:put(1,sp-1);self.pc=self.W[sp-1]
        elif op==IO and 0<=imm<len(PRIMITIVES):
            name=PRIMITIVES[imm]
            if c==PRIM_ARITY[name] and b+c<=len(self.R):
                args=tuple(signed(get(i)) for i in range(b,b+c));self.io_counts[name]+=1
                result=ports.perform(name,args,self);put(a,0 if result is None else result)
                self.word_work+=PRIM_WORD_COST[name]-1
                if name=='yield_frame':self.yielded=True
        elif op==HALT:self.halted=True
        ports.advance(self)
        return True
    def run(self,ports,budget=10000000,until_yield=True,hook=None):
        self.yielded=False;start=self.steps
        while self.steps-start<budget and not self.halted:
            if hook:hook(self,ports)
            if not self.step(ports):return 'halt' if self.halted else 'blocked'
            if until_yield and self.yielded:return 'yield'
        return 'halt' if self.halted else 'timeout'
    def enter(self,name,args=()):
        self.pc=self.compiled.labels[name];self.R[1]=1;self.W[0]=len(self.C);self.halted=False;self.yielded=False
        for reg,value in zip(self.compiled.formals[name],args):self.R[reg]=value&WORD_MASK
    def result(self):return signed(self.R[2])


class RawPorts:
    """Finite raw I/physical fixture for instruction tests, not a helper policy.

    Head reads inspect actual target cells/coordinates. I mutation is permitted
    independently of C/R/W. No intended-image or good-source test occurs here.
    Time/due lists are checker descriptions of bounded source registers.
    """
    def __init__(self,compiled):
        self.compiled=compiled;self.c=compiled.constants;self.now=0;self.events=[];self.fast={};self.replies={};self.requests={};self.I=[0]*8;self.valid=False;self.job=None;self.conversion_delay=1
        self.functional={};self.offer_pending=[];self.delivered=[];self.sample_attempts=0;self.own_override={};self.frames=0;self.world_latch=(0,0);self.fields={};self.target_cells={};self.publications=[];self.offers=0;self.samples=0;self.pending=[];self.slot_inputs={};self.write_enabled=True
        self.own_bays={t:compiled.design.own_bay for t in range(self.c["DEGREE"])};self.default_views={};self.raw_reads=0;self.input_events=[];self.dropped_offers=0;self.capacity=128
    def advance(self,machine):
        self.elapse(1)
    def elapse(self,ticks):
        require(ticks>=0,"Physical time cannot go backward")
        self.now+=ticks
        if self.job is not None and self.now>=self.job[0]:
            _,kind,key,value=self.job;self.I[1]=value&WORD_MASK;self.valid=True;self.job=None
        due=[x for x in self.pending if x[0]<=self.now];self.pending=[x for x in self.pending if x[0]>self.now]
        for _,kind,key,value in due:
            if kind=='fast':self.fast[key]=value
            else:self.replies[key]=value
        delivered=[x for x in self.offer_pending if x[0]<=self.now];self.offer_pending=[x for x in self.offer_pending if x[0]>self.now]
        self.delivered.extend(delivered)
    def set_view(self,target,view):
        self.default_views[target]=list(view)
        for k,value in enumerate(view):
            key=3+target*self.c['FAST_TARGET_KEYS']+k
            for origin in range(self.c['ORIGINS']):
                for bank in range(2):self.fast[(origin,bank,key)]=value
    def perform(self,name,args,machine):
        c=self.c
        if name=='fast_cmp':
            origin,bank,key,pivot=args;self.raw_reads+=1
            return int((self.fast.get((origin,bank,key),WORD_MASK)&WORD_MASK)<=pivot)
        if name=='fast_equal':
            origin,bank,key,expected=args;self.raw_reads+=1
            return int((self.fast.get((origin,bank,key),WORD_MASK)&WORD_MASK)==expected)
        if name=='fast_range':
            origin,bank,key,lower,upper=args;self.raw_reads+=1
            return int(lower<=(self.fast.get((origin,bank,key),WORD_MASK)&WORD_MASK)<=upper)
        if name=='request':
            origin,bank,target,key=args
            if 0<=origin<c['ORIGINS'] and bank in (0,1) and 0<=target<c['DEGREE']:
                self.requests[(origin,bank,target)]=key;self.events.append(('request',origin,bank,target,key))
            return 0
        if name=='reply_equal':
            origin,bank,target,expected=args;self.raw_reads+=1
            return int((self.replies.get((origin,bank,target),WORD_MASK)&WORD_MASK)==expected)
        if name=='source_capture_request':
            client,target=args;self.I[0]=(self.slot_inputs.get((client,target),WORD_MASK) if 0<=client<2*c['DEGREE'] and 0<=target<c['DEGREE'] else WORD_MASK)&WORD_MASK;return 0
        if name=='source_ieq':
            index,value=args;return int(0<=index<len(self.I) and self.I[index]==value)
        if name=='source_ilt':
            index,threshold=args;return int(0<=index<len(self.I) and self.I[index]<threshold)
        if name in ('source_idiv','source_imod','source_ishl','source_iadd_constant','source_iadd'):
            dst,src,operand=args
            if 0<=dst<len(self.I) and 0<=src<len(self.I):
                value=self.I[src]
                if name=='source_idiv':value=value//operand if operand>0 else 0
                elif name=='source_imod':value=value%operand if operand>0 else 0
                elif name=='source_ishl':value=value<<min(max(operand,0),WORD_BITS)
                elif name=='source_iadd_constant':value=value+operand
                elif 0<=operand<len(self.I):value=value+self.I[operand]
                self.I[dst]=value&WORD_MASK
            return 0
        if name=='source_iconstant':
            index,value=args
            if 0<=index<len(self.I):self.I[index]=value&WORD_MASK
            return 0
        if name=='source_icopy':
            dst,src=args
            if 0<=dst<len(self.I) and 0<=src<len(self.I):self.I[dst]=self.I[src]
            return 0
        if name=='source_ilt_register':
            left,right=args;return int(0<=left<len(self.I) and 0<=right<len(self.I) and self.I[left]<self.I[right])
        if name=='source_isub_constant':
            dst,value,src=args
            if 0<=dst<len(self.I) and 0<=src<len(self.I):self.I[dst]=(value-self.I[src])&WORD_MASK
            return 0
        if name=='source_start_functional':
            self.sample_attempts+=1
            if self.job is not None:self.events.append(('busy_conversion','functional'));return 0
            target,side,member,kind=args;count=c['CONNECTORS_A'] if side==0 else c['CONNECTORS_B']
            valid=0<=target<c['DEGREE'] and side in (0,1) and 0<=member<count and kind in (0,1)
            value=self.functional.get((target,side,member,kind),WORD_MASK) if valid else WORD_MASK
            self.job=(self.now+self.conversion_delay,'functional',(target,side,member,kind),value);self.valid=False;self.samples+=1;return 0
        if name=='source_start_cell':
            self.sample_attempts+=1
            if self.job is not None:self.events.append(('busy_conversion','cell'));return 0
            target=args[0];key=self.I[0];lookup=(target,self.I[2],self.I[3],self.I[4]);bound=0<=target<c['DEGREE'] and self.I[2] in (0,1) and self.I[3]<c['BAYS'] and self.I[4]<c['IMAGE_CELLS'];value=self.target_cells.get(lookup,WORD_MASK) if bound else WORD_MASK
            self.job=(self.now+self.conversion_delay,'cell',key,value);self.valid=False;self.samples+=1;return 0
        if name=='source_start_fast':
            self.sample_attempts+=1
            if self.job is not None:self.events.append(('busy_conversion','fast'));return 0
            key=args[0];singleton=0<=key<3 or (3<=key<c['FAST_KEYS'] and (key-3)%c['FAST_TARGET_KEYS']<c['VIEW_WORDS']);value=self.fast.get(('head',key),WORD_MASK) if singleton else WORD_MASK;self.I[0]=key&WORD_MASK
            self.job=(self.now+self.conversion_delay,'fast',key,value);self.valid=False;self.samples+=1;return 0
        if name=='source_ready':return int(self.valid and self.job is None)
        if name in ('source_offer_reply','source_offer_missing','source_offer_fast'):
            self.offers+=1
            lane=args[0]
            if not (0<=lane<2*c['DEGREE'] and 0<=args[1]<(c['FAST_KEYS'] if name=='source_offer_fast' else c['DEGREE'])):self.dropped_offers+=1;return 0
            if sum(item[2][0]==lane for item in self.offer_pending)>=self.capacity:self.dropped_offers+=1;return 0
            value=WORD_MASK if name=='source_offer_missing' else self.I[1] if name=='source_offer_fast' else self.I[5]
            self.offer_pending.append((self.now+2,name,args,value));self.publications.append((name,args,value));self.events.append((name,args,value));return 0
        if name=='source_invalidate':self.valid=False;self.I[5]=WORD_MASK;return 0
        if name=='send_command':
            target,record=args
            if 0<=target<c['DEGREE'] and 0<=record<1<<46:
                route=record&31;side=(record>>5)&1;cam=((record>>6)&63)-32;mode=((record>>12)&63)-32;action=(record>>18)&15;index=(record>>22)&((1<<18)-1);amplitude=((record>>40)&63)-32
                for key in list(self.fields):
                    if key[0]==target:del self.fields[key]
                self.fields[(target,c['CAM_PORT'],side,0)]=max(-22,min(22,cam))
                self.fields[(target,c['MODE_PORT'],side,0)]=max(-22,min(22,mode))
                if 2<=action<c['PORTS'] and index<c['BAYS']:self.fields[(target,action,side,index)]=max(-22,min(22,amplitude))
                self.events.append(('command',target,route,side,cam,mode,action,index,amplitude))
            return 0
        if name=='own_equal':
            target,side,address,expected=args;self.raw_reads+=1
            bay=self.own_bays.get(target,-1)
            return int((self.own_override.get((target,side,address),self.target_cells.get((target,side,bay,address),WORD_MASK))&WORD_MASK)==expected)
        if name=='write_own':
            target,side,address,value=args;bay=self.own_bays.get(target,-1)
            if self.write_enabled and 0<=bay<c['BAYS'] and side in (0,1) and 0<=address<c['IMAGE_CELLS']:
                self.target_cells[(target,side,bay,address)]=value&CELL_MASK
            self.events.append(('write_own',target,side,address,value&CELL_MASK));return 0
        if name=='world':
            self.world_latch=tuple(max(-100,min(100,x)) for x in args);self.events.append(('world',*self.world_latch));return 0
        if name=='cpu_count':return machine.retired if machine is not None else self.now%(1<<64)
        if name=='yield_frame':self.frames+=1;return 0
        raise RuntimeError('Unknown elementary operation')


def digest(path):return hashlib.sha256(path.read_bytes().replace(b'\r\n',b'\n')).hexdigest()


def definite_assignment(compiled):
    """Check the live-register premise used by the structural compiler proof."""
    names=set(compiled.constants)
    def expression(node,assigned):
        if isinstance(node,ast.Name):require(node.id in assigned or node.id in names,'Read before nominal assignment: '+node.id)
        elif isinstance(node,ast.Subscript):expression(node.slice,assigned)
        elif isinstance(node,ast.Call):
            for arg in node.args:expression(arg,assigned)
        else:
            for child in ast.iter_child_nodes(node):
                if isinstance(child,ast.expr):expression(child,assigned)
    def block(nodes,assigned):
        assigned=set(assigned)
        for node in nodes:
            if isinstance(node,ast.Assign):
                expression(node.value,assigned)
                for target in node.targets:
                    if isinstance(target,ast.Name):assigned.add(target.id)
                    else:expression(target.slice,assigned)
            elif isinstance(node,ast.AugAssign):
                expression(node.target,assigned);expression(node.value,assigned)
            elif isinstance(node,ast.Expr):expression(node.value,assigned)
            elif isinstance(node,ast.Return):
                if node.value:expression(node.value,assigned)
                return None
            elif isinstance(node,ast.If):
                expression(node.test,assigned);left=block(node.body,assigned);right=block(node.orelse,assigned)
                if left is None and right is None:return None
                assigned=right if left is None else left if right is None else left&right
            elif isinstance(node,ast.While):
                expression(node.test,assigned);block(node.body,assigned)
            elif not isinstance(node,ast.Pass):raise RuntimeError('Unknown formation statement')
        return assigned
    for name,node in compiled.functions.items():block(node.body,{x.arg for x in node.args.args})
    return {'procedures':len(compiled.functions),'every_nominal_local_read_assigned':True}

def compile_check(design):
    compiled=Compiler(design).compile()
    definite_assignment(compiled)
    # Decoder/encoder equality includes signed immediate and every real cell.
    require(all(encode(*decode(cell))==cell for cell in compiled.image),'Encoding is not injective on intended instructions')
    require(not any(node[0]==STOREC for node in compiled.nodes),'Nominal program writes its own C')
    return compiled


def basic_checks():
    design=Design();compiled=compile_check(design);ports=RawPorts(compiled);machine=Machine(compiled)
    require(machine.run(ports)=='yield','Full stored entry/frame did not yield')
    require(machine.W[compiled.constants['ENTRY']]==design.entry_frames-1,'Bootstrap/entry countdown mismatch')
    require(ports.world_latch==(60,60),'Applied bootstrap fallback missing')
    require(machine.C==compiled.image,'Nominal stored image changed')
    first=dict(instructions=machine.steps,word_work=machine.word_work,io=dict(machine.io_counts),raw_reads=ports.raw_reads)
    # Inputs mutate independently; the machine never reads the checker mutation log.
    state=(machine.C[:],machine.R[:],machine.W[:],machine.pc)
    ports.fast[(0,0,0)]=123456;ports.input_events.append(('replace-primary',))
    require(state==(machine.C,machine.R,machine.W,machine.pc),'Input-only mutation changed private/code state')
    # Exact large-alphabet encoded-word comparisons retain key and one origin vote.
    for value in (0,1,1000,2000):
        port=RawPorts(compiled)
        for o in range(design.origins):
            for bank in range(2):port.fast[(o,bank,7)]=value
        m=Machine(compiled);m.enter('estimate',(7,2000));m.run(port,until_yield=False)
        require(m.result()==value,'Executed binary search differs from equal nominal words')
    return compiled,first



class SignedMemory(list):
    def __getitem__(self,index):
        value=super().__getitem__(index)
        return [signed(x) for x in value] if isinstance(index,slice) else signed(value)
    def __setitem__(self,index,value):
        super().__setitem__(index,[x&WORD_MASK for x in value] if isinstance(index,slice) else value&WORD_MASK)


def reference_call(compiled,name,args,initial_w,code,ports):
    """Checker-only direct IMP interpretation, never used by Machine.step."""
    memory=SignedMemory(initial_w)
    env=dict(compiled.constants,w=memory,code=code)
    def primitive(pname):
        def call(*values):
            result=ports.perform(pname,tuple(values),None);ports.advance(None)
            return 0 if result is None else result
        return call
    env.update({pname:primitive(pname) for pname in PRIMITIVES})
    exec(compile(SOURCE.read_text(encoding='utf-8-sig'),str(SOURCE),'exec'),env)
    result=env[name](*args)
    return result,list(memory)


def populated_view(compiled,half=0,phase=0,mode=0):
    c=compiled.constants;v=[0]*c['VIEW_WORDS'];v[c['CAM']]=(half*c['PHASES']+phase)*c['SEGMENT']+c['GUARD'];v[c['ANCHOR']]=half;v[c['MODE']]=0;v[c['NORMAL_STOP']]=int(mode==0);v[c['ABORT_FULL']]=int(mode>0);v[c['BLEND']]=half*c['BLEND_LIMIT']
    for side in range(2):
        v[c['CUT_A']+side]=0 if side==half else c['CUT_LIMIT']
        v[c['CLAMP_A']+side]=0;v[c['RESET_A']+side]=0;v[c['ISO_DEF_A']+side]=0;v[c['SHUNT_DEF_A']+side]=0;v[c['ENERGY_A']+side]=c['RESERVE_CAP'] if side==half else 0
        for j in range(c['BAYS']):
            v[c['ACT_A']+side*c['BAYS']+j]=c['WARM_AT'] if side==half and j==0 else 0
            v[c['SEAT_A']+side*c['BAYS']+j]=30
            v[c['ACT_ZERO_A']+side*c['BAYS']+j]=int(v[c['ACT_A']+side*c['BAYS']+j]==0)
            v[c['ACT_POWER_A']+side*c['BAYS']+j]=int(v[c['ACT_A']+side*c['BAYS']+j]>=c['POWER_AT'])
        v[c['CUT_OPEN_A']+side]=int(v[c['CUT_A']+side]==c['CUT_LIMIT'])
        v[c['CLAMP_OPEN_A']+side]=1;v[c['RESET_OPEN_A']+side]=1;v[c['POWER_OFF_A']+side]=int(side!=half)
        v[c['ISO_SEATED_A']+side]=1;v[c['SHUNT_SEATED_A']+side]=1;v[c['SHUNT_OPEN_A']+side]=0
        v[c['BLEND_AT_A']+side]=int(side==half);v[c['CAM_ENTRY_A']+side]=0
    v[c['ANCHOR_IS_A']]=int(half==0);v[c['ANCHOR_IS_B']]=int(half==1)
    return v


def formation(compiled):
    m=Machine(compiled);p=RawPorts(compiled)
    require(m.run(p)=='yield','Entry did not form private state')
    c=compiled.constants
    for t in range(c['DEGREE']):
        b=c['TARGET_BASE']+t*c['TARGET_WORDS']
        require(m.W[b+c['SCAN_MATCH']]==1 and m.W[b+c['SELECTED']]==0 and m.W[b+c['SCAN_BAY']]==0 and m.W[b+c['SCAN_ADDRESS']]==0,'Fresh helper does not form common-first-bay state')
        require(m.W[b+c['ABORT']]==0 and m.W[b+c['WATCH_HALF']]==0,'Fresh watchdog state is not invalid/clear')
    return m


def refinement_checks(compiled):
    from copy import deepcopy
    c=compiled.constants;cases=0;maximum=0;per_function={};commands=0
    formed=formation(compiled)
    for half in (0,1):
        for phase in range(c['PHASES']):
            for mode in (0,1):
                p=RawPorts(compiled);view=populated_view(compiled,half,phase,mode);p.set_view(0,view)
                # Exercise physical own-lead data and genuinely malformed requests.
                p.target_cells[(0,1-half,compiled.design.own_bay,0)]=compiled.image[0]
                q=deepcopy(p);m=Machine(compiled);m.W=formed.W[:];m.enter('helper',(0,));before=m.steps
                expected,expected_w=reference_call(compiled,'helper',(0,),m.W[:],m.C[:],q)
                verdict=m.run(p,until_yield=False)
                require(verdict=='halt' and m.result()==(expected or 0),'Instruction function return differs')
                require(m.W[c['STACK_WORDS']:]==expected_w[c['STACK_WORDS']:],'Actual helper W differs from IMP interpretation')
                require(p.events==q.events,'Actual helper actions differ from IMP interpretation')
                require(m.C==compiled.image,'Helper changed nominal C')
                elapsed=m.steps-before;maximum=max(maximum,elapsed);cases+=1;commands+=sum(e[0]=='command' for e in p.events)
    for name in ('publish_plant','publish_fast','publish_queries','frame'):
        p=RawPorts(compiled)
        for k in range(c['FAST_KEYS']):p.fast[('head',k)]=600
        for client in range(2*c['DEGREE']):
            for target in range(c['DEGREE']):
                p.slot_inputs[(client,target)]=((client+target)%(2*c['BAYS']))*c['IMAGE_CELLS']+3
                key=p.slot_inputs[(client,target)];p.target_cells[(target,key//(c['BAYS']*c['IMAGE_CELLS']),(key//c['IMAGE_CELLS'])%c['BAYS'],3)]=compiled.image[3]
        q=deepcopy(p);m=Machine(compiled);m.W=formed.W[:];m.enter(name);expected,expected_w=reference_call(compiled,name,(),m.W[:],m.C[:],q)
        m.run(p,until_yield=name=='frame')
        require(m.W[c['STACK_WORDS']:]==expected_w[c['STACK_WORDS']:],'Provider/frame W differs from IMP')
        require(p.events==q.events,'Provider/frame effects differ from IMP')
        require(p.I==q.I,'Provider raw I arithmetic differs')
        per_function[name]={'instructions':m.steps,'word_work':m.word_work,'offers':p.offers,'samples':p.samples,'io':dict(m.io_counts)}
    return {'helper_cases':cases,'actual_command_records':commands,'maximum_helper_instructions':maximum,'provider_and_frame':per_function}


def changing_input_checks(compiled):
    c=compiled.constants;outcomes=[]
    for start in range(c['ORIGINS']):
        p=RawPorts(compiled);m=Machine(compiled);m.enter('estimate',(7,2000))
        def perturb(machine,ports):
            if 0<=machine.pc<len(machine.C):
                op,a,b,n,prim=decode(machine.C[machine.pc])
                if op==IO and 0<=prim<len(PRIMITIVES) and PRIMITIVES[prim]=='fast_cmp':
                    origin,bank,key,pivot=[signed(machine.R[x]) for x in range(b,b+n)]
                    value=0 if origin==start and ports.raw_reads%2 else WORD_MASK if origin==start else 980 if ports.raw_reads%2 else 1020
                    before=(machine.R[:],machine.W[:],machine.pc,machine.C[:]);ports.fast[(origin,bank,key)]=value
                    require(before==(machine.R,machine.W,machine.pc,machine.C),'Input mutation changed execution')
        m.run(p,until_yield=False,hook=perturb)
        require(980<=m.result()<=1020,'Changing-slot envelope failed in full program')
        outcomes.append(m.result())
    return {'rotating_affected_origins':len(outcomes),'results':outcomes,'scope':'one affected origin per complete small-instance job; not a renewal theorem'}


def adversarial_checks(compiled):
    c=compiled.constants
    # No C==P dispatcher exists: an actually stored bad program emits first,
    # then loops. Timeout/release do not undo its accepted prefix or overwrite C.
    m=Machine(compiled);p=RawPorts(compiled)
    m.C[:5]=[encode(LI,3,immediate=-100),encode(MOV,4,3),encode(IO,5,3,2,PRIM['world']),encode(JMP,immediate=0),encode(HALT)]
    require(m.run(p,budget=30)=='timeout' and p.world_latch==(-100,-100),'Bad-code accepted prefix missing')
    image=m.C[:];before_emissions=len(p.events);m.run(p,budget=30)
    require(len(p.events)>before_emissions,'Released bad code stopped issuing effects')
    require(m.C==image and p.world_latch==(-100,-100),'Release silently repaired code/effects')
    # Self-modification is an ordinary bad instruction, outside nominal C invariance.
    z=Machine(compiled);zp=RawPorts(compiled);z.C[:5]=[encode(LI,3,immediate=0),encode(LI,4,immediate=100),encode(STOREC,3,4),encode(HALT),0]
    z.run(zp,until_yield=False)
    require(z.C[100]==0 and z.code_writes==1,'Actual bad code cannot change future image')
    # Own-image copying observes altered actual padding, not the compiler's image.
    source=formation(compiled);source.C[-1]=17;source.W[c['TARGET_BASE']+c['CURSOR']]=c['IMAGE_CELLS']-1
    view=populated_view(compiled,0,6);p=RawPorts(compiled);p.set_view(0,view);source.enter('helper',(0,));source.run(p,until_yield=False)
    require(('write_own',0,1,c['IMAGE_CELLS']-1,17) in p.events,'Copy read a canonical template instead of actual C')
    # Source's two receiver-bank slots are distinct and visited by the real loop.
    x=formation(compiled);xp=RawPorts(compiled);xp.slot_inputs[(0,0)]=3;xp.slot_inputs[(c['DEGREE'],0)]=4
    xp.target_cells[(0,0,0,3)]=111;xp.target_cells[(0,0,0,4)]=222
    seen=[]
    total=2*c['DEGREE']*c['DEGREE']
    for _ in range(math.ceil(total/c['QUERY_BATCH'])):
        x.enter('publish_queries');x.run(xp,until_yield=False)
    for event in xp.publications:
        if event[0]=='source_offer_reply':seen.append((event[1],event[2]))
    require(((0,0),(3<<CELL_BITS)+111) in seen and ((c['DEGREE'],0),(4<<CELL_BITS)+222) in seen,'Consumer-bank requests alias')
    # A matching value under a wrong key must fail the whole-word comparison.
    a=formation(compiled);ap=RawPorts(compiled);base=c['TARGET_BASE'];desired=7;a.W[base+c['CELL_KEY']]=desired;a.W[base+c['PENDING']]=1;a.W[base+c['CELL_WAIT']]=0
    for origin in range(c['ORIGINS']):
        for bank in range(2):ap.replies[(origin,bank,0)]=((desired+1)<<CELL_BITS)+a.C[7]
    a.enter('cell_result',(0,0,0,7));a.run(ap,until_yield=False)
    require(a.result()==1,'Wrong-key frame passed encoded comparison')
    # Fresh helpers are ready to accept bay zero. The rejected zero-only formation
    # is retained as a specific semantic obstruction, not silently normalized.
    fresh=formation(compiled);fresh.W[base+c['SCAN_MATCH']]=0
    require(fresh.W[base+c['SCAN_MATCH']]!=1,'Zero-only formation countercase absent')
    # An unsuccessful private write cannot advance the actual copy cursor.
    blocked=formation(compiled);bp=RawPorts(compiled);bp.write_enabled=False;bp.set_view(0,populated_view(compiled,0,6));blocked.enter('helper',(0,));blocked.run(bp,until_yield=False)
    require(blocked.W[base+c['CURSOR']]==0 and any(e[0]=='write_own' for e in bp.events),'Failed write became successful copy progress')
    # A forged own-read word is an input fault, not detected by a hidden label.
    forged=formation(compiled);fp=RawPorts(compiled);fp.set_view(0,populated_view(compiled,0,6));fp.own_override[(0,1,0)]=forged.C[0];forged.enter('helper',(0,));forged.run(fp,until_yield=False)
    require(forged.W[base+c['CURSOR']]==1 and not fp.target_cells,'Forged read obstruction was hidden')
    # Busy raw conversion and queued publications survive reset/invalidations.
    retained=RawPorts(compiled);retained.conversion_delay=100;retained.perform('source_start_fast',(0,),None);job=retained.job
    retained.perform('source_invalidate',(),None);retained.perform('source_start_fast',(1,),None)
    require(retained.job==job and retained.sample_attempts==2,'Another request erased a launched conversion')
    retained.I[5]=123;retained.perform('source_offer_reply',(0,0),None);queued=retained.offer_pending[:]
    require(queued,'Ordinary publication did not create a queued record')
    retained.perform('source_invalidate',(),None);require(retained.offer_pending==queued,'Cache invalidation erased a queued reply')
    retained.offer_pending=[(retained.now+100,'source_offer_reply',(0,0),j) for j in range(retained.capacity)]
    old_offers=retained.offers;retained.perform('source_offer_reply',(0,0),None)
    require(retained.offers==old_offers+1 and retained.dropped_offers==1,'Rejected offer was not charged')
    require('write_cell' not in PRIM,'Foreign-bay write remains in installed ISA')
    ownership=Machine(compiled);op=RawPorts(compiled);owner=op.own_bays[0];foreign=(owner+1)%c['BAYS'];op.target_cells[(0,1,foreign,0)]=55
    ownership.C[:6]=[encode(LI,3,immediate=0),encode(LI,4,immediate=1),encode(LI,5,immediate=0),encode(LI,6,immediate=77),encode(IO,7,3,4,PRIM['write_own']),encode(HALT)]
    ownership.run(op,until_yield=False)
    require(op.target_cells[(0,1,owner,0)]==77 and op.target_cells[(0,1,foreign,0)]==55,'Compromised code crossed its physical private writer lead')
    return {'bad_code_prefix_retained_after_timeout_and_release':True,'actual_self_write':True,'copy_reads_actual_C':True,'distinct_consumer_bank_requests':True,'wrong_key_rejected':True,'zero_only_scan_formation_rejected':True,'all_source_slots_visited':total,'failed_copy_write_does_not_advance':True,'forged_own_read_remains_input_fault_obstruction':True,'launched_conversion_and_queue_survive_invalidation':True,'rejected_raw_offer_charged':True,'arbitrary_code_writer_is_owner_bound':True,'no_foreign_bay_write_opcode':True}



def functional_and_unknown_checks(compiled):
    c=compiled.constants;base=c['TARGET_BASE'];view=populated_view(compiled,0,0)
    outcomes=[]
    for load in (200,1200):
        m=formation(compiled);p=RawPorts(compiled);p.set_view(0,view)
        for origin in range(c['ORIGINS']):
            for bank in range(2):
                for side in (0,1):
                    p.fast[(origin,bank,3+c['VIEW_WORDS']+side)]=load
                    p.fast[(origin,bank,3+c['VIEW_WORDS']+2+side)]=0
        p.fields[(0,c['CUT_PORT'],0,0)]=20;p.fields[(0,c['CUT_PORT'],1,0)]=20
        m.enter('helper',(0,));m.run(p,until_yield=False)
        cut=p.fields.get((0,c['CUT_PORT'],1,0),0)
        require(cut==(20 if load==200 else 0),'Functional guard accepted failed attenuation or refused working case')
        require(p.fields.get((0,c['CUT_PORT'],0,0),0)==0,'Inactive side retained a cut field')
        outcomes.append({'actual_max_load':load,'pose_shunt_deficit':view[c['SHUNT_DEF_A']+1],'cut_command':cut})
    # Range-validated estimates do not treat missing nominal words as high truth.
    m=Machine(compiled);p=RawPorts(compiled);p.fast[(0,0,7)]=2000
    for bank in range(2):p.fast[(1,bank,7)]=1
    m.enter('estimate',(7,2000));m.run(p,until_yield=False)
    require(m.W[c['EST_VALID']]==0,'Missing words were silently a valid geometric point')
    m=Machine(compiled);p=RawPorts(compiled);p.fast[(0,0,3+c['CUT_OPEN_A'])]=1
    m.enter('contact',(0,c['CUT_OPEN_A']));m.run(p,until_yield=False)
    require(m.result()==0,'Unavailable contact became a positive stop witness')
    # Over-margin threshold arithmetic must reject before subtraction/comparison.
    reject=compile_check(Design(physical_parameters=(('LOAD_MARGIN',1001),)))
    m=Machine(reject);p=RawPorts(reject);m.enter('permission',(reject.constants['TARGET_BASE'],0));m.run(p,until_yield=False)
    require(m.result()==0 and not m.io_counts['fast_cmp'],'Unsigned threshold underflow was not rejected')
    # Execute an actual aggregate fold, with query work interleaved between members.
    d=Design(fast_batch=1,query_batch=1);folded=compile_check(d);fc=folded.constants;f=formation(folded);fp=RawPorts(folded)
    f.W[fc['FAST_CURSOR']]=fc['VIEW_WORDS']
    for pindex,value in enumerate((1200,200)):fp.functional[(0,0,pindex,0)]=fc["SENSE_BIAS"]+value
    f.enter('publish_fast');f.run(fp,until_yield=False)
    require(fp.I[6]==1200,'First member did not enter the actual I accumulator')
    fp.slot_inputs[(0,0)]=0;fp.target_cells[(0,0,0,0)]=77
    f.enter('publish_queries');f.run(fp,until_yield=False)
    require(fp.I[6]==1200,'Query reused the partial raw aggregate register')
    f.enter('publish_fast');f.run(fp,until_yield=False)
    key=3+fc['VIEW_WORDS'];values=[event[2] for event in fp.publications if event[0]=='source_offer_fast' and event[1][1]==key]
    require(values and all(value==1200 for value in values),'Executed max fold differs from individual connector readings')
    # A missing member poisons availability, not an assumed zero load.
    missing=formation(folded);mp=RawPorts(folded);missing.W[fc['FAST_CURSOR']]=fc['VIEW_WORDS'];mp.functional[(0,0,0,0)]=fc["SENSE_BIAS"]+100
    for _ in range(2):missing.enter('publish_fast');missing.run(mp,until_yield=False)
    values=[event[2] for event in mp.publications if event[0]=='source_offer_fast' and event[1][1]==key]
    require(values and all(value==WORD_MASK for value in values),'Missing connector was dropped from the maximum')
    # Cam intervals touching a band boundary produce no substantive stroke.
    ambiguous=compile_check(Design(physical_parameters=(('CAM_ERROR',2),('SEGMENT',40),('GUARD',20))))
    ac=ambiguous.constants;a=formation(ambiguous);ap=RawPorts(ambiguous);av=populated_view(ambiguous,0,0);av[ac['CAM']]=39;ap.set_view(0,av)
    a.enter('helper',(0,));a.run(ap,until_yield=False)
    require(not any(key[1] not in (ac['CAM_PORT'],ac['MODE_PORT']) and value for key,value in ap.fields.items()),'Ambiguous band selected a substantive force')
    # A constant actual maximum does not imply slowly varying individual heads.
    staggered=(200,200);actual_max=(1200,1200)
    require(max(staggered)==200 and max(actual_max)==1200,'Staggered-sample boundary missing')
    return {'working_and_failed_attenuation':outcomes,'missing_pose_is_unknown':True,'unavailable_contact_not_a_stop':True,'oversized_margin_rejected_before_read':True,'actual_I_max_fold':1200,'query_does_not_overwrite_fold':True,'missing_member_publishes_unavailable':True,'ambiguous_cam_abstains':True,'staggered_fold_boundary':{'sampled_members':list(staggered),'actual_max_at_both_samples':list(actual_max),'consequence':'per-connector rates and oldest-member age are required; aggregate-rate0 is insufficient'}}

class WorkBound:
    """Syntax-directed upper instruction count with explicit loop certificates."""
    def __init__(self,compiled):self.p=compiled;self.c=compiled.constants;self.cache={};self.loops=[]
    def limit(self,fn,node):
        text=ast.unparse(node.test);c=self.c
        if fn=='main':raise RuntimeError('The indefinite service loop has no finite total bound')
        if fn=='boot' and 'cpu_count' in text:n=c['BOOT_DRAIN_STEPS'];variant='remaining local retirement distance before publication'
        elif fn=='boot' and text.startswith('a <'):n=c['DATA_WORDS']-c['STACK_WORDS'];variant='DATA_WORDS-a'
        elif fn=='boot':n=c['DEGREE'];variant='DEGREE-t'
        elif fn in ('count_fast','count_range','cell_result','contact'):n=c['ORIGINS'];variant='ORIGINS-origin'
        elif fn=='estimate':n=c['POSE_MAX'].bit_length();variant='hi-lo halves after each counted pass'
        elif fn=='publish_fast' and text.startswith('visit <'):n=c['FAST_BATCH'];variant='FAST_BATCH-visit'
        elif fn=='publish_queries' and text.startswith('visit <'):n=c['QUERY_BATCH'];variant='QUERY_BATCH-visit'
        elif text.startswith('polls <'):n=c['CONVERSION_POLLS'];variant='CONVERSION_POLLS-polls'
        elif fn=='publish_fast':n=2*c['DEGREE'];variant='2*DEGREE-client'
        elif fn=='publish_value':n=2*c['DEGREE'];variant='2*DEGREE-client'
        elif fn=='publish_plant':n=3;variant='3-key'
        elif fn=='read_view':n=c['POSE_WORDS'];variant='POSE_WORDS-k'
        elif fn in ('clear_target','progress','first_activation'):n=c['BAYS'];variant='BAYS-j'
        elif fn=='helper' and text.startswith('p <='):n=7;variant='CMD_AMPLITUDE-p+1'
        elif fn=='helper':n=c['BAYS'];variant='BAYS-j'
        elif fn=='frame' and text.startswith('visits <'):n=c['MAINT_BATCH'];variant='MAINT_BATCH-visits'
        elif fn=='frame' and text.startswith('target <'):n=c['DEGREE'];variant='DEGREE-target'
        elif fn=='frame':n=c['FRAME_STEPS'];variant='remaining local retired-instruction distance; at least one instruction per read; modulo2^64 window bound'
        else:raise RuntimeError('Uncertified source loop '+fn+': '+text)
        self.loops.append({'function':fn,'line':node.lineno,'condition':text,'iterations':n,'variant':variant});return n
    def expr(self,node):
        if isinstance(node,ast.Constant):return 1
        if isinstance(node,ast.Name):return int(node.id in self.c)
        if isinstance(node,ast.Subscript):return self.expr(node.slice)+1
        if isinstance(node,ast.BinOp):return self.expr(node.left)+self.expr(node.right)+1
        if isinstance(node,ast.UnaryOp):return self.expr(node.operand)+(2 if isinstance(node.op,ast.USub) else 1)
        if isinstance(node,ast.Compare):return self.expr(node.left)+self.expr(node.comparators[0])+1+int(isinstance(node.ops[0],ast.NotEq))
        if isinstance(node,ast.BoolOp):return sum(self.expr(x) for x in node.values)+len(node.values)+(len(node.values)-1)*(1 if isinstance(node.op,ast.And) else 2)
        if isinstance(node,ast.Call):
            name=node.func.id;base=sum(self.expr(x) for x in node.args)+len(node.args)
            return base+1 if name in PRIM else base+2+self.function(name)
        raise RuntimeError('Unbounded expression')
    def target(self,node):return 1 if isinstance(node,ast.Name) else self.expr(node.slice)+1
    def statement(self,node,fn):
        if isinstance(node,ast.Assign):return self.expr(node.value)+self.target(node.targets[0])
        if isinstance(node,ast.AugAssign):return self.expr(node.target)+self.expr(node.value)+1+self.target(node.target)
        if isinstance(node,ast.Expr):return self.expr(node.value)
        if isinstance(node,ast.Return):return (self.expr(node.value) if node.value else 1)+2
        if isinstance(node,ast.If):return self.expr(node.test)+2+max(self.block(node.body,fn),self.block(node.orelse,fn))
        if isinstance(node,ast.While):
            n=self.limit(fn,node);return (n+1)*(self.expr(node.test)+1)+n*(self.block(node.body,fn)+1)
        if isinstance(node,ast.Pass):return 0
        raise RuntimeError('Unbounded statement')
    def block(self,body,fn):return sum(self.statement(node,fn) for node in body)
    def function(self,name):
        if name not in self.cache:self.cache[name]=self.block(self.p.functions[name].body,name)+2
        return self.cache[name]
    def report(self):
        for name in self.p.functions:
            if name!='main':self.function(name)
        active=sum(self.statement(node,'frame') for node in self.p.functions['frame'].body if not (isinstance(node,ast.While) and 'cpu_count' in ast.unparse(node.test)))+2
        sharp=max(active,self.c['FRAME_STEPS'])+64
        boot_active=sum(self.statement(node,'boot') for node in self.p.functions['boot'].body if not (isinstance(node,ast.While) and 'cpu_count' in ast.unparse(node.test)))+2
        boot_sharp=boot_active+self.c['BOOT_DRAIN_STEPS']+64
        return {'instruction_upper_bounds':dict(sorted(self.cache.items())),'boot_active_upper':boot_active,'boot_padded_upper':boot_sharp,'active_frame_upper':active,'padded_frame_upper':sharp,'padded_frame_lower':self.c['FRAME_STEPS'],'padding_scope':'actual per-bank64-bit retired counter, offset arbitrary; fewer than2^64 instructions per frame; a final counter polling iteration and caller boundary cost at most64','loop_certificates':self.loops,'loop_proof_scope':'formation plus ordinary arithmetic; estimate uses the counted-threshold envelope width argument','code_cells':len(self.p.nodes),'padded_image_bytes':self.p.design.image_cells*(CELL_BITS//8),'private_array_bits':WORD_BITS*(self.p.next_register+self.c['DATA_WORDS']),'private_bits':WORD_BITS*(self.p.next_register+self.c['DATA_WORDS']+32),'private_words_with_metadata':self.p.next_register+self.c['DATA_WORDS']+32,'source_I_scratch_words':8,'stack_depth':self.p.stack_depth,'cell_bits':CELL_BITS,'private_and_reply_bits':WORD_BITS,'maximum_reply_bits':CELL_BITS+(self.c['CODE_KEYS']-1).bit_length(),'source_slots':2*self.c['DEGREE']**2,'fast_fanout':2*self.c['DEGREE'],'provider_offers_per_frame':2*self.c['DEGREE']*(3+self.c['FAST_BATCH'])+self.c['QUERY_BATCH'],'raw_maintenance_heads':self.c['RAW_MAINT_HEADS'],'published_fast_keys':self.c['FAST_KEYS'],'connector_counts':[self.c['CONNECTORS_A'],self.c['CONNECTORS_B']]}





def abort_protocol_checks():
    d=Design(fast_batch=1,post_stage_frames=2);c=compile_check(d);k=c.constants;base=k['TARGET_BASE'];decoded=[]
    # Decode ONE captured mode word, not two independently sampled contacts.
    for raw,expected in ((0,0),(1,WORD_MASK),(2,1),(3,0),(7,WORD_MASK)):
        m=formation(c);p=RawPorts(c);m.W[k['FAST_CURSOR']]=k['MODE'];key=3+k['MODE'];p.fast[('head',key)]=raw
        m.enter('publish_fast');m.run(p,until_yield=False)
        values=[x[2] for x in p.publications if x[0]=='source_offer_fast' and x[1][1]==key]
        require(values and all(v==expected for v in values),'Raw mode-word decoder violates entry/full/reset ordering')
        decoded.append([raw,expected])
    # Actual stored code sets EXITING from verified ready/entry, then ignores
    # every lower-priority stale state while retaining a reverse field.
    m=formation(c);p=RawPorts(c);v=populated_view(c,0,0,1);v[k['CAM']]=0;v[k['CAM_ENTRY_A']]=1;p.set_view(0,v)
    m.W[base+k['STAGE_ID']]=27;m.W[base+k['STAGE_WAIT']]=0
    m.enter('helper',(0,));m.run(p,until_yield=False)
    require(m.W[base+k['EXITING_ABORT']]==1,'Verified abort completion did not form exit state')
    v[k['CAM_ENTRY_A']]=0;v[k['CUT_OPEN_A']+1]=0;v[k['MODE']]=1;v[k['ABORT_FULL']]=1;v[k['NORMAL_STOP']]=0;p.set_view(0,v)
    m.enter('helper',(0,));m.run(p,until_yield=False)
    require(p.fields.get((0,k['MODE_PORT'],0,0))==-20 and not any(key[1]==k['CAM_PORT'] and value for key,value in p.fields.items()),'Stale predicates overrode the continuous exit field')
    v[k['NORMAL_STOP']]=1;p.set_view(0,v);m.enter('helper',(0,));m.run(p,until_yield=False)
    require(m.W[base+k['EXITING_ABORT']]==1 and m.W[base+k['EXIT_WAIT']]==2,'A single normal-stop sample erased exit state')
    # Execute the actual frame countdowns; the predicate must be checked again.
    for _ in range(2):m.enter('frame');m.run(p)
    v[k['NORMAL_STOP']]=0;p.set_view(0,v);m.enter('helper',(0,));m.run(p,until_yield=False)
    require(m.W[base+k['EXITING_ABORT']]==1,'An expired wait without a fresh normal contact cleared exit')
    v[k['NORMAL_STOP']]=1;p.set_view(0,v);m.enter('helper',(0,));m.run(p,until_yield=False)
    for _ in range(2):m.enter('frame');m.run(p)
    m.enter('helper',(0,));m.run(p,until_yield=False)
    require(m.W[base+k['EXITING_ABORT']]==0 and m.W[base+k['ABORT']]==0,'Fresh post-wait normal-stop evidence did not release exit')
    return {'single_captured_mode_word_cases':decoded,'exit_latch_set_by_code':True,'exit_priority_over_stale_full_entering_ready':True,'reverse_field_persists_during_wait':True,'fresh_normal_after_wait_required':True,'scope':'The physical one-way entry, retained FULL, ordered11→01→00 return, normal catch retention and residence bounds remain the source adapter.'}

def io_inventory(compiled):
    """Nominal whole-frame attempts, separate from raw hostile line traffic."""
    c=compiled.constants;d=c['DEGREE'];m=c['MAINT_BATCH'];n=c['ORIGINS']
    require(m<=d,'Per-branch one-visit bound needs MAINT_BATCH<=DEGREE')
    return {
      'publisher_and_reply_offers':2*d*(3+c['FAST_BATCH'])+c['QUERY_BATCH'],
      'helper_request_latch_updates':m*(2*n),
      'helper_command_records':m,'helper_own_write_attempts':m,'helper_own_read_attempts':m,'world_vector_records':1,
      'raw_conversion_attempts':3+c['FAST_BATCH']+c['QUERY_BATCH'],
      'per_directed_bank_pair_if_applicable':{'publication_reply_records':3+c['FAST_BATCH']+c['QUERY_BATCH'],'request_updates':m,'command_records':1,'own_writes':1,'own_read_requests_or_responses':2},
      'payload_limbs64':{'publication_reply':4,'held_request':4,'helper_command':1,'own_write_header_and_data':4,'own_read_header':1,'own_read_response':3,'world_vector':1},
      'bootstrap_command_records':d,
      'admission_and_sharing_obligation':'Every source IO attempt is counted in executed instruction work, including locally rejected offers. Bad code may attempt one IO per instruction per powered processor, so multiply the actual processor/rate envelope; nominal publication counts are not a hostile raw-ingress envelope. Physical serializers bound EVERY data/control/reset symbol before the receiver parser. START/END/malformed/reset costs, receiver assembly/drop/timer work and sharing with request, maintenance and active-sense traffic require the actual port graph/capacity allocation. Raw converter attempts, owned-read time and delivered force draw retain separate physical prices.'}


def primary_consumption_check():
    c=compile_check(Design(origins=13,physical_parameters=(('LOAD_MARGIN',300),('ISOLATION_MARGIN',180))))
    key=3+c.constants['VIEW_WORDS'];results=[]
    for primary in (690,710):
        p=RawPorts(c)
        for origin in range(13):
            load=690 if origin<=6 else 710
            for bank in range(2):p.fast[(origin,bank,key)]=load;p.fast[(origin,bank,key+2)]=0
        m=Machine(c);m.enter('permission',(c.constants['TARGET_BASE'],0));changed=[False]
        def replace(machine,ports):
            if not changed[0] and 0<=machine.pc<len(machine.C):
                op,a,b,n,primitive=decode(machine.C[machine.pc])
                if op==IO and 0<=primitive<len(PRIMITIVES) and PRIMITIVES[primitive]=='fast_cmp':
                    before=(machine.C[:],machine.R[:],machine.W[:],machine.pc)
                    ports.fast[(0,0,key)]=primary;ports.fast[(0,1,key)]=primary;ports.fast[(0,0,key+2)]=1000;ports.fast[(0,1,key+2)]=1000
                    require(before==(machine.C,machine.R,machine.W,machine.pc),'Primary input write altered execution')
                    changed[0]=True
        m.run(p,until_yield=False,hook=replace);results.append(m.result())
    require(results==[1,0],'Primary input is not consumed in actual cut permission')
    return {'same_auxiliary_inputs':True,'primary_values':[690,710],'actual_permission_results':results,'changed_private_or_code_state':False,'scope':'A full primary-field replacement changes permit/defer in the executed same program. Functional field availability and whole-window support still have their physical suppliers.'}


def clipping_checks():
    cases=0;encoded=[]
    for true in (0,1,990,1000):
        for noise in range(-10,11):
            raw=32+true+noise
            require(22<=raw<=1042,'Nominal tagged numeric value is out of range')
            decoded=max(0,raw-32);clipped=min(1000,decoded)
            require(abs(clipped-true)<=abs((raw-32)-true),'Projection increased nominal sensor error')
            cases+=1
    c=compile_check(Design(fast_batch=1));k=c.constants
    for raw in (32-10,32,32+1000,32+1010,32+1500,WORD_MASK):
        m=formation(c);p=RawPorts(c);m.W[k['FAST_CURSOR']]=k['VIEW_WORDS']+k['CONNECTORS_A']+k['CONNECTORS_B']
        for member in range(k['CONNECTORS_A']):p.functional[(0,0,member,1)]=raw
        for _ in range(k['CONNECTORS_A']):m.enter('publish_fast');m.run(p,until_yield=False)
        key=3+k['VIEW_WORDS']+2;values=[x[2] for x in p.publications if x[0]=='source_offer_fast' and x[1][1]==key]
        expected=1000-min(1000,max(0,raw-32)) if 22<=raw<=1042 else WORD_MASK
        require(values and all(v==expected for v in values),'Actual clipping code differs from tagged format')
        encoded.append({'raw':raw,'deficit':expected})
    return {'error_preservation_cases':cases,'executed_endpoint_and_invalid_cases':encoded}

def circular_checks():
    d=Design(physical_parameters=(('CAM_VERIFY_RADIUS',1),('POSE_VERIFY_RADIUS',1)))
    c=compile_check(d);p=RawPorts(c);m=Machine(c);m.enter('estimate',(3,31))
    def wrap(machine,ports):
        if 0<=machine.pc<len(machine.C):
            op,a,b,n,primitive=decode(machine.C[machine.pc])
            if op==IO and 0<=primitive<len(PRIMITIVES):
                name=PRIMITIVES[primitive]
                if name=='fast_cmp':
                    origin,bank,key,pivot=[signed(machine.R[i]) for i in range(b,b+n)]
                    ports.fast[(origin,bank,key)]=31 if pivot==15 else 0
                elif name=='fast_range':
                    origin,bank,key,lower,upper=[signed(machine.R[i]) for i in range(b,b+n)]
                    ports.fast[(origin,bank,key)]=0
    m.run(p,until_yield=False,hook=wrap)
    require(m.result()==16 and m.W[c.constants['EST_VALID']]==0,'Circular middle candidate was certified')
    # Unknown cam still drives the generic normal cam, so a physical stop can
    # bring it into a chart; that generic drive is disabled by actual abort routing.
    a=formation(c);ap=RawPorts(c);view=populated_view(c,0,0);ap.set_view(0,view)
    for origin in range(d.origins):
        for bank in range(2):ap.fast[(origin,bank,3)]=WORD_MASK
    a.enter('helper',(0,));a.run(ap,until_yield=False)
    require(any(key[1]==c.constants['CAM_PORT'] and value==20 for key,value in ap.fields.items()),'Unknown cam deadlocks by blanket silence')
    require(not any(key[1] not in (c.constants['CAM_PORT'],c.constants['MODE_PORT']) and value for key,value in ap.fields.items()),'Unknown cam selected a substantive field')
    # Abort recovery uses raw keeper/end-stop contacts, not a fabricated cam chart.
    b=formation(c);bp=RawPorts(c);view=populated_view(c,0,0,1);bp.set_view(0,view)
    for origin in range(d.origins):
        for bank in range(2):bp.fast[(origin,bank,3)]=WORD_MASK
    b.enter('helper',(0,));b.run(bp,until_yield=False)
    require(any(event[0]=='command' and event[2]==26 for event in bp.events),'Abort depended on obtaining a normal cam chart')
    triangle=interior=0
    for length in (16,32,64):
        distance=lambda x,y:min((x-y)%length,(y-x)%length)
        for candidate in range(2*length):
            for sample in range(length):
                for current in range(length):
                    radius=abs(candidate-sample);beta=distance(sample,current)
                    require(distance(candidate,current)<=radius+beta,'Circular quotient triangle failed');triangle+=1
        # Four equal bands, captured radius1 and source age/error1: verified
        # current ball2 at an interior stop; adjacent/wrap boundaries abstain.
        band=length//4;error=2
        for center in range(length):
            offset=center%band
            if offset>=error and offset+error<band:
                for current in range(length):
                    if distance(center,current)<=error:
                        require(current//band==center//band,'A certified circular ball crossed its selected band');interior+=1
    return {'all_nominal_wrap_search_candidate':16,'verified':False,'generic_normal_cam_survives_unknown_chart':True,'abort_uses_contacts_without_cam_chart':True,'circular_triangle_cases':triangle,'band_containment_cases':interior,'scope':'Range soundness is independent of the linear candidate; normal forward motion to a retained interior stop supplies liveness under the physical source conditions.'}


def processing_certificate(compiled,bounds):
    """Local arithmetic with explicit raw connector inventory; no global win."""
    c=compiled.constants;mu=1<<26;fast=F(101,100);minimum=F(c['FRAME_STEPS'],mu)/fast;own_read_delay=F(1,64);maximum=F(bounds['padded_frame_upper'],mu)+c['MAINT_BATCH']*own_read_delay
    require(bounds['active_frame_upper']<=c['FRAME_STEPS'],'Active program exceeds padded frame')
    require(bounds['padded_frame_upper']<1<<64,'Retirement-counter reuse ambiguous within a frame')
    require(F(12*(c['CONVERSION_POLLS']-2),mu*fast)>F(1,64),'Conversion polling can time out before nominal completion')
    targets=c['DEGREE'];source_slots=2*targets*targets
    query_period=(math.ceil(source_slots/c['QUERY_BATCH'])+1)*maximum
    maintenance_period=(math.ceil(c['RAW_MAINT_HEADS']/c['FAST_BATCH'])+1)*maximum
    plant_period=2*maximum
    fold=(1+math.ceil((max(c['CONNECTORS_A'],c['CONNECTORS_B'])-1)/c['FAST_BATCH']))*maximum
    query_lifetime=math.ceil(fast*(query_period+1+2+2))+4
    maintenance_lifetime=math.ceil(fast*(maintenance_period+1+2+2))+4
    plant_lifetime=8
    require(F(plant_lifetime)/fast>plant_period+2,"Plant receipts expire before the next nominal offer")
    cap=lambda value:(1<<value.bit_length())-1
    query_cap=cap(query_lifetime);maintenance_cap=cap(maintenance_lifetime);plant_cap=cap(plant_lifetime)
    query_age=1+2+2+query_lifetime
    pose_age=1+2+2+maintenance_lifetime
    functional_age=pose_age+fold
    plant_age=1+2+2+plant_lifetime
    require((c['READ_WAIT_FRAMES']-1)*minimum>query_age+6,'Cell wait omits a possible final word tail')
    require(F(c['BOOT_DRAIN_STEPS'],mu*fast)>3,'Pre-publication drain omits old conversion/reply residence')
    boot_time=F(bounds['boot_padded_upper']+16,mu)
    require((c['ENTRY_FRAMES']-1)*minimum>boot_time+max(query_cap,maintenance_cap)+4,'Maintenance entry does not clear arbitrary I debt')
    require((c['PLANT_ENTRY_FRAMES']-1)*minimum>boot_time+plant_cap+4,'Plant entry does not clear its actual I debt')
    per_target=(math.ceil(targets/c['MAINT_BATCH'])+1)*maximum
    stage_wait_min=(c['POST_STAGE_FRAMES']-1)*minimum
    require(stage_wait_min>pose_age+6,'Post-stage contact wait omits sample age/word tails')
    stage_wait_max=(c['POST_STAGE_FRAMES']+1)*maximum+per_target
    cell=(c['READ_WAIT_FRAMES']+2*math.ceil(targets/c['MAINT_BATCH'])+2)*maximum+4
    scan=(c['BAYS']*c['IMAGE_CELLS']+2)*cell+stage_wait_max
    watch_min=(c['WATCH_FRAMES']-1)*minimum
    require(watch_min>scan+per_target,'Full scan can time out before finishing')
    work=max(scan+per_target+8,50000+2*(c['WATCH_FRAMES']+1)*maximum+per_target+40)
    entry=boot_time+c['ENTRY_FRAMES']*maximum+per_target+8
    compare_to_emit=F(bounds['instruction_upper_bounds']['helper']+64,mu)+own_read_delay
    withdrawal=per_target+2*3+6+3
    horizon=functional_age+compare_to_emit+withdrawal
    # This is a source-law instantiation, not a guarantee inferred from shunt pose.
    error=F(1,100);load_rate=F(1,10000);isolation_rate=F(1,12000)
    load_needed=error+load_rate*horizon;gap_needed=error+isolation_rate*horizon
    require(F(c['LOAD_MARGIN'],1000)>=load_needed,'Load margin fails its explicit future envelope')
    require(F(c['ISOLATION_MARGIN'],1000)>=gap_needed,'Isolation margin fails its explicit future envelope')
    require(F(1,5)+error+F(c['LOAD_MARGIN'],1000)<1,'Working low-load guard lacks useful margin')
    require(error+F(c['ISOLATION_MARGIN'],1000)<F(1,5),'Working isolation guard lacks useful margin')
    require(F(23)/minimum<64,'Nominal branch publication rate exceeds its physical envelope')
    cam_beta=F(1,4)+pose_age+compare_to_emit
    require(c['CAM_VERIFY_RADIUS']>=2*cam_beta,'Cam range cannot cover every nominal value at a stable stop')
    require(c['CAM_ERROR']>=c['CAM_VERIFY_RADIUS']+cam_beta,'Cam classification forgets its range certificate radius')
    require(F(c['SEGMENT'],4)>c['CAM_ERROR'],'Cam work stop has no recognizable interior')
    pose_beta=F(1,4)+500*(pose_age+compare_to_emit)
    require(c['POSE_VERIFY_RADIUS']>=2*pose_beta,'Pose range is too narrow for the declared raw rate')
    required_rank_error=c['BAYS']*(c['POSE_VERIFY_RADIUS']+pose_beta)+c['RESERVE_CAP']+10*c['CAM_ERROR']
    require(c['PROGRESS_ERROR']>=required_rank_error,'Progress mark ignores validated pose intervals')
    require(watch_min>scan+per_target+c['HIGH_STEP']+4*c['PROGRESS_ERROR']+1,'A complete scan plus one unit-rate progress milestone can time out')
    native_step_bound=16384
    return {'connector_counts':[c['CONNECTORS_A'],c['CONNECTORS_B']],'instruction_service_min_per_quantum':mu,'instruction_service_max_per_quantum':str(mu*fast),'frame_min':str(minimum),'frame_max':str(maximum),'own_read_nonretirement_delay':str(own_read_delay),'own_read_waits_per_frame':c['MAINT_BATCH'],'query_period':str(query_period),'maintenance_period':str(maintenance_period),'plant_period':str(plant_period),'functional_fold_span':str(fold),'query_receipt_lifetime':query_lifetime,'maintenance_receipt_lifetime':maintenance_lifetime,'plant_receipt_lifetime':plant_lifetime,'arbitrary_counter_caps':[query_cap,maintenance_cap,plant_cap],'query_age':query_age,'pose_age':pose_age,'functional_age':str(functional_age),'plant_age':plant_age,'comparison_to_emission':str(compare_to_emit),'cut_withdrawal':str(withdrawal),'functional_guard_horizon':str(horizon),'raw_cam_error_and_age_bound':str(cam_beta),'raw_pose_error_and_age_bound':str(pose_beta),'required_progress_error':str(required_rank_error),'cam_work_stop_half_band':c['SEGMENT']//2,'raw_uniform_failed_state_load_rate':str(load_rate),'raw_uniform_failed_state_isolation_rate':str(isolation_rate),'required_load_margin':str(load_needed),'required_isolation_margin':str(gap_needed),'post_stage_wait_min':str(stage_wait_min),'per_target_response':str(per_target),'conservative_cell_transaction':str(cell),'complete_scan':str(scan),'watch_min':str(watch_min),'high_water_step':c['HIGH_STEP'],'long_rank_min_rate':1,'extra_mark_window':str(scan+per_target+c['HIGH_STEP']+4*c['PROGRESS_ERROR']+1),'local_nontransferable_work':str(work),'new_bank_entry_before_driver_geometry':str(entry),'wide_instruction_upper_per_frame':bounds['padded_frame_upper'],'native64_step_upper':native_step_bound,'native64_work_upper_per_frame':native_step_bound*bounds['padded_frame_upper'],'code_cell_transfer_limbs64':3,'reply_transfer_limbs64':4,'private_memory_limbs64':4,'scope':'Conditional LOCAL processor/acquisition/conduct arithmetic for the provisional closed-enclosure11-conduit source and stated connector counts and raw failed-state envelopes. Full connector map, geometry, energy/thermal prices and same-history renewal remain parent obligations.'}


def counter_and_common_image_checks(compiled):
    other=compile_check(Design(own_bay=0))
    require(other.image==compiled.image,'Common P depends on a producer bay identity')
    c=compiled.constants;cases=[]
    for offset in (0,(1<<64)-10,(1<<64)-c['FRAME_STEPS']//2):
        m=formation(compiled);p=RawPorts(compiled);m.retired=offset;m.enter('frame');before=m.steps
        require(m.run(p)=='yield','Finite modulo-counter frame did not yield')
        elapsed=m.steps-before
        require(elapsed>=c['FRAME_STEPS'] and elapsed<=WorkBound(compiled).report()['padded_frame_upper'],'Counter wrap lost local pacing bound')
        cases.append({'offset':offset,'instructions':elapsed,'final_counter':m.retired})
    m=Machine(compiled);m.C[0]=encode(HALT);m.W[-1]=987;old=m.C[:];m.pc=100;m.reset_entry()
    require(m.C==old and m.W[-1]==987 and m.pc==0,'Reset silently cleans code/private memory')
    # An actual sibling executes independently and cannot advance this processor's
    # local counter. Primary/I writes likewise have no path to the register.
    left=Machine(compiled);right=Machine(compiled);lp=RawPorts(compiled);rp=RawPorts(compiled)
    before=left.retired
    for _ in range(100):right.step(rp)
    lp.fast[(0,0,0)]=WORD_MASK;lp.I[:]=[WORD_MASK]*len(lp.I)
    require(left.retired==before and right.retired==100,'Counter is a sibling sum or input register')
    # Physical conversion and queue residence continue during CPU halt.
    left.halted=True;lp.conversion_delay=20;lp.perform('source_start_fast',(0,),None);lp.I[5]=7;lp.perform('source_offer_reply',(0,0),None)
    unchanged=left.retired;lp.elapse(20)
    require(left.retired==unchanged and lp.job is None and lp.delivered,'No-retirement physical time was erased')
    # An old ADC completion is not mislabeled as the first post-reset sample.
    drained=compile_check(Design(boot_drain_steps=128));dm=Machine(drained);dp=RawPorts(drained)
    dp.job=(20,'fast',999,777)
    for key in range(drained.constants['FAST_KEYS']):dp.fast[('head',key)]=600
    require(dm.run(dp)=='yield','Drained entry failed')
    first_fast=[event[2] for event in dp.publications if event[0]=='source_offer_fast']
    require(first_fast and all(value==600 for value in first_fast),'Pre-reset conversion was relabeled under a new key')
    # A funded old instruction completes with its actual latched code/operands
    # after power loss; power/reset do not erase the pending object.
    tail=Machine(compiled);tp=RawPorts(compiled);tail.C[0]=encode(STOREC,3,4);tail.R[3]=77;tail.R[4]=100
    require(tail.launch(funded=True),'Funded instruction did not launch')
    tail.powered=False;tail.C[0]=encode(HALT);tail.R[3]=88;tail.reset_entry()
    require(not tail.launch() and tail.pending_instruction is not None,'Power/reset erased or relaunched pending work')
    require(tail.complete(tp) and tail.C[100]==77,'Funded old operand completion disappeared after power loss')
    unfunded=Machine(compiled);require(not unfunded.launch(funded=False) and unfunded.steps==0,'Unfunded instruction executed')
    return {'common_image_across_physical_writer_leads':True,'counter_wrap_cases':cases,'reset_only_sets_entry':True,'counter_is_per_processor_not_primary_or_sibling':True,'physical_time_advances_without_retirement':True,'old_adc_drained_before_new_publication':True,'funded_instruction_tail_preserved_after_power_reset':True,'unfunded_launch_rejected':True}


def initial_prefix_checks():
    """Genuine different PC/private-prefix states, not only counter labels."""
    from copy import deepcopy
    c=compile_check(Design(boot_drain_steps=1024));initial=Machine(c,poison=999);old=RawPorts(c)
    old.world_latch=(60,60)
    loop=next(node for node in c.functions['boot'].body if isinstance(node,ast.While) and 'cpu_count' in ast.unparse(node.test))
    loop_pc=c.line_spans[f'boot:{loop.lineno}'][0]
    snapshots=[deepcopy(initial)];points={40,150}
    while initial.steps<10000:
        if initial.steps in points:snapshots.append(deepcopy(initial))
        if initial.pc==loop_pc:
            elapsed=(initial.retired-initial.R[c.registers[('boot','drain_start')]])%(1<<64)
            if elapsed>=128:
                require(elapsed<512,'Constructed entry leaves too little real drain')
                snapshots.append(deepcopy(initial));break
        initial.step(old)
    require(len(snapshots)==4,'Prefix checkpoint construction failed')
    results=[]
    for index,m in enumerate(snapshots):
        p=RawPorts(c);p.world_latch=(60,60);p.I[:]=[WORD_MASK]*len(p.I);p.valid=True
        p.job=(250,'fast',999,777);p.offer_pending=[(252,'source_offer_reply',(0,0),WORD_MASK)]
        for key in range(c.constants['FAST_KEYS']):p.fast[('head',key)]=600
        # Clock offset is independent of the genuine execution-phase difference.
        offset=(index+1)*123456789;delta=(offset-m.retired)%(1<<64);m.retired=offset
        if m.pc==loop_pc:
            reg=c.registers[('boot','drain_start')];m.R[reg]=(m.R[reg]+delta)%(1<<64)
        initial_pc=m.pc;start=m.steps
        while not p.publications and m.steps-start<20000:
            require(m.step(p),'Initial prefix unexpectedly blocked')
            require(p.world_latch==(60,60),'Entry consumed unknown I as active feedback')
            require(not any(key[1] not in (c.constants['CAM_PORT'],c.constants['MODE_PORT']) and value for key,value in p.fields.items()),'Unformed helper issued a stroke')
        require(p.publications and p.now>252,'A new publication preceded old transaction drainage')
        require(p.publications[0][2]==600,'Initial arbitrary I became a fresh publication')
        require(m.W[c.constants['ENTRY']]==c.constants['ENTRY_FRAMES'] and m.W[c.constants['PLANT_ENTRY']]==c.constants['PLANT_ENTRY_FRAMES'],'Initial phase consumed quarantine debt early')
        results.append({'initial_pc':initial_pc,'counter_offset':offset,'first_publication_after_instructions':m.steps-start,'remaining_maintenance_frames':m.W[c.constants['ENTRY']],'remaining_plant_frames':m.W[c.constants['PLANT_ENTRY']]})
    require(len({x['initial_pc'] for x in results})>=3 and len({x['first_publication_after_instructions'] for x in results})>=3,'Initial timing variation is only a counter relabeling')
    return {'different_actual_prefix_states':results,'scope':'Prefix invariants before first publication, or drain loop with sufficient remaining debt-clearing interval. Not arbitrary-PC stabilization or arbitrary past controller state.'}

def main():
    require(not sys.flags.optimize,'Optimized Python invalidates checks')
    parser=argparse.ArgumentParser(description=__doc__);g=parser.add_mutually_exclusive_group(required=True);g.add_argument('--check',action='store_true');g.add_argument('--write',action='store_true');args=parser.parse_args()
    names=('program_source.py','program_model.py','PROGRAM.md')
    before={name:digest(HERE/name) for name in names}
    evidence=HERE/'program_results.json'
    expected=json.loads(evidence.read_text()) if args.check else None
    if expected:require(expected['sources']==before,'Program sources changed; inspect before refresh')
    compiled,first=basic_checks()
    refinement=refinement_checks(compiled);changing=changing_input_checks(compiled);adversarial=adversarial_checks(compiled);functional=functional_and_unknown_checks(compiled)
    bounds=WorkBound(compiled).report()
    for name,data in refinement['provider_and_frame'].items():require(data['instructions']<=bounds['instruction_upper_bounds'][name],name+' exceeded its syntax work bound')
    require(refinement['maximum_helper_instructions']<=bounds['instruction_upper_bounds']['helper'],'Helper exceeded syntax work bound')
    full=compile_check(Design(degree=40,bays=80,origins=13,fast_batch=16,query_batch=4,maintenance_batch=4,connectors_a=11,connectors_b=11,entry_frames=4096,plant_entry_frames=64,read_wait_frames=950,post_stage_frames=2100,watch_frames=2400000000,conversion_polls=88259,frame_steps=1<<26,boot_drain_steps=4*(1<<26),physical_parameters=(("POSE_MAX",1<<44),("LOAD_MARGIN",300),("ISOLATION_MARGIN",180),("ROW_VERIFY_RADIUS",12),("POSE_VERIFY_RADIUS",2000000),("CAM_VERIFY_RADIUS",4000),("CLAMP_VERIFY_RADIUS",4000),("CAM_ERROR",6000),("JOIN_ERROR",6000),("SEGMENT",32000),("GUARD",16000),("PROGRESS_ERROR",250000000),("HIGH_STEP",594059405))))
    full_bounds=WorkBound(full).report()
    timing=processing_certificate(full,full_bounds);counter=counter_and_common_image_checks(compiled);circular=circular_checks();initial_family=initial_prefix_checks();primary=primary_consumption_check();clipping=clipping_checks();abort=abort_protocol_checks()
    result={'schema':'local-program-v1','python_major_minor':list(sys.version_info[:2]),'scope':'finite stored bank program; physical/evidence/recurrence suppliers remain conditional','sources':before,'code_cells':len(compiled.nodes),'image_cells':len(compiled.image),'register_words':compiled.next_register,'data_words':compiled.constants['DATA_WORDS'],'stack_depth':compiled.stack_depth,'initial_frame':first,'refinement':refinement,'changing_inputs':changing,'adversarial':adversarial,'functional_and_unknown':functional,'small_bounds':bounds,'full_layout_bounds':full_bounds,'processing_certificate':timing,'counter_and_identity':counter,'circular':circular,'initial_prefix_family':initial_family,'definite_assignment':definite_assignment(compiled),'whole_frame_io_inventory':io_inventory(full),'primary_consumption':primary,'functional_clipping':clipping,'abort_protocol':abort}
    require(before=={name:digest(HERE/name) for name in names},'Program inputs changed during verification')
    path=HERE/'program_results.json'
    if args.write:path.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n',encoding='utf-8')
    else:require(result==expected,'Program evidence differs')
    print('PASS finite program',len(compiled.nodes),'code cells;',compiled.next_register,'register words;',compiled.constants['DATA_WORDS'],'data words')

if __name__=='__main__':main()

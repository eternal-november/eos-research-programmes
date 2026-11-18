"""Ordinary-ISA vector refresh: source-local executable evidence.

This is a scanner, not a controller, a field transducer or a renewal theorem.
The physical set_field primitive and its work/timing remain open suppliers.
"""
from __future__ import annotations
import argparse
from collections import Counter
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import types

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
BASE = "fb85a7606f45e52d0cd48e023ab9776dd526640c"
if sys.flags.optimize:
    raise RuntimeError("Unoptimized Python is required")
if sys.version_info[:2] != (3, 12):
    raise RuntimeError("This evidence is pinned to Python 3.12")
ISA_PATH = "theories-and-designs/byzantine-control/local-control/program_model.py"
SCANNER_SOURCE = """
def refresh_frame():
    count = 0
    while count < UPDATES:
        j = w[CURSOR] % SLOTS
        target = j // (2 * IMAGE_BITS)
        side = (j // IMAGE_BITS) % 2
        bit = j % IMAGE_BITS
        cell = code[bit // SYMBOL_BITS]
        divisor = 1 << (bit % SYMBOL_BITS)
        value = (cell // divisor) % 2
        set_field(target, side, bit, 2 * value - 1)
        j = j + 1
        if j == SLOTS:
            j = 0
        w[CURSOR] = j
        count = count + 1

def main():
    w[CURSOR] = 0
    while 1:
        refresh_frame()
        yield_frame()
"""

def require(ok, why):
    if not ok:
        raise AssertionError(why)

def load_isa(repo):
    text = subprocess.check_output(
        ["git", "show", BASE + ":" + ISA_PATH], cwd=repo
    ).decode("utf-8-sig").replace("\r\n", "\n")
    module = types.ModuleType("_vector_refresh_frozen_isa")
    module.__file__ = str(Path(repo) / ISA_PATH)
    sys.modules[module.__name__] = module
    exec(compile(text, module.__file__, "exec"), module.__dict__)
    # Isolated in-memory ABI extension; repository source is untouched.
    module.PRIMITIVES = module.PRIMITIVES + ("set_field",)
    module.PRIM = {name: i for i, name in enumerate(module.PRIMITIVES)}
    module.PRIM_ARITY["set_field"] = 4
    module.PRIM_WORD_COST["set_field"] = 1
    # The value 1 is VM instruction instrumentation, not physical work.
    class Source:
        def read_text(self, **unused):
            return SCANNER_SOURCE
    module.SOURCE = Source()
    module.source_sha256 = hashlib.sha256(text.encode()).hexdigest()
    return module

@dataclass(frozen=True)
class Design:
    image_cells: int
    degree: int
    updates: int

    def constants(self):
        for value in (self.image_cells, self.degree, self.updates):
            require(type(value) is int and value > 0, "positive integer design required")
        bits = 192 * self.image_cells
        slots = 2 * self.degree * bits
        require(max(bits, slots, self.updates) < 2**111, "signed immediate capacity")
        require(self.image_cells < 2**24, "finite code-address encoding")
        return dict(STACK_WORDS=32, DATA_WORDS=33, CURSOR=32,
                    IMAGE_BITS=bits, SYMBOL_BITS=192,
                    SLOTS=slots, UPDATES=self.updates)

class HeldFields:
    """Finite sparse representation of source-held ternary settings.

    Missing slots denote zero. Physical propagation/forces are not implemented.
    No intended image or healthy-donor identity is available to this object.
    Offer/rejection counters are checker instrumentation, not runtime state.
    """
    def __init__(self, design, physical_targets=None):
        self.d = design
        self.bits = 192 * design.image_cells
        self.targets = tuple(physical_targets if physical_targets is not None
                             else (("body", i) for i in range(design.degree)))
        require(len(self.targets) == design.degree and
                len(set(self.targets)) == design.degree, "injective target wiring")
        self.held = {}
        self.offers = 0
        self.rejected = 0

    def key(self, target, side, bit):
        if (0 <= target < self.d.degree and side in (0, 1)
                and 0 <= bit < self.bits):
            return self.targets[target], side, bit
        return None

    def perform(self, name, args, machine):
        if name == "yield_frame":
            return 0
        if name != "set_field":
            # Other legacy I/O is outside this standalone scanner harness.
            self.rejected += 1
            return 0
        target, side, bit, value = args
        self.offers += 1
        key = self.key(target, side, bit)
        if key is None or value not in (-1, 0, 1):
            self.rejected += 1
            return 0
        self.held[key] = value
        return 1

    def advance(self, machine):
        # One ordinary retirement is recorded by the imported Machine itself.
        # This adapter makes no assertion about elapsed physical time.
        pass

def compile_scanner(isa, design):
    c = isa.Compiler(design).compile()
    require(not any(n[0] == isa.STOREC for n in c.nodes), "nominal self-code write")
    require(c.stack_depth < 32 and c.next_register < 2**24, "finite ISA layout")
    require(isa.LOADC in [n[0] for n in c.nodes], "actual C reads required")
    return c

def frame(machine, ports, updates, limit=None):
    before = machine.steps
    status = machine.run(ports, budget=limit or (1000 + 300 * updates))
    require(status == "yield", "scanner did not finish its finite frame")
    return machine.steps - before

def expected(machine, design, slot):
    bits = 192 * design.image_cells
    target, remainder = divmod(slot, 2 * bits)
    side, bit = divmod(remainder, bits)
    value = (machine.C[bit // 192] >> (bit % 192)) & 1
    return (target, side, bit, 2 * value - 1)

def isolated_frame(isa, c, design, cursor, poison=123):
    m = isa.Machine(c, poison=poison)
    m.W[32] = cursor & isa.WORD_MASK
    m.enter("refresh_frame")
    p = HeldFields(design)
    before = m.steps
    status = m.run(p, budget=1000 + 300 * design.updates, until_yield=False)
    # enter installs a return address beyond C; the attempted next launch halts.
    require(status == "halt", "finite routine did not return")
    return m, p, m.steps - before

def io_machine(isa, compiled, args):
    m = isa.Machine(compiled)
    address = next(i for i, n in enumerate(compiled.nodes)
                   if n[0] == isa.IO and n[4] == isa.PRIM["set_field"])
    _, _, base, count, _ = compiled.nodes[address]
    m.pc = address
    for i, value in enumerate(args):
        m.R[base+i] = value & isa.WORD_MASK
    require(count == 4, "field descriptor arity")
    return m

class DelayedFields(HeldFields):
    """Two-slot packet witness only; not a full physical delivery supplier."""
    def __init__(self, design):
        super().__init__(design)
        self.now = 0
        self.delay = 0
        self.pending = []

    def perform(self, name, args, machine):
        require(name == "set_field", "countercase uses only field offers")
        target, side, bit, value = args
        key = self.key(target, side, bit)
        self.offers += 1
        if key is None or value not in (-1,0,1) or len(self.pending) == 2:
            self.rejected += 1
            return 0
        require(0 <= self.delay <= 2, "bounded witness residence")
        self.pending.append((self.now+self.delay, key, value))
        return 1

    def deliver(self, time):
        require(time >= self.now, "causal witness clock")
        self.now = time
        due = sorted((x for x in self.pending if x[0] <= time), key=lambda x:x[0])
        self.pending = [x for x in self.pending if x[0] > time]
        for _, key, value in due:
            self.held[key] = value

def generate(repo):
    isa = load_isa(repo)
    large = Design(8192, 40, 7)
    c = compile_scanner(isa, large)
    require(len(c.nodes)==75 and c.next_register==60 and c.stack_depth==2,
            "recheck source-level path counts after compiler change")
    # CFG check binds the count derivation to actual imported instructions:
    # 2 entry, 3(q+1) loop tests, 52q body steps, 3 per wrap, 2 return.
    require(c.labels == {"refresh_frame":2,"while.1":4,"else.3":56,
                         "endif.4":56,"endwhile.2":62,"main":64,
                         "while.5":67,"endwhile.6":73}, "CFG label drift")
    require([n[0] for n in c.nodes[53:56]] == [isa.LI,isa.MOV,isa.JMP]
            and c.nodes[52][4]==56 and c.nodes[61][4]==4,
            "cursor wrap path drift")
    bits = 192*large.image_cells
    slots = 2*large.degree*bits
    starts = (0,80,191,192,bits-3,bits,2*bits-3,
              slots-7,slots-3,(1<<255)-1,-(1<<255))
    slice_results=[]
    for start in starts:
        m,p,steps = isolated_frame(isa,c,large,start)
        j0 = isa.signed(start & isa.WORD_MASK) % slots
        wraps = (j0+large.updates)//slots
        require(steps==7+55*large.updates+3*wraps,"routine instruction count")
        require(p.offers==large.updates and p.rejected==0,"q bounded offers")
        require(m.executed[isa.LOADC]==large.updates,"one actual C read per bit")
        for offset in range(large.updates):
            t,b,a,v = expected(m,large,(j0+offset)%slots)
            require(p.held[p.key(t,b,a)]==v,"physical destination/value mismatch")
        require(m.W[32]==(j0+large.updates)%slots,"finite cursor")
        slice_results.append(dict(start=str(start),steps=steps,wraps=wraps))
    # Change an actually stored C word, not a protected checker template.
    # Routine entry bypasses main's first instruction, so this is a valid
    # data-provenance countercase without claiming the altered program nominal.
    m = isa.Machine(c)
    m.C[0] ^= 1<<80
    m.W[32] = 80
    m.enter("refresh_frame")
    p = HeldFields(large)
    require(m.run(p,budget=3100,until_yield=False)=="halt","mutated-C probe")
    require(p.held[p.key(0,0,80)]==1,"actual mutated code bit was not copied")
    # Complete manageable image, including every bit of its executing program.
    small = Design(80,1,64)
    sc = compile_scanner(isa,small)
    sm = isa.Machine(sc,poison=isa.WORD_MASK)
    sm.C[-1] = (1<<191)+0xA55A
    sp = HeldFields(small)
    small_slots = small.constants()["SLOTS"]
    require(small_slots % small.updates==0,"complete-cycle test sizing")
    frame_count=small_slots//small.updates
    totals=Counter()
    for k in range(frame_count):
        old_cursor=sm.W[32] if k else 0
        wraps=(old_cursor+small.updates)//small_slots
        count=frame(sm,sp,small.updates)
        bound=(17 if k==0 else 13)+55*small.updates+3*wraps
        require(count==bound,"entry/steady exact frame count")
        totals[count]+=1
    require(sm.W[32]==0 and len(sp.held)==small_slots,"full finite scan")
    for slot in range(small_slots):
        t,b,a,v=expected(sm,small,slot)
        require(sp.held[sp.key(t,b,a)]==v,"full current-image vector mismatch")
    require(sm.executed[isa.LOADC]==small_slots and sm.code_writes==0,
            "C-read count or nominal self-modification")
    # Invalid physical addresses/values are bounded inert ordinary I/O.
    invalid=((-1,0,0,1),(large.degree,0,0,1),(0,-1,0,1),(0,2,0,1),
             (0,0,-1,1),(0,0,bits,1),(0,0,0,2))
    bad=HeldFields(large)
    for args in invalid:
        im=io_machine(isa,c,args)
        require(im.step(bad) and im.steps==1,"invalid I/O did not retire")
    require(bad.rejected==len(invalid) and not bad.held,"invalid address affected state")
    # Reset/repaired current C and R do not delete an older funded instruction.
    old=io_machine(isa,c,(0,0,0,-1))
    op=HeldFields(large)
    require(old.launch(),"old ordinary launch")
    old.reset_entry()
    old.R=[0]*len(old.R)
    require(old.complete(op),"funded old suffix disappeared")
    require(op.held[op.key(0,0,0)]==-1,"latched old value was silently replaced")
    # A newer +1 can arrive first, then be overwritten by an older -1.
    dp=DelayedFields(large)
    dp.delay=2
    require(io_machine(isa,c,(0,0,0,-1)).step(dp),"old packet offer")
    dp.now=1;dp.delay=0
    require(io_machine(isa,c,(0,0,0,1)).step(dp),"fresh packet offer")
    dp.deliver(1)
    require(dp.held[dp.key(0,0,0)]==1,"fresh witness missing")
    dp.deliver(2)
    require(dp.held[dp.key(0,0,0)]==-1,"non-FIFO witness missing")
    # A pending record retains its captured physical destination across a
    # change of the present logical route; resolving it at delivery is wrong.
    rp=DelayedFields(large);rp.delay=2
    require(io_machine(isa,c,(0,0,0,1)).step(rp),"destination offer")
    captured=rp.pending[0][1]
    targets=list(rp.targets);targets[0]=("replacement-body",0);rp.targets=tuple(targets)
    rebound=rp.key(0,0,0)
    require(captured!=rebound,"destination distinction missing")
    rp.deliver(2)
    require(rp.held[captured]==1 and rebound not in rp.held,
            "old packet was rebound to replacement body")
    return dict(
        status="source-local ordinary-ISA construction; first-pass evidence",
        base=BASE,isa_sha256=isa.source_sha256,
        executable_inputs=dict(
            frozen_isa=dict(commit=BASE, path=ISA_PATH, sha256_lf=isa.source_sha256),
            current_sources_sha256_lf={Path(__file__).name: hashlib.sha256(
                Path(__file__).read_bytes().replace(b"\r\n",b"\n")).hexdigest()},
            python_version=sys.version,
            trust_boundary="Python 3.12 standard runtime and Git content retrieval; all nonstandard executable source is bound here"),
        source_sha256=hashlib.sha256(SCANNER_SOURCE.encode()).hexdigest(),
        scope="local ordinary-ISA scan and countercases; no physical delivery, guard, controller or recurrent proof",
        code_cells=len(c.nodes),registers=c.next_register,working_words=33,
        stack_depth=c.stack_depth,word_bits=isa.WORD_BITS,cell_bits=isa.CELL_BITS,
        routine_steps="7+55*q+3*floor((cursor_mod_K+q)/K)",
        initial_frame_steps="17+55*q+3*wraps",
        steady_frame_steps="13+55*q+3*wraps",
        large_design=dict(image_cells=8192,degree=40,updates=7,
                          bits_per_image=bits,slots_per_source_bank=slots,
                          slices=slice_results),
        full_scan=dict(image_cells=80,degree=1,updates=64,
                       bits_per_image=15360,slots=small_slots,
                       frames=frame_count,retired_instructions=sm.steps,
                       frame_instruction_histogram={str(k):v for k,v in sorted(totals.items())},
                       actual_C_reads=sm.executed[isa.LOADC],
                       executing_code_and_changed_padding_copied=True),
        invalid_IOS=len(invalid),mutated_actual_C_word_copied=True,
        old_instruction_survives_reset=True,late_old_packet_overwrites_fresh=True,
        captured_destination_not_rebound=True,
        physical_work_for_new_IO="open source-local supplier; VM instrumentation is not a price",
        open_suppliers=["target-specific startup/configuration image",
                        "ISA physical refinement for new IO", "field delivery/response",
                        "source-local formation and overlap", "same-history fault projection",
                        "complete resource/thermal inventory", "integrated controller and guard"])

def main():
    parser=argparse.ArgumentParser()
    mode=parser.add_mutually_exclusive_group()
    mode.add_argument("--write",action="store_true")
    mode.add_argument("--check",action="store_true")
    args=parser.parse_args()
    result=generate(REPO)
    record=HERE/"vector_refresh_results.json"
    if args.write:
        record.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n",encoding="utf-8")
        print("vector refresh record written")
    elif args.check:
        require(json.loads(record.read_text(encoding="utf-8-sig"))==result,
                "Vector refresh record differs")
        print("vector refresh record matches")
    else:
        print(json.dumps(result,indent=2,sort_keys=True))

if __name__ == "__main__":
    main()

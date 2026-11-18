"""Candidate complete threshold controller on the frozen ordinary ISA.

These are instruction-level checks and numerical loop bounds. The raw fixture
is not a physical simulator, a truthful-source oracle or a recurrent controller
verification. Production pacing is retained; boot coverage is stated exactly.
"""
from __future__ import annotations
import argparse
import ast
from collections import Counter
from dataclasses import asdict, replace
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import types

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
BASE = "fb85a7606f45e52d0cd48e023ab9776dd526640c"
PREFIX = "theories-and-designs/byzantine-control/local-control/"
SOURCE = HERE / "threshold_program_source.py"
FORBIDDEN = {"write_own", "own_equal", "request", "reply_equal", "source_capture_request",
             "source_start_cell", "source_offer_reply", "source_offer_missing"}
if sys.flags.optimize or sys.version_info[:2] != (3, 12):
    raise RuntimeError("Unoptimized Python 3.12 required")


def need(ok, message):
    if not ok:
        raise AssertionError(message)


def frozen(name):
    return subprocess.check_output(["git", "show", BASE + ":" + PREFIX + name],
                                   cwd=REPO).decode("utf-8-sig").replace("\r\n", "\n")


def hash_text(text):
    return hashlib.sha256(text.encode()).hexdigest()


def digest(path):
    return hashlib.sha256(path.read_bytes().replace(b"\r\n", b"\n")).hexdigest()


def load_isa():
    text = frozen("program_model.py")
    isa = types.ModuleType("_threshold_frozen_isa")
    isa.__file__ = str(HERE / "_frozen_isa.py")
    sys.modules[isa.__name__] = isa
    exec(compile(text, isa.__file__, "exec"), isa.__dict__)
    isa.PRIMITIVES = isa.PRIMITIVES + ("set_field",)
    isa.PRIM = {name: i for i, name in enumerate(isa.PRIMITIVES)}
    isa.PRIM_ARITY["set_field"] = 4
    isa.PRIM_WORD_COST["set_field"] = 1  # Instrumentation, not physical pricing.
    isa.SOURCE = SOURCE
    isa.source_hash = hash_text(text)
    return isa


def design_class(isa):
    class ThresholdDesign(isa.Design):
        def constants(self):
            for key, value in asdict(self).items():
                if key != "physical_parameters":
                    need(type(value) is int and value >= 0, "Exact nonnegative design field: " + key)
            need(self.bays == 1 and self.own_bay == 0, "One physical body per bank required")
            need(self.origins == 15, "This candidate uses fifteen consumed origins")
            need(75 <= self.image_cells < 2**24, "Finite image address range")
            c = super().constants()
            c.update(VECTOR_CURSOR=39, VECTOR_UPDATES=7,
                     IMAGE_BITS=192*self.image_cells,
                     VECTOR_SLOTS=2*self.degree*192*self.image_cells)
            need(c["VECTOR_CURSOR"] < c["TARGET_BASE"], "Cursor aliases target memory")
            need(c["VECTOR_SLOTS"] < 2**111 and c["FRAME_STEPS"] < 2**63
                 and c["BOOT_DRAIN_STEPS"] < 2**63, "Immediate/counter range")
            return c
    return ThresholdDesign


def production_design(isa):
    data = json.loads(frozen("geometry_results.json"))["design"]
    data["physical_parameters"] = tuple(tuple(p) for p in data["physical_parameters"])
    data.update(bays=1, own_bay=0, origins=15, query_batch=0)
    return design_class(isa)(**data)


def compile_program(isa, design):
    c = isa.compile_check(design)
    names = {isa.PRIMITIVES[n[4]] for n in c.nodes if n[0] == isa.IO}
    need(not names & FORBIDDEN, "Old reconstruction interface still operates")
    need("set_field" in names and any(n[0] == isa.LOADC for n in c.nodes), "Missing actual-C fields")
    need(not {"cell_result", "publish_queries", "clear_target"} & c.functions.keys(), "Old image machinery remains")
    return c


def bounds(isa, compiled):
    class NewBounds(isa.WorkBound):
        def limit(self, fn, node):
            if fn == "refresh_fields":
                n = self.c["VECTOR_UPDATES"]
                self.loops.append(dict(function=fn, line=node.lineno, condition=ast.unparse(node.test),
                                       iterations=n, variant="VECTOR_UPDATES-count"))
                return n
            if fn == "publish_plant":
                self.loops.append(dict(function=fn, line=node.lineno, condition=ast.unparse(node.test),
                                       iterations=2, variant="2-key"))
                return 2
            return super().limit(fn, node)
    b = NewBounds(compiled).report()
    # Do not inherit the old query-server inventory fields from report().
    keys = ("instruction_upper_bounds", "boot_active_upper", "boot_padded_upper",
            "active_frame_upper", "padded_frame_upper", "padded_frame_lower",
            "padding_scope", "loop_certificates", "loop_proof_scope",
            "private_array_bits", "private_bits", "private_words_with_metadata", "stack_depth")
    return {k: b[k] for k in keys}


def ports_class(isa):
    class ThresholdPorts(isa.RawPorts):
        """Raw per-instruction fixture, not elapsed physical time or field work."""
        def __init__(self, c):
            super().__init__(c)
            self.held_fields = {}
            self.field_offers = 0
            self.field_rejections = 0
            self.targets = tuple(("body", t) for t in range(c.constants["DEGREE"]))
        def perform(self, name, args, machine):
            if name == "set_field":
                target, side, bit, value = args
                self.field_offers += 1
                if not (0 <= target < self.c["DEGREE"] and side in (0, 1)
                        and 0 <= bit < self.c["IMAGE_BITS"] and value in (-1, 0, 1)):
                    self.field_rejections += 1
                    return 0
                self.held_fields[(self.targets[target], side, bit)] = value
                return 1
            need(name not in FORBIDDEN, "Nominal test invoked removed reconstruction primitive: " + name)
            return super().perform(name, args, machine)
    return ThresholdPorts


def initialized(isa, c):
    m = isa.Machine(c, poison=isa.WORD_MASK)
    m.W = [0]*len(m.W)
    return m


def call(isa, c, ports, name, args, limit, machine=None):
    m = machine or initialized(isa, c)
    m.enter(name, args)
    status = m.run(ports, budget=limit, until_yield=False)
    need(status == "halt" and m.C == c.image, "Finite call failed or changed code: " + name)
    return m


def fill_permission(c, p, target=0, low=125, bad=0, bad_value=3000):
    k = c.constants
    key = 3+target*k["FAST_TARGET_KEYS"]+k["VIEW_WORDS"]
    for origin in range(k["ORIGINS"]):
        for bank in range(2):
            for side in range(2):
                p.fast[(origin, bank, key+side)] = bad_value if origin < bad else low
                p.fast[(origin, bank, key+2+side)] = 0


def fill_rows(c, p, x=450, total=1050):
    for origin in range(c.constants["ORIGINS"]):
        for bank in range(2):
            p.fast[(origin, bank, 0)] = x
            p.fast[(origin, bank, 1)] = total
    p.fast[("head", 0)] = x
    p.fast[("head", 1)] = total


def helper_fixture(isa, c, p, half, phase, target=0):
    k = c.constants
    view = isa.populated_view(c, half, phase)
    cold = 1-half
    if phase == 1:
        view[k["ACT_A"]+cold] = k["WARM_AT"]
        view[k["ACT_ZERO_A"]+cold] = 0
    p.set_view(target, view)
    fill_permission(c, p, target)
    m = initialized(isa, c)
    base = k["TARGET_BASE"]+target*k["TARGET_WORDS"]
    m.W[base+k["STAGE_ID"]] = half*k["PHASES"]+phase+1
    return m, view


def local_checks(isa, c, b, Ports):
    k=c.constants; limit=b["instruction_upper_bounds"]
    guards=[]
    for load,bad,value,expected in ((125,0,0,1),(125,7,3000,1),(1100,7,0,0),(1100,8,0,1)):
        p=Ports(c);fill_permission(c,p,low=load,bad=bad,bad_value=value)
        m=call(isa,c,p,"permission",(k["TARGET_BASE"],0),limit["permission"]+100)
        need(m.result()==expected,"Seven/fifteen factual guard mismatch")
        guards.append(dict(actual_load=load,bad_slots=bad,bad_word=value,verdict=m.result(),instructions=m.steps))
    p=Ports(c)
    missing=call(isa,c,p,"permission",(k["TARGET_BASE"],0),limit["permission"]+100)
    need(missing.result()==0,"Missing permission data was accepted")
    phases=[]
    for half in (0,1):
        for phase in range(k["PHASES"]):
            p=Ports(c);m,view=helper_fixture(isa,c,p,half,phase)
            m=call(isa,c,p,"helper",(0,),limit["helper"]+100,m)
            event=next(e for e in reversed(p.events) if e[0]=="command")
            if phase==6:need(event[6]==k["CLAMP_PORT"] and event[8]==k["FORCE"],"Threshold close not selected")
            if phase==8:need(event[6]==k["ACT_PORT"] and event[7]==0 and event[8]==k["FORCE"],"Single-body activation failed")
            if phase==4:need(m.W[k["TARGET_BASE"]+k["TIMER"]]==k["WATCH_FRAMES"],"Phase4 reset branch changed")
            phases.append(dict(half=half,phase=phase,instructions=m.steps,command=list(event[2:])))
    # Missing CAM causes a bounded probing/watch branch, not an image oracle.
    p=Ports(c);m=call(isa,c,p,"helper",(0,),limit["helper"]+100)
    need(m.W[k["TARGET_BASE"]+k["WATCH_HALF"]]==3,"Unknown-cam branch lost")
    need(not any(e[0]=="command" and e[6] not in (0,k["CAM_PORT"],k["MODE_PORT"]) for e in p.events),"Unknown CAM selected substantive action")
    unknown_steps=m.steps
    p=Ports(c);m,view=helper_fixture(isa,c,p,0,6)
    view[k["ABORT_FULL"]]=1;view[k["CAM_ENTRY_A"]]=1;p.set_view(0,view)
    base=k["TARGET_BASE"];m.W[base+k["STAGE_ID"]]=27
    m=call(isa,c,p,"helper",(0,),limit["helper"]+100,m)
    need(m.W[base+k["EXITING_ABORT"]]==1,"Full abort did not enter retained exit")
    abort_steps=m.steps
    p=Ports(c);m,view=helper_fixture(isa,c,p,0,0);m.W[base+k["EXITING_ABORT"]]=1
    m=call(isa,c,p,"helper",(0,),limit["helper"]+100,m)
    need(m.W[base+k["EXIT_OBSERVED"]]==1 and m.W[base+k["EXIT_WAIT"]]==k["POST_STAGE_FRAMES"],"Exit wait was skipped")
    m.W[base+k["EXIT_WAIT"]]=0;m.enter("helper",(0,))
    need(m.run(p,budget=limit["helper"]+100,until_yield=False)=="halt" and not m.W[base+k["EXITING_ABORT"]],"Finite exit did not close")
    class NeverReady(Ports):
        def perform(self,name,args,machine):
            if name=="source_ready":return 0
            return super().perform(name,args,machine)
    no_input=NeverReady(c)
    timed=call(isa,c,no_input,"wait_conversion",(),limit["wait_conversion"]+100)
    need(timed.result()==0 and timed.io_counts["source_ready"]==k["CONVERSION_POLLS"]+1,
         "Unavailable conversion did not take bounded failure")
    return dict(guard=guards,missing_guard_instructions=missing.steps,helper_phases=phases,
                unknown_cam_instructions=unknown_steps,full_abort_instructions=abort_steps,
                unavailable_conversion_instructions=timed.steps,
                unavailable_conversion_polls=timed.io_counts["source_ready"],
                retained_exit_wait_checked=True,physical_view_fixture_not_hybrid_realizability=True)


def scanner_checks(isa,c,b,Ports):
    k=c.constants;K=k["VECTOR_SLOTS"];q=k["VECTOR_UPDATES"];checks=[]
    for start in (0,191,192,k["IMAGE_BITS"]-3,K-3,-(1<<255)):
        m=initialized(isa,c);m.W[k["VECTOR_CURSOR"]]=start&isa.WORD_MASK;p=Ports(c)
        m=call(isa,c,p,"refresh_fields",(),b["instruction_upper_bounds"]["refresh_fields"]+100,m)
        j0=isa.signed(start&isa.WORD_MASK)%K;wraps=(j0+q)//K
        need(m.steps==7+55*q+3*wraps and p.field_offers==q,"Integrated scanner count changed")
        for offset in range(q):
            j=(j0+offset)%K;target,rem=divmod(j,2*k["IMAGE_BITS"]);side,bit=divmod(rem,k["IMAGE_BITS"])
            value=2*((m.C[bit//192]>>(bit%192))&1)-1
            need(p.held_fields[(p.targets[target],side,bit)]==value,"Scanner did not read actual C")
        checks.append(dict(start=str(start),instructions=m.steps,wraps=wraps))
    m=initialized(isa,c);m.C[0]^=1<<80;m.W[k["VECTOR_CURSOR"]]=80;m.enter("refresh_fields");p=Ports(c)
    need(m.run(p,budget=2000,until_yield=False)=="halt" and p.held_fields[(p.targets[0],0,80)]==1,"Mutated stored C not consumed")
    return dict(slices=checks,actual_C_mutation_read=True,
                mutation_scope="Isolated routine with altered nonexecuted entry word; not nominal behavior of the altered complete image",
                full_production_image_scan_executed=False,
                complete_standalone_scan_evidence="vector_refresh_results.json at e9820af; separate scanner image and smaller interface")


def fixture_frames(isa,production,Ports):
    # Same full degree/image/geometry, explicitly changed pacing/drain only.
    fixture=replace(production,frame_steps=0,boot_drain_steps=1024)
    c=compile_program(isa,fixture);b=bounds(isa,c);k=c.constants;p=Ports(c);m=isa.Machine(c,poison=isa.WORD_MASK)
    need(m.run(p,budget=b["boot_padded_upper"]+b["padded_frame_upper"]+100)=="yield","Complete fixture boot/frame failed")
    need(m.W[k["VECTOR_CURSOR"]]==7 and m.W[k["ENTRY"]]==fixture.entry_frames-1 and p.world_latch==(60,60),"Fixture entry effects differ")
    boot_frame=m.steps
    observations=[]
    for x,total,expected in ((450,1050,(50,80)),(550,1050,(70,60))):
        q=Ports(c);fill_rows(c,q,x,total)
        n=initialized(isa,c);n.W[k["ENTRY"]]=1;n.enter("frame")
        need(n.run(q,budget=b["padded_frame_upper"]+100)=="yield" and q.world_latch==expected,"x/x+y reconstruction mismatch")
        need(q.field_offers==7 and n.C==c.image,"Frame omitted scanner or changed image")
        observations.append(dict(rows=[x,total],actual_world=list(q.world_latch),instructions=n.steps))
    q=Ports(c);n=initialized(isa,c);n.W[k["ENTRY"]]=1;n.enter("frame")
    need(n.run(q,budget=b["padded_frame_upper"]+100)=="yield" and q.world_latch==(60,60),"Unavailable rows did not fallback")
    return dict(design=asdict(fixture),image_sha256=hash_text(json.dumps(c.image)),
                complete_boot_plus_frame_instructions=boot_frame,rows=observations,
                missing_rows_fallback=[60,60],changed_pacing_is_nonadmitted_fixture=True,
                production_boot_drain_not_bruteforced=True)


def production_boot_prefix(isa,c,b,Ports):
    m=isa.Machine(c,poison=isa.WORD_MASK);p=Ports(c);m.enter("boot")
    while not m.io_counts["cpu_count"] and m.steps<b["boot_active_upper"]+100:
        need(m.step(p),"Production boot prefix blocked")
    k=c.constants
    need(m.io_counts["cpu_count"]==1 and m.W[k["ENTRY"]]==k["ENTRY_FRAMES"]
         and m.W[k["PLANT_ENTRY"]]==k["PLANT_ENTRY_FRAMES"]
         and m.W[k["VECTOR_CURSOR"]]==0 and p.world_latch==(60,60),
         "Production initialization before drain differs")
    need(m.io_counts["send_command"]==k["DEGREE"] and m.io_counts["source_invalidate"]==1,
         "Production boot omitted actual neutralization/invalidation")
    need(m.C==c.image and not m.code_writes,"Production boot changed its own image")
    return dict(retired_instructions=m.steps,pc=m.pc,full_boot_executed=False,
                cutoff="First actual cpu_count return, before the long drain loop",
                initialized_cursor=0,neutral_command_count=m.io_counts["send_command"])


def production_frame(isa,c,b,Ports):
    k=c.constants;p=Ports(c);fill_rows(c,p);m=initialized(isa,c)
    for target in range(k["MAINT_BATCH"]):
        p.set_view(target,isa.populated_view(c,0,6));fill_permission(c,p,target)
        base=k["TARGET_BASE"]+target*k["TARGET_WORDS"]
        m.W[base+k["STAGE_ID"]]=7
    m.enter("frame")
    need(m.run(p,budget=b["padded_frame_upper"]+100)=="yield","Production frame did not yield")
    need(m.steps>=k["FRAME_STEPS"] and m.steps<=b["padded_frame_upper"],"Production padding bound failed")
    need(p.world_latch==(50,80) and p.field_offers==7 and m.W[k["MAINT_CURSOR"]]==k["MAINT_BATCH"],"Full production frame effects differ")
    need(m.C==c.image and not m.code_writes,"Production nominal image changed")
    return dict(retired_instructions=m.steps,actual_world=list(p.world_latch),field_offers=p.field_offers,
                helper_visits=k["MAINT_BATCH"],io_counts=dict(sorted(m.io_counts.items())),
                full_padded_frame_executed=True,initial_state_scope="Initialized private frame fixture; production boot loop separately bounded, not executed")


def generate(include_production=True):
    isa=load_isa();d=production_design(isa);c=compile_program(isa,d);b=bounds(isa,c);Ports=ports_class(isa)
    need(b["padded_frame_upper"]<2**64 and b["boot_padded_upper"]<2**64,"Counter proof needs a larger width")
    print("checking local helpers and guards",flush=True)
    local=local_checks(isa,c,b,Ports)
    scanner=scanner_checks(isa,c,b,Ports)
    fixtures=fixture_frames(isa,d,Ports)
    boot_prefix=production_boot_prefix(isa,c,b,Ports)
    actual=None
    if include_production:
        print("executing complete production paced frame",flush=True)
        actual=production_frame(isa,c,b,Ports)
    files=("threshold_program_source.py","threshold_program_model.py","THRESHOLD-PROGRAM.md")
    return dict(scope="candidate complete ordinary controller; source admission and recurrent proof remain open",
                status="instruction-level implementation with bounded checks; no RP completion claim",
                base=BASE,frozen_isa_sha256=isa.source_hash,
                source_design_input=dict(path=PREFIX+"geometry_results.json",sha256=hash_text(frozen("geometry_results.json")),consumer="finite design data only; no prior global winning predicate imported"),
                sources_sha256_lf={f:digest(HERE/f) for f in files},python_version=sys.version,
                production_design=asdict(d),production_image_sha256=hash_text(json.dumps(c.image)),
                code_cells=len(c.nodes),registers=c.next_register,working_words=c.constants["DATA_WORDS"],
                forbidden_nominal_primitives=sorted(FORBIDDEN),nominal_self_code_writes=False,
                actual_row_geometry=["x","x+y"],origins=15,quorum=8,bodies_per_bank=1,
                vector_updates_per_frame=7,vector_slots_per_bank=c.constants["VECTOR_SLOTS"],
                bounds=b,local_checks=local,scanner=scanner,fixture_frames=fixtures,
                production_frame=actual,production_boot_prefix=boot_prefix,production_boot_fully_executed=False,
                production_boot_evidence="Actual production initialization through first counter read; complete boot in separately hashed short-drain fixture; production counter/loop bound from frozen compiler discipline",
                new_field_IO_price="open physical supplier; unit VM instrumentation is not a work price",
                open_suppliers=["source-compatible fifteen-origin incidence and row acquisition",
                    "actual full open-contact dwell before threshold cutoff",
                    "source-local field delivery/hold and all-emitter formation",
                    "complete timing/age/withdrawal and work/resource/thermal rebinding",
                    "guarded access, interrupted-state recovery and relative retirement",
                    "flow/event/source map and all-history mission closure"],
                baseline_global_winning_imported=False,program_completion=False)


def main():
    p=argparse.ArgumentParser();g=p.add_mutually_exclusive_group(required=True)
    g.add_argument("--write",action="store_true");g.add_argument("--check",action="store_true");g.add_argument("--quick",action="store_true")
    a=p.parse_args()
    # JSON is the evidence boundary: tuple-valued design constants become arrays.
    result=json.loads(json.dumps(generate(not a.quick)))
    path=HERE/"threshold_program_results.json"
    if a.write:path.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n",encoding="utf-8",newline="\n")
    elif a.check:need(json.loads(path.read_text(encoding="utf-8"))==result,"Threshold program record differs")
    print("PASS candidate threshold program "+("quick development checks; full production frame omitted" if a.quick else "bound instruction evidence; physical/recurrent suppliers remain open"))


if __name__=="__main__":main()

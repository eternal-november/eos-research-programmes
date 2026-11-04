"""Prospective barrier-capacity inference and compiled finite fold.

The circuit cutset, actual residual-current bound, and actuation are separate
source duties. This checker never substitutes measured current for capacity.
"""
from __future__ import annotations
import argparse
import ast
from dataclasses import replace
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations, product
import json
from pathlib import Path
import sys
import program_model as pm
import geometry_model as gm

HERE=Path(__file__).resolve().parent
if sys.flags.optimize:
    raise RuntimeError('Unoptimized Python required')

def require(ok,message):
    if not ok: raise AssertionError(message)

def serial(x):
    if isinstance(x,F):return str(x)
    if isinstance(x,dict):return {k:serial(v) for k,v in x.items()}
    if isinstance(x,(tuple,list)):return [serial(v) for v in x]
    return x

def source_hash(name):
    return sha256((HERE/name).read_text(encoding='utf-8-sig').replace('\r\n','\n').encode()).hexdigest()

def composed_source():
    base=(HERE/'program_source.py').read_text(encoding='utf-8-sig')
    replacement=(HERE/'conduit_program_source.py').read_text(encoding='utf-8-sig')
    base_tree=ast.parse(base);extra=ast.parse(replacement)
    functions=[node for node in extra.body if isinstance(node,ast.FunctionDef)]
    require(len(functions)==1 and functions[0].name=='publish_fast','Unreviewed source replacement')
    old=[node for node in base_tree.body if isinstance(node,ast.FunctionDef) and node.name=='publish_fast']
    require(len(old)==1,'Base function ambiguous')
    lines=base.splitlines(keepends=True)
    text=''.join(lines[:old[0].lineno-1])+ast.get_source_segment(replacement,functions[0])+'\n\n'+''.join(lines[old[0].end_lineno:])
    return text

class TextSource:
    def __init__(self,text): self.text=text
    def read_text(self,**_): return self.text

class BarrierPorts(pm.RawPorts):
    def __init__(self,compiled):
        super().__init__(compiled)
        # Actual new source scratch; ten words still fit the paid sixteen.
        self.I.extend([0,0])
        self.conversion_delay=F(1,64)

def compile_adapter(fast_batch=24):
    design=replace(gm.design(),fast_batch=fast_batch,connectors_a=66,connectors_b=66)
    old_source=pm.SOURCE
    try:
        pm.SOURCE=TextSource(composed_source())
        compiled=pm.compile_check(design)
    finally:
        pm.SOURCE=old_source
    return compiled

def prospective_theorem_checks():
    count=0
    # Different sample times are represented by independent actual increments.
    # A failed barrier may have any sampled value, then arbitrary final effect.
    for reported in product((F(0),F(1,100),F(1,2),F(3,2)),repeat=3):
        for faulty in (-1,0,1,2):
            median=sorted(reported)[1]
            selected=sorted(range(3),key=lambda i:reported[i])[:2]
            good=[i for i in selected if i!=faulty]
            require(good,'The selected two contain no surviving barrier')
            for dt0,dt1,dt2 in product((F(0),F(1),F(20)),repeat=3):
                dt=(dt0,dt1,dt2)
                error=F(1,200);rate=F(33,800000)
                actual={i:reported[i]+error+rate*dt[i] for i in range(3) if i!=faulty}
                # Series flow upper bound is only assumed at the explicit
                # circuit cutset interface; no such premise is inferred here.
                surviving_bound=min(actual.values())
                upper=median+error+rate*max(dt)
                require(surviving_bound<=upper,'Order-statistic continuation failed')
                count+=1
    # With one jammed-high member, two nominal low members supply availability.
    for bad,high in product(range(3),(0,10,1000,3000)):
        values=[5,5,5];values[bad]=high
        require(sorted(values)[1]<=5,'Jammed-high availability failed')
    # A series-only architecture cannot provide reconnection after stuck closed.
    conductances=[1,0,1]
    require(min(conductances)==0,'Series reconnection obstruction absent')
    # Two disjoint paths guarantee one all-good path for one defective site.
    for bad in range(6):
        good_paths=[p for p in range(2) if bad not in range(3*p,3*p+3)]
        require(len(good_paths)==1,'Parallel service supplier lost')
    # Pointwise one-failure occupancy permits two different mechanisms to
    # falsify the two low witnesses during the window. The union premise is
    # stronger, and release does not restore the formerly failed state.
    mobile_samples=[0,0,1]
    mobile_final=[1,1,1]
    require(sorted(mobile_samples)[1]<min(mobile_final),'Mobile-fault countercase missing')
    return dict(cases=count, samples_need_not_be_simultaneous=True,
                physical_faults_over_whole_window=1, series_members_per_path=3,
                parallel_paths=2, actual_residual_cut_current_bound_not_supplied=True,
                series_only_reconnection_counterexample=conductances,
                pointwise_only_fault_counterexample=dict(samples=mobile_samples,final=mobile_final,
                                                        distinct_failed_members=[0,1]))

def run_fold(compiled,kind,values,missing=(),interleave=True):
    k=compiled.constants
    machine=pm.Machine(compiled,poison=0)
    ports=BarrierPorts(compiled)
    group_start=k['VIEW_WORDS']+(0 if kind==0 else k['CONNECTORS_A']+k['CONNECTORS_B'])
    machine.W[k['FAST_CURSOR']]=group_start
    for member,value in enumerate(values):
        raw=k['SENSE_BIAS']+(value if kind==0 else 1000-value)
        if member not in missing:
            ports.functional[(0,0,member,kind)]=raw
    wanted=3+k['VIEW_WORDS']+(0 if kind==0 else 2)
    # Three bounded invocations cover all66 members at FAST_BATCH24. The last
    # invocation also begins the next side; inspect the actual emitted value.
    for iteration in range(3):
        machine.enter('publish_fast',())
        machine.run(ports,until_yield=False)
        if interleave:
            before=ports.I[6:10]
            # Actual source query operation uses I0..I5; exercise its code.
            machine.enter('publish_queries',())
            machine.run(ports,until_yield=False)
            require(ports.I[6:10]==before,'Query work overwrote median scratch')
    outputs=[value for op,args,value in ports.publications if op=='source_offer_fast' and args[1]==wanted]
    require(outputs,'Actual source emitted no finished group')
    require(len(set(outputs))==1,'Different consumers got different group values')
    return outputs[0]

def compiler_checks():
    compiled=compile_adapter()
    bounds=pm.WorkBound(compiled).report()
    require(bounds['source_I_scratch_words']==8,'Base scratch metadata changed')
    bounds['source_I_scratch_words']=10
    bounds['scratch_metadata_adapter']='Base fixed eight-word annotation replaced by actual ten-word BarrierPorts array; the stored source uses I0..I9'
    timing=pm.processing_certificate(compiled,bounds)
    k=compiled.constants
    require(len(compiled.nodes)<8192,'Expanded source no longer fits actual image')
    require(k['RAW_TARGET_HEADS']==k['VIEW_WORDS']+264,'Raw member inventory wrong')
    require(10*pm.WORD_BITS<=4096,'Retained scratch exceeds paid source capacity')
    horizon=F(timing['functional_guard_horizon'])
    # Both path samples contribute error5/1000; the public guard still pays.01.
    load_needed=F(1,100)+horizon/F(10000)+F(1,5)
    iso_needed=F(1,100)+F(11,400000)*horizon+F(1,10)
    require(load_needed<F(1,2) and iso_needed<F(9,50),'Prospective guard does not fit')
    samples=[]
    for kind in (0,1):
        for bad_location,bad_value in product((0,1,2,3,4,5,65),(0,3000 if kind==0 else 1000)):
            vals=[5]*66;vals[bad_location]=bad_value
            observed=run_fold(compiled,kind,vals)
            require(observed==10,'Median/pathsum/max result wrong')
            samples.append(dict(kind=kind,bad_location=bad_location,bad_value=bad_value,result=observed))
        vals=[5]*66
        observed=run_fold(compiled,kind,vals,missing=(65,))
        require(observed==10,'A missing single barrier erased valid path evidence')
        samples.append(dict(kind=kind,missing=[65],result=observed))
    # Two bad/unknown members in one triplet violate the physical support;
    # they can manufacture an unjustifiably small median. Keep the witness.
    unsafe=[0,0,1500]+[5]*63
    unsafe_result=run_fold(compiled,0,unsafe,interleave=False)
    require(unsafe_result==10,'Two-fault false pass witness changed')
    return dict(image_sha256=sha256(b''.join(x.to_bytes(24,'little') for x in compiled.image)).hexdigest(),
                code_cells=len(compiled.nodes),raw_members_per_side=66,
                functional_physical_heads_per_target=264,source_scratch_words=10,
                private_words=compiled.next_register+k['DATA_WORDS'],
                fast_batch=compiled.design.fast_batch,work=bounds,timing=timing,
                load_margin_needed=load_needed,isolation_margin_needed=iso_needed,
                executed_folds=samples,two_fault_unsupported_case=unsafe_result)

def main():
    parser=argparse.ArgumentParser()
    group=parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--write',action='store_true');group.add_argument('--check',action='store_true')
    args=parser.parse_args()
    names=('BARRIERS.md','barrier_model.py','conduit_program_source.py','program_source.py',
           'program_model.py','geometry_model.py')
    sources={name:source_hash(name) for name in names}
    result=serial(dict(status='prospective-capacity theorem and compiled adapter; physical source incomplete',
                       sources=sources,theorem=prospective_theorem_checks(),compiler=compiler_checks()))
    require(sources=={name:source_hash(name) for name in names},'Source changed during verification')
    path=HERE/'barrier_results.json'
    if args.write:path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n',encoding='utf-8')
    else:require(json.loads(path.read_text())==result,'Evidence differs; inspect before rewriting')
    print(json.dumps({'status':'passed','code_cells':result['compiler']['code_cells'],
                      'horizon':result['compiler']['timing']['functional_guard_horizon'],
                      'physical_source_admitted':False}))

if __name__=='__main__':main()

"""Exact reuse check for certified-watermark progress, not source admission."""
from fractions import Fraction as Q
from math import ceil
from pathlib import Path
from hashlib import sha256
import argparse
import ast
import copy
import json
import subprocess
import sys
import types

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[2]
PREFIX='theories-and-designs/byzantine-control/'
A='fb85a7606f45e52d0cd48e023ab9776dd526640c'
B='57e475c82d13267161f617ebf240791e89e152d3'


def need(ok,message):
    if not ok:raise ValueError(message)


def exact(x):
    need(type(x) in (int,Q),'Exact int/Fraction required')
    return Q(x)


def frozen(commit,name):
    return subprocess.check_output(['git','show',commit+':'+PREFIX+name],cwd=REPO).decode('utf-8-sig').replace('\r\n','\n')


def digest(text):return sha256(text.encode('utf-8')).hexdigest()


def budget(span,step,window):
    need(type(step) is int and step>0,'Positive integer source watermark quantum required')
    span,window=map(exact,(span,window))
    need(span>=0 and window>=0,'Invalid watermark budget')
    bins=ceil(span/step)+1
    return dict(span=span,step=step,possible_bins=bins,window=window,allocation=bins*window)


def functions(text):
    return {n.name:n for n in ast.parse(text).body if isinstance(n,ast.FunctionDef)}


def field_names(node):
    return {n.id for n in ast.walk(node) if isinstance(n,ast.Name)}


class ForgetRetiredQueryState(ast.NodeTransformer):
    def visit_Expr(self,node):
        if isinstance(node.value,ast.Call) and isinstance(node.value.func,ast.Name) and node.value.func.id=='clear_target':return None
        return self.generic_visit(node)
    def visit_Assign(self,node):
        if any(isinstance(t,ast.Subscript) and 'PENDING' in field_names(t.slice) for t in node.targets):return None
        return self.generic_visit(node)


def watermark_node(helper):
    for i,node in enumerate(helper.body):
        if (isinstance(node,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='rank' for t in node.targets)
            and isinstance(node.value,ast.Call) and isinstance(node.value.func,ast.Name)
            and node.value.func.id=='progress'):
            block=helper.body[i+1]
            need(isinstance(block,ast.If),'No literal watermark branch')
            return block,helper.body[i+2:i+4]
    raise ValueError('Actual helper watermark not found')


def source_binding(a_text,b_text):
    af=functions(a_text);bf=functions(b_text)
    original,a_after=watermark_node(af['helper']);changed,b_after=watermark_node(bf['helper'])
    lowered=ForgetRetiredQueryState().visit(copy.deepcopy(original))
    need(ast.dump(lowered,include_attributes=False)==ast.dump(changed,include_attributes=False),
         'The actual old/new watermark rule is not shared')
    need(ast.dump(ast.Module(body=a_after,type_ignores=[]),include_attributes=False)==
         ast.dump(ast.Module(body=b_after,type_ignores=[]),include_attributes=False),
         'Timer expiry/abort issuance differs')
    touched=set()
    for n in ast.walk(af['clear_target']):
        if isinstance(n,ast.Assign):
            for t in n.targets:
                if isinstance(t,ast.Subscript):touched|=field_names(t.slice)-{'base','j'}
    protected={'TIMER','HIGH','RANK_VALID','WATCH_HALF','LAST_PHASE','ABORT'}
    need(not touched&protected,'Removed query reset touched watermark/abort state')
    same=[]
    for name in ('progress','read_view','count_fast','count_range','estimate'):
        need(ast.dump(af[name],include_attributes=False)==ast.dump(bf[name],include_attributes=False),
             'A claimed shared source function changed: '+name)
        same.append(name)
    # The literal expressions, not a renamed high-level rule, carry the bounds.
    rendered=ast.unparse(changed)
    need('rank - PROGRESS_ERROR > w[base + HIGH] + HIGH_STEP' in rendered
         and 'w[base + HIGH] = rank + PROGRESS_ERROR' in rendered,
         'Actual certified upper/lower updates differ')
    return dict(shared_functions=same,shared_watermark_ast_sha256=digest(ast.dump(changed,include_attributes=False)),
        excluded_query_reset_fields=sorted(touched|{'PENDING'}),
        timer_expiry_and_abort_spine_same=True,
        scope='literal source rule and explicit state projection; not a new compiler/physical theorem')


def module_from(text,name):
    module=types.ModuleType(name);module.__file__=str(HERE/(name+'.py'))
    sys.modules[name]=module
    exec(compile(text,module.__file__,'exec'),module.__dict__)
    return module


def layouts_and_cadence(a_text,b_text,a_record,b_record,isa_text,threshold_text):
    isa=module_from(isa_text,'_watermark_frozen_isa')
    threshold=module_from(threshold_text,'_watermark_threshold_supplier')
    a_design=dict(a_record['design']);b_design=dict(b_record['changed_design'])
    for design in (a_design,b_design):design['physical_parameters']=tuple(map(tuple,design['physical_parameters']))
    old=isa.Design(**a_design).constants()
    new=threshold.design_class(isa)(**b_design).constants()
    protected_names={'TIMER','HIGH','RANK_VALID','WATCH_HALF','LAST_PHASE','ABORT','VIEW_VALID',
                     'CMD_MODE','CMD_CAM','CMD_ACTION','CMD_SIDE','CMD_INDEX','CMD_AMPLITUDE','CMD_ROUTE'}
    removed_names={'CURSOR','COMPLETED','JOINED','SCAN_BAY','SCAN_ADDRESS','SCAN_MATCH',
                   'SELECTED','VERIFY_ADDRESS','PENDING'}
    removed={old[name] for name in removed_names}|set(range(old['ACCEPTED'],old['ACCEPTED']+old['BAYS']))
    protected_old={old[name] for name in protected_names}
    protected_new={new[name] for name in protected_names}
    deleted_addresses={old['TARGET_BASE']+t*old['TARGET_WORDS']+i
                       for t in range(old['DEGREE']) for i in removed}
    protected_addresses={old['TARGET_BASE']+t*old['TARGET_WORDS']+i
                         for t in range(old['DEGREE']) for i in protected_old}
    need(deleted_addresses.isdisjoint(protected_addresses),'Numeric query/control alias')
    need(all(0<=x<old['DATA_WORDS'] for x in deleted_addresses|protected_addresses),
         'Projected old state escapes its physical private array')
    need(all(0<=i<new['TARGET_WORDS'] for i in protected_new),'New control state escapes target stride')
    profile={}
    for label,source,c,record in (('primary',a_text,old,a_record),('threshold',b_text,new,b_record)):
        frame=functions(source)['frame']
        helper_sites=[i for i,n in enumerate(frame.body) if any(isinstance(x,ast.Call)
            and isinstance(x.func,ast.Name) and x.func.id=='helper' for x in ast.walk(n))]
        decrement_sites=[i for i,n in enumerate(frame.body) if any(isinstance(x,ast.AugAssign)
            and isinstance(x.target,ast.Subscript) and 'TIMER' in field_names(x.target.slice)
            and isinstance(x.op,ast.Sub) and isinstance(x.value,ast.Constant) and x.value.value==1
            for x in ast.walk(n))]
        need(len(helper_sites)==len(decrement_sites)==1 and helper_sites[0]<decrement_sites[0],
             'Literal timer decrement is not after helper visits')
        visits=ast.unparse(frame.body[helper_sites[0]])
        decrements=ast.unparse(frame.body[decrement_sites[0]])
        need('while visits < MAINT_BATCH:' in visits and 'helper(target)' in visits
             and 'w[MAINT_CURSOR] = (target + 1) % DEGREE' in visits and 'visits += 1' in visits,
             'Actual fixed cyclic target visitation changed')
        need('while target < DEGREE:' in decrements and 'if w[base + TIMER] > 0:' in decrements
             and 'w[base + TIMER] -= 1' in decrements and 'target += 1' in decrements,
             'Actual saturating per-frame timer decrement changed')
        degree=c['DEGREE'];batch=c['MAINT_BATCH'];watch=c['WATCH_FRAMES']
        need(type(degree) is int and type(batch) is int and degree>0 and batch>0 and degree%batch==0,
             'Uniform visit cadence not supplied')
        period=degree//batch
        need(watch%period==0,'One post-refresh callback bound needs timeout/cadence alignment')
        residues=[(-residue)%period for residue in range(period)]
        if label=='primary':
            time=record['timing'];calc=record['compiler']['processing_certificate']
            F=Q(calc['frame_max']);T=Q(time['latest_timeout']);J=Q(calc['per_target_response'])
            form=Q(time['formation']);window=Q(time['timer_window'])
        else:
            time=record['arithmetic'];F=Q(time['frames']['max']);T=Q(time['watchdog']['latest'])
            J=Q(time['polling']);form=Q(time['recognition_allocation']);window=Q(time['watchdog']['complete_timer_job'])
        need(T==(watch+1)*F and J==(period+1)*F,'Frame/callback consumer differs')
        need(window>=form+2*T+J+40,'Complete timer window omits the one initial callback allowance')
        profile[label]=dict(degree=degree,batch=batch,visit_period_frames=period,watch=watch,
            timer_reset_to_expiry_visit_frames=watch,initial_callback_residues=residues,
            maximum_initial_extra_frames=max(residues),frame_max=F,aligned_timeout=T,
            initial_callback_bound=J,formation=form,complete_job=window,
            bound_uses_only_one_unaligned_initial_callback=True)
    small_watch=101;small_period=10;remaining=small_watch;observed=None
    for frame in range(111):
        if frame>0 and frame%small_period==0 and remaining==0:
            observed=frame;break
        if remaining>0:remaining-=1
    need(observed==110>small_watch+1,'Nonaligned callback countercase disappeared')
    return dict(nondivisible_timeout_countercase=dict(watch=small_watch,visit_period=small_period,
        first_expiry_invocation_frame=observed,insufficient_scalar_upper_frames=small_watch+1,
        scope='local frame/timer interface countercase, not a whole admitted family'),
        old_target_stride=old['TARGET_WORDS'],new_target_stride=new['TARGET_WORDS'],
        old_protected_offsets=sorted(protected_old),new_protected_offsets=sorted(protected_new),
        old_deleted_query_offsets=sorted(removed),checked_target_count=old['DEGREE'],
        cross_target_addresses_disjoint=True,cadence=profile)


def algebra_checks(step,error):
    need(type(step) is int and step>0 and type(error) is int and error>=0,'Invalid integer profile')
    cases=0
    # Endpoint/interior probes for the interval proof; Lean supplies the
    # arbitrary-integer implication. These are not whole-source trajectories.
    for left in (0,step,2*step):
        for before in (left,left+step//2,left+step):
            for after in (left,left+step//2,left+step):
                for old_noise in (-error,0,error):
                    for new_noise in (-error,0,error):
                        old=before+old_noise;new=after+new_noise
                        high=old+error;low=new-error
                        need(not(high+step<low),'Two certified refreshes fit one bin')
                        cases+=1
    # Full parameter-scale countercase to dropping the certified upper mark.
    left=2*step+2*error
    before=left;after=left+step-error+1
    need(0<error<step and before<=after<left+step,'Countercase requires this profile')
    old_sample=before-error;new_sample=after+error
    need(new_sample-error>old_sample+step,'Uncertified upper-mark countercase missing')
    need(not(new_sample-error>old_sample+error+step),'Certified mark accepted a same-bin refresh')
    # One late valid grounding/refresh can restart a nearly expired timer.
    T=Q(2400000000);epsilon=Q(1)
    restart=T-epsilon;expiration=restart+T
    need(expiration>T and expiration<2*T,'One-time timer restart was lost')
    rejected=0
    for args in ((-1,step,1),(1,0,1),(1,True,1),(1,step,0.1),(1,step,-1),(1,Q(step),1)):
        try:budget(*args)
        except ValueError:rejected+=1
        else:raise ValueError('Invalid budget admitted')
    return dict(endpoint_cases=cases,typed_rejections=rejected,
        weaker_mark_countercase=dict(bin_left=left,bin_right=left+step,rank_before=before,rank_after=after,
            old_sample=old_sample,new_sample=new_sample,uncertified_mark=old_sample,correct_mark=old_sample+error,
            scope='counterexample to the generic error-only interface; not asserted as a full source history'),
        one_timer_countercase=dict(initial_remaining=T,late_restart=restart,expiration=expiration,
            scope='conditional timer interface: one late restart; physical sample history remains a supplier'))


def normalize(value):
    if isinstance(value,Q):return str(value)
    if isinstance(value,dict):return {k:normalize(v) for k,v in value.items()}
    if isinstance(value,(list,tuple)):return [normalize(v) for v in value]
    return value


def generate():
    need(sys.version_info[:2]==(3,12) and not sys.flags.optimize,'Unoptimized Python3.12 required')
    inputs={A+':local-control/program_source.py':frozen(A,'local-control/program_source.py'),
        B+':portability/threshold_program_source.py':frozen(B,'portability/threshold_program_source.py'),
        A+':local-control/geometry_results.json':frozen(A,'local-control/geometry_results.json'),
        B+':portability/threshold_geometry_results.json':frozen(B,'portability/threshold_geometry_results.json'),
        A+':local-control/CYCLE.md':frozen(A,'local-control/CYCLE.md'),
        A+':local-control/GEOMETRY.md':frozen(A,'local-control/GEOMETRY.md'),
        A+':local-control/program_model.py':frozen(A,'local-control/program_model.py'),
        B+':portability/threshold_program_model.py':frozen(B,'portability/threshold_program_model.py')}
    binding=source_binding(inputs[A+':local-control/program_source.py'],inputs[B+':portability/threshold_program_source.py'])
    a_record=json.loads(inputs[A+':local-control/geometry_results.json'])
    b_record=json.loads(inputs[B+':portability/threshold_geometry_results.json'])
    ar=a_record['timing'];br=b_record['arithmetic']
    a_params=dict(a_record['design']['physical_parameters'])
    b_params=dict(b_record['changed_design']['physical_parameters'])
    need(len(a_params)==len(a_record['design']['physical_parameters'])
         and len(b_params)==len(b_record['changed_design']['physical_parameters']),
         'Duplicate physical parameter binding')
    layout=layouts_and_cadence(inputs[A+':local-control/program_source.py'],
        inputs[B+':portability/threshold_program_source.py'],a_record,b_record,
        inputs[A+':local-control/program_model.py'],inputs[B+':portability/threshold_program_model.py'])
    step=a_params['HIGH_STEP'];error=a_params['PROGRESS_ERROR']
    need((step,error)==(b_params['HIGH_STEP'],b_params['PROGRESS_ERROR'])
         ==(br['watchdog']['rank_quantum'],br['watchdog']['rank_error']),
         'Actual old/new watermark parameter bindings differ')
    need(a_record['compiler']['processing_certificate']['high_water_step']==step,
         'Frozen processing certificate uses another quantum')
    rows={}
    for family,record,spans_key,window_key,bounds_key in (
        ('frozen_primary_geometry',ar,'rank_spans','timer_window','partial_stall_bounds'),
        ('changed_threshold_geometry',br,'rank_spans','watchdog','partial_stall_allocations')):
        window=Q(record[window_key] if family.startswith('frozen') else record[window_key]['complete_timer_job'])
        spans=record[spans_key];observed=record[bounds_key]
        profiles=[]
        for key,value in (spans.items() if isinstance(spans,dict) else enumerate(spans)):
            phase=int(key)
            if phase==4:continue
            item=budget(Q(value),step,window)
            actual=observed[str(phase)] if isinstance(observed,dict) else observed[phase]
            need(item['allocation']==Q(actual),'Existing phase consumer differs: '+family+'/'+str(phase))
            profiles.append(dict(phase=phase,**item))
        need(len(profiles)==12,'A physical-direct phase was counted as a watchdog phase')
        rows[family]=profiles
    names=('WATCHDOG-PROGRESS.md','watchdog_progress.py','WatchdogProgress.lean')
    return normalize(dict(scope='reused conditional watermark/bin kernel, literal source binding and exact phase allocations',
        source_rule=binding,actual_layout_and_cadence=layout,parameters=dict(step=step,error=error),profiles=rows,
        checks=algebra_checks(step,error),python_version=sys.version,
        sources_sha256_lf={name:digest((HERE/name).read_text(encoding='utf-8').replace('\r\n','\n')) for name in names},
        immutable_inputs_sha256_lf={name:digest(text) for name,text in inputs.items()},
        phase4_requires_direct_physical_progress=True,
        source_premises=['certified lower/upper rank observations and no signed-word overflow',
            'actual stable-phase/entry handling, no new private corruption or incarnation change inside the selected job',
            'monotone physical rank or a separately proved no-bin-reentry law',
            'actual whole-job bank interval, scheduled calls, clock bounds and compatible abort application'],
        remaining=['full source-to-phase realization and interrupted-entry itinerary',
                   'shared initialized global recurrence/retirement/time closure and both positive families'],
        independent_review_pending=False,
        independent_review_scope='bounded algebra/floor/source projection/cadence review; numeric aliases and cadence bindings repaired',
        formal_kernel=dict(toolchain='Lean4.33.0',checked_declarations=5,
            observed_axioms=['propext','Quot.sound'],physical_or_global_closure_proved=False),
        program_completion=False))


def main():
    ap=argparse.ArgumentParser(description=__doc__);g=ap.add_mutually_exclusive_group(required=True)
    g.add_argument('--write',action='store_true');g.add_argument('--check',action='store_true');args=ap.parse_args()
    result=generate();path=HERE/'watchdog_progress_results.json'
    if args.write:path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n',encoding='utf-8',newline='\n')
    else:need(json.loads(path.read_text(encoding='utf-8'))==result,'Watermark record differs')
    print('PASS shared watermark source rule and conditional phase allocations; global source closure remains open')


if __name__=='__main__':main()

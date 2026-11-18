"""Interrupted renewal itinerary bookkeeping against the actual threshold image.

The finite phase paths and compiled probes do not supply their physical
progress, writer custody, input truth or same-history compatibility premises.
"""
from fractions import Fraction as Q
from pathlib import Path
import argparse
import json
import sys
import subprocess
import threshold_program_model as program
import threshold_design as design

HERE=Path(__file__).resolve().parent
BASE='ffe23ea603afe863a2bcf82a2f1f365e3797c423'
need=program.need


def frozen(commit,name):
    return subprocess.check_output(['git','show',commit+':theories-and-designs/byzantine-control/'+name],
        cwd=HERE.parents[2]).decode('utf-8-sig').replace('\r\n','\n')


def normalize(x):
    if isinstance(x,Q):return str(x)
    if isinstance(x,dict):return {str(k):normalize(v) for k,v in x.items()}
    if isinstance(x,(tuple,list)):return [normalize(v) for v in x]
    return x


def successor(half,phase,n):
    if not(type(half) is int and half in (0,1) and type(phase) is int and 0<=phase<n):
        raise ValueError('Invalid physical half/phase index')
    return (half,phase+1) if phase+1<n else (1-half,0)


def clearing_visits(half,phase,n):
    """Normal succession until completion of a full fresh phase4 sweep.

    Entry inside4 is contaminated and cannot serve as that full sweep.
    Abort branches are represented separately, not silently skipped here.
    """
    visits=[];initial=True
    while True:
        fresh=phase==4 and not initial
        visits.append(dict(half=half,phase=phase,full_fresh_clear=fresh))
        if fresh:return visits
        half,phase=successor(half,phase,n);initial=False
        need(len(visits)<=n+1,'Normal phase succession did not reach fresh clearing')


def compiled_probes(isa,c,b):
    k=c.constants;Ports=program.ports_class(isa);out=[]
    for half in (0,1):
        ports=Ports(c);m,view=program.helper_fixture(isa,c,ports,half,6)
        cold=1-half;view[k['CLAMP_A']+cold]=499999999
        view[k['CLAMP_OPEN_A']+cold]=0;ports.set_view(0,view)
        m=program.call(isa,c,ports,'helper',(0,),b['instruction_upper_bounds']['helper']+100,m)
        command=next(e for e in reversed(ports.events) if e[0]=='command')
        need(list(command[2:])==[13*half+6,cold,k['FORCE'],0,k['CLAMP_PORT'],0,k['FORCE']]
             and m.W[k['TARGET_BASE']+k['ABORT']]==0,
             'Near-cutoff source call unexpectedly forces immediate abort')
        out.append(dict(half=half,phase=6,actual_clamp=499999999,
            instructions=m.steps,command=list(command[2:]),private_abort=0,
            scope='actual compiled helper at a bounded observation/private-state fixture; full source reachability not asserted'))
    return out


def generate():
    need(sys.version_info[:2]==(3,12) and not sys.flags.optimize,'Unoptimized Python3.12 required')
    names=('threshold_geometry_results.json','threshold_program_source.py','threshold_program_model.py',
           'threshold_design.py','watchdog_progress_results.json')
    texts={name:frozen(BASE,'portability/'+name) for name in names}
    for name,text in texts.items():
        need(program.digest(HERE/name)==program.hash_text(text),'Itinerary supplier changed: '+name)
    g=json.loads(texts['threshold_geometry_results.json']);a=g['arithmetic']
    isa=program.load_isa();c=program.compile_program(isa,design.design(isa));b=program.bounds(isa,c);k=c.constants
    need(program.hash_text(json.dumps(c.image))==g['changed_image_sha256'] and b==g['bounds'],
         'Itinerary is not bound to the checked changed image')
    need(isa.source_hash==g['frozen_isa_sha256']
         and program.hash_text(program.frozen('geometry_results.json'))==g['frozen_geometry_sha256'],
         'Frozen ISA/design supplier differs from the checked image record')
    n=k['PHASES'];need(n==13 and k['SEGMENT']==32000,'Changed phase grammar')
    stalls={int(i):Q(v) for i,v in a['partial_stall_allocations'].items()}
    # JSON dictionaries are sorted on serialization; recover physical order by
    # each explicit numeric phase prefix rather than dictionary iteration.
    phases=[None]*n
    for name,value in a['phase_bounds'].items():phases[int(name.split('_',1)[0])]=Q(value)
    need(all(v is not None for v in phases),'Incomplete physical phase allocation')
    band=Q(a['band_travel'])/n;extra=phases[4]+band
    old_partial=Q(a['partial_time_allocation']);new_partial=old_partial+extra
    new_sequence=Q(a['complete_sequence_allocation'])+extra
    H=Q(a['candidate_H']);lam=Q(a['raw_rate'])
    need(extra==Q(136934427299,2359296) and new_sequence==Q(59168150925885444623,201326592),
         'Fresh second clearing allocation changed')
    need(new_sequence<H and 1+2+(3+2*lam*H).__floor__()==6,'Repaired itinerary loses horizon/support margin')
    cases=[]
    for half in (0,1):
        for phase in range(n):
            visits=clearing_visits(half,phase,n)
            counts=[sum(v['phase']==j for v in visits) for j in range(n)]
            need(counts[4]==(2 if phase==4 else 1) and all(counts[j]<=1 for j in range(n) if j!=4),
                 'Contaminated entry visits were silently folded together')
            duration=Q(a['recognition_allocation'])+sum(stalls[v['phase']]+band for v in visits)
            need(duration<=new_partial,'A normal contaminated prefix exceeds its explicit allocation')
            terminal_half=visits[-1]['half']
            suffix=list(range(5,n));second=list(range(n))
            suffix_time=sum(phases[j]+band for j in suffix+second)
            need(suffix_time<=2*Q(a['fresh_half_time']),'Two target restorations exceed two fresh halves')
            cases.append(dict(initial_half=half,initial_phase=phase,visits=visits,
                conditional_prefix_bound=duration,phase4_visit_count=counts[4],
                fresh_suffix_targets=[1-terminal_half,terminal_half],
                fresh_suffix_phases=[suffix,second],conditional_fresh_suffix_bound=suffix_time))
    need(max(len(x['visits']) for x in cases)==14,'Missing second phase4 visit')
    malformed=0
    for half,phase in ((True,0),(0,True),(-1,0),(2,0),(0,-1),(0,13)):
        try:successor(half,phase,n)
        except ValueError:malformed+=1
        else:raise ValueError('Malformed source phase accepted')
    return normalize(dict(scope='derived finite interrupted-entry itinerary and conditional phase budget; no achieved-return theorem',
        base=BASE,python_version=sys.version,actual_image_sha256=g['changed_image_sha256'],
        frozen_ISA_sha256=isa.source_hash,frozen_geometry_sha256=g['frozen_geometry_sha256'],
        physical_phase_count=n,normal_entry_cases=cases,malformed_index_rejections=malformed,
        compiled_near_cutoff_probes=compiled_probes(isa,c,b),
        old_partial_allocation=old_partial,extra_fresh_phase4_and_band=extra,
        corrected_partial_allocation=new_partial,abort_allocation=Q(a['abort_time_allocation']),
        fresh_half_allocation=Q(a['fresh_half_time']),old_effect_suffix=Q(a['old_suffix_allocation']),
        all_role_initialization=Q(a['reconstruction_startup_allocation']),
        corrected_sequence_allocation=new_sequence,H=H,strict_slack=H-new_sequence,raw_cover=6,
        terminal_scope='formed local C/PC/private/parent and retired local outgoing authority, conditional on actual suppliers; remote-origin raw input fibres are separate',
        source_premises=['normal physical phase succession and predecessor zero-entry/stop laws',
            'actual monotone rank or forced abort with whole-job interval and invocation suppliers',
            'full phase4 all-emitter clearing; a partial phase4 or half boundary is insufficient',
            'finite actual abort cleanup/return and EXITING/post-stage handling',
            'fresh cam/field/parent formation, writer exclusion, accepted-child binding and old effect retirement',
            'same-history support, all installed concurrent work and compatible input/field service'],
        unresolved=['complete all-mode A-prime/threshold source maps and physical placements',
            'full source-local TX/ADC field correspondence and temporal sibling publication',
            'fibrewise input-debt closure at origins, not receiver-wide reset',
            'initialized common support/mission/resource/time theorem and positive families'],
        sources_sha256_lf={name:program.digest(HERE/name) for name in ('INTERRUPTED-RENEWAL.md','interrupted_renewal.py')},
        immutable_inputs_sha256_lf={BASE+':portability/'+name:program.hash_text(text) for name,text in texts.items()},
        old_full_paced_frame_reused_only_at_unchanged_image=True,
        full_hybrid_trace=False,source_progress_proved=False,independent_review_pending=False,
        independent_review_scope='all26 entry paths, exact prefix and suffix sums, actual compiled probe tuples, physical/source boundaries and transitive loader repair',program_completion=False))


def main():
    parser=argparse.ArgumentParser(description=__doc__);group=parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--write',action='store_true');group.add_argument('--check',action='store_true');args=parser.parse_args()
    result=generate();path=HERE/'interrupted_renewal_results.json'
    if args.write:path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n',encoding='utf-8',newline='\n')
    else:need(json.loads(path.read_text(encoding='utf-8'))==result,'Interrupted itinerary record differs')
    print('PASS finite interrupted itinerary and compiled boundary probes; source progress remains conditional')


if __name__=='__main__':main()

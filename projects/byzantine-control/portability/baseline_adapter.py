"""Numerical baseline adapter through the new constructors.

This derives the phase/horizon and per-intact-host work joins from frozen local
supplier records. It does not import the old all-history mission as a premise,
and does not certify the still-open rule/retirement/event source maps.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as Q
from hashlib import sha256
import importlib.util
import json
from math import ceil
from pathlib import Path
import sys
from constructors import PhaseEdge, WindowEnvelope, phase_family_budget, check_horizon, reservoir_margin

HERE=Path(__file__).resolve().parent
LOCAL=HERE.parent/'local-control'
spec=importlib.util.spec_from_file_location('_baseline_comparison_loader',LOCAL/'primary_comparison_model.py')
loader=importlib.util.module_from_spec(spec);sys.modules[spec.name]=loader;spec.loader.exec_module(loader)


def need(ok,reason):
    if not ok:raise AssertionError(reason)


def digest(path):return sha256(path.read_bytes().replace(b'\r\n',b'\n')).hexdigest()


def generate():
    source,sb=loader.record_at(loader.SOURCE,'port_source_results.json')
    resources,rb=loader.record_at(loader.RESOURCES,'port_resource_results.json')
    need(resources['bindings']['source']['commit']==loader.SOURCE,'Resource and source bindings differ')
    base=source['base_binding']['commit']
    gtext=loader.text_at(base,'geometry_results.json')
    need(loader.digest(gtext)==source['base_binding']['sources']['geometry_results.json'],'Geometry supplier binding differs')
    geom=json.loads(gtext);gt=geom['timing'];rs=source['return_schedule']
    old_phase={k:Q(v) for k,v in gt['phase_bounds'].items()}
    phase={k:Q(v) for k,v in rs['phase_bounds'].items()}
    clearance=Q(source['mechanical']['clearance_time'])
    for name,cost in old_phase.items():
        expected=cost+clearance if name.startswith(('0_','10_')) else cost
        need(phase[name]==expected,'Changed phase has an unaccounted source substitution: '+name)
    partial=Q(gt['formation'])+sum(map(Q,gt['partial_stall_bounds'].values()))+Q(gt['normal_band_travel'])
    need(partial==Q(gt['partial'])==Q(rs['unchanged_partial_bound']),'Partial rank expansion differs')
    half=sum(phase.values())+Q(gt['normal_band_travel'])
    need(half==Q(rs['half_cycle']),'Half-cycle phase expansion differs')
    abort=Q(gt['abort'])+clearance
    need(abort==Q(rs['abort']),'Abort clearance not counted')
    old=Q(gt['old_suffix']);commission=Q(gt['commissioning'])
    burst=Q(resources['point']['upstream_burst']);rate=Q(resources['point']['upstream_rate'])
    # This work dimension is a uniform debit bound for ONE intact upstream host.
    # It includes that host's complete allowed traffic, not only the current job.
    def edge(a,b,time,dependency):
        return PhaseEdge(a,b,time,burst+rate*time,dependency)
    ranks={'partial':5,'abort':4,'first_half':3,'second_half':2,'old_tail':1,'done':0}
    edges=[edge('partial','abort',partial,'GEOMETRY partial phase/rank and all-emitter map'),
           edge('abort','first_half',abort,'GEOMETRY abort plus bank-local source clearance'),
           edge('first_half','second_half',half,'source phases 0-12 plus cam-band traversal'),
           edge('second_half','old_tail',half,'second fresh half of the same local source phases'),
           edge('old_tail','done',old,'funded old suffix, fixed destinations and receiver age')]
    certificate=phase_family_budget(ranks,frozenset({'done'}),edges,tuple(ranks))
    sequence=partial+abort+2*half+old
    need(certificate.time_bound==sequence,'Entry-family construction missed the largest partial case')
    H=Q(ceil(commission+certificate.time_bound)+1)
    need(H==rs['conditional_return_H'],'Derived H differs from source local supplier point')
    lam=Q(rs['original_raw_acquisition_rate'])
    joined=check_horizon(WindowEnvelope(1,2,Q(3),lam),H,commission,certificate,Q(0),6)
    need(joined.slack==Q(rs['strict_slack']),'Strict age-out margin differs')
    need(5*clearance==Q(rs['actual_extra_total_return']),'Five added clearances not accounted')
    # Resource supplier has supply slope D and a two-quantum outage envelope.
    capacity=Q(resources['point']['new_upstream_capacity'])
    latency=Q(resources['point']['upstream_latency'])
    reserve=reservoir_margin(capacity,burst,rate,rate,latency)
    return dict(scope='quantitative baseline replay; full source-to-core adapter incomplete',
                bindings=dict(source=sb,resources=rb,geometry=dict(commit=base,sha256_lf=loader.digest(gtext))),
                phase_expansion={k:str(v) for k,v in phase.items()},
                macro=dict(partial=str(partial),abort=str(abort),half=str(half),old_tail=str(old),
                           commissioning=str(commission),sequence=str(sequence)),
                entries=list(ranks),H=str(H),raw_lambda=str(lam),cover=joined.support_budget,slack=str(joined.slack),
                per_intact_upstream_host=dict(work_bound=str(certificate.work_bound),burst=str(burst),rate=str(rate),
                                             reserve_margin=str(reserve),failed_funding_boundary_not_covered=True),
                open_source_maps=['rule-local no-spread/frame proof','actual entry-family coverage',
                                  'all-emitter and debt-transport map','retirement-path inventory',
                                  'flow coordinate/event/boundary inventory','local-policy and mission assembly'],
                sources_sha256_lf={name:digest(HERE/name) for name in ('baseline_adapter.py','BASELINE-ADAPTER.md','constructors.py','CONSTRUCTORS.md','CORE.md','FLOW-COMPOSITION.md','RankedJobs.lean','ContextualJobs.lean')},
                helper_sha256_lf=digest(LOCAL/'primary_comparison_model.py'),
                program_completion=False,baseline_global_theorem_used_as_premise=False)


def main():
    p=argparse.ArgumentParser(description=__doc__);g=p.add_mutually_exclusive_group(required=True)
    g.add_argument('--write',action='store_true');g.add_argument('--check',action='store_true');a=p.parse_args()
    result=generate();path=HERE/'baseline_adapter_results.json'
    if a.write:path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n',encoding='utf-8',newline='\n')
    else:need(json.loads(path.read_text(encoding='utf-8'))==result,'Baseline adapter record differs')
    print('PASS quantitative baseline adapter; source/closure obligations remain open')


if __name__=='__main__':main()

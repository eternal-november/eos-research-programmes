"""Frozen numerical protocol runner; keeps every offered case and certificate."""
import json,time,hashlib,statistics,gzip,random,os,gc,copy
from collections import Counter,defaultdict
from dataclasses import replace
from ladder_model import LadderModel,Job
from exact_search import ExactSearch,WIN,LOSE,UNKNOWN
from check_certificate import check_certificate
from workloads import PROTOCOL,RICH_PROTOCOL,all_cases,pair_workload,rich_cases,rich_workload

ROOT=os.path.dirname(os.path.abspath(__file__))
OUT=os.path.join(ROOT,'results')
def stable(x):return json.dumps(x,sort_keys=True,separators=(',',':'))
def dump(path,obj):
    with open(path,'w') as f:json.dump(obj,f,sort_keys=True,indent=2)
def gzip_dump(path,obj):
    with gzip.open(path,'wt') as f:json.dump(obj,f,sort_keys=True,separators=(',',':'))
def world_count(inf,domains):
    states={p:1 for p in inf.pairs(domains,0)}
    for c in range(1,inf.m):
        states={q:sum(v for p,v in states.items() if inf.compatible(p,q,c)) for q in inf.pairs(domains,c)}
    return sum(states.values())

def interface_metrics(model,result):
    totals=Counter(); maxima=Counter()
    for rec in result['certificate'].values():
        s=model.decode_state(rec['state']);sup=model.inf.support(s.domains)
        totals['nodes']+=1
        maxima['worlds_consistent']=max(maxima['worlds_consistent'],world_count(model.inf,s.domains))
        known=sum(not(mask&(mask-1)) for mask in sup)
        totals['identified_parent_coordinates']+=known
        for i in range(model.n):
            prior={0 if p<0 else s.previous[p] for p in model.inf.choices[i]}
            current={0 if p<0 else s.previous[p] for p in model.inf.values(i,sup[i])}
            if len(prior)==1:totals['prior_action_constant_rows']+=1
            elif len(current)==1:totals['additional_evidence_constant_rows']+=1
            else:totals['remaining_nonconstant_rows']+=1
        if rec['kind']=='choice':
            u=rec['action'][0]
            for i in range(model.n):
                if u[i]==2:
                    prior={0 if p<0 else s.previous[p] for p in model.inf.choices[i]}
                    current={0 if p<0 else s.previous[p] for p in model.inf.values(i,sup[i])}
                    if 2 in prior and 2 not in current:totals['productive_rows_safe_only_after_evidence']+=1
    return dict(totals=totals,maxima=maxima)

def replay_all_worlds(model,result):
    if result['status']!=WIN:return None
    cert=result['certificate']; summaries=[];distinct_traces=set();ticks=0
    for world in model.inf.complete_worlds(model.inf.initial()):
        node=result['root'];state=model.initial();prev=(0,)*model.n
        used=0;pulses=0;uncredited=0;stages=0;first_work=None;first_full=None;maxload=0;trace=[]
        while True:
            rec=cert[node]
            assert rec['state']==model.encode_state(state)
            if all(not(d&(d-1)) for d in state.domains) and first_full is None:first_full=state.t
            if rec['kind']=='terminal':
                assert rec['status']==WIN and not any(prev)
                break
            controls,credits=map(tuple,rec['action'])
            load=tuple(controls[i]+(0 if world[i]<0 else prev[world[i]]) for i in range(model.n))
            assert max(load)<=3 and sum(controls)<=model.power
            maxload=max(maxload,max(load));used+=sum(controls);assert used<=model.energy
            credited_nodes=[];progress=[]
            for job,(r,done),credit in zip(model.jobs,state.progress,credits):
                if credit<0:progress.append((r,done));continue
                assert job.release<=state.t<=job.deadline
                assert r<0 or r==credit
                actuator=job.routes[credit][done];assert controls[actuator]==2
                assert actuator not in credited_nodes;credited_nodes.append(actuator)
                progress.append((credit,done+1));stages+=1
            if credited_nodes and first_work is None:first_work=state.t
            pulses+=controls.count(1);uncredited+=controls.count(2)-len(credited_nodes)
            edge=next(e for e in rec['outcomes'] if tuple(e['observation'])==load)
            successor=model.decode_state(cert[edge['next']]['state'])
            assert successor.t==state.t+1 and successor.energy==state.energy-sum(controls)
            assert successor.previous==controls and successor.progress==tuple(progress)
            assert all(successor.domains[i]>>(model.inf.choices[i].index(world[i]))&1 for i in range(model.n))
            trace.append((controls,credits,load));prev=controls;state=successor;node=edge['next'];ticks+=1
        assert stages==sum(len(j.routes[r]) for j,(r,done) in zip(model.jobs,state.progress))
        assert all(done==len(j.routes[r]) for j,(r,done) in zip(model.jobs,state.progress))
        summaries.append(dict(energy=used,pulses=pulses,uncredited_full=uncredited,ticks=state.t,
                              first_work=first_work,first_full_identification=first_full,
                              complete_without_full_identification=first_full is None,
                              work_before_full_identification=first_full is None or first_work<first_full,
                              final_identified=sum(not(d&(d-1)) for d in state.domains),max_twice_load=maxload))
        distinct_traces.add(hashlib.sha256(stable(trace).encode()).hexdigest())
    answer=dict(worlds_replayed=len(summaries),physical_ticks=ticks,distinct_traces=len(distinct_traces),violations=0)
    for key in ('energy','pulses','uncredited_full','ticks','final_identified','max_twice_load'):
        vals=[s[key] for s in summaries];answer[key]=dict(min=min(vals),max=max(vals),mean=statistics.mean(vals))
    for key in ('complete_without_full_identification','work_before_full_identification'):
        answer[key]=sum(s[key] for s in summaries)
    return answer

def run_case(case):
    jobs=(rich_workload if case.get('family')=='rich' else pair_workload)(case['n'],case['seed'],case['roomy'])
    m=LadderModel(case['n'],jobs,case['power'],case['energy'])
    result=ExactSearch(m,PROTOCOL['max_nodes'],PROTOCOL['max_seconds']).solve(m.initial())
    print('PHASE',case['id'],'SEARCH',result['status'],result['statistics']['elapsed_seconds'],flush=True)
    solve_stats=dict(model=dict(m.stats),inference=dict(m.inf.stats),
                     support_cache=m.inf.support.cache_info()._asdict(),outcome_cache=m.inf.outcomes.cache_info()._asdict())
    result['case']=case;result['jobs']=[j.__dict__ for j in jobs]
    metrics=interface_metrics(m,result)
    replays=replay_all_worlds(m,result)
    print('PHASE',case['id'],'METRICS_REPLAY_DONE',flush=True)
    checks={}
    if result['status']!=UNKNOWN:
        for mode in PROTOCOL['paired_checkers']:
            reps=[]
            for repeat in range(PROTOCOL['repetitions']):
                cm=LadderModel(case['n'],jobs,case['power'],case['energy'],checker=mode)
                checked=check_certificate(cm,cm.initial(),result)
                checked['model_stats']=dict(cm.stats);checked['inference_stats']=dict(cm.inf.stats)
                reps.append(checked)
                cm.inf.support.cache_clear();cm.inf.outcomes.cache_clear()
            checks[mode]=reps
            print('PHASE',case['id'],'CHECKED',mode,sum(r['seconds'] for r in reps),flush=True)
    frozen=LadderModel(case['n'],jobs,case['power'],case['energy'],frozen=True)
    frozen_result=ExactSearch(frozen,PROTOCOL['max_nodes'],PROTOCOL['max_seconds']).solve(frozen.initial())
    frozen_check=check_certificate(frozen,frozen.initial(),frozen_result)
    print('PHASE',case['id'],'FROZEN',frozen_result['status'],flush=True)
    # Predeclared 3 sampled worlds per configuration; not an exhaustive oracle claim.
    worlds=list(m.inf.complete_worlds(m.inf.initial()));rng=random.Random(900000+case['seed']+case['n'])
    sampled=rng.sample(worlds,min(3,len(worlds)))
    oracles=[]
    for world in sampled:
        om=LadderModel(case['n'],jobs,case['power'],case['energy'])
        initial=replace(om.initial(),domains=tuple(om.inf.mask(i,{p}) for i,p in enumerate(world)))
        ores=ExactSearch(om,PROTOCOL['max_nodes'],PROTOCOL['max_seconds']).solve(initial)
        oc=check_certificate(om,initial,ores)
        oracles.append(dict(world=world,status=ores['status'],statistics=ores['statistics'],validation=oc))
        om.inf.support.cache_clear();om.inf.outcomes.cache_clear()
    payload=dict(case=case,jobs=[j.__dict__ for j in jobs],status=result['status'],statistics=result['statistics'],
                 planner_model_statistics=solve_stats,interface_metrics=metrics,world_replay=replays,
                 checker_results=checks,frozen_evidence_status=frozen_result['status'],
                 frozen_evidence_statistics=frozen_result['statistics'],frozen_evidence_validation=frozen_check,
                 sampled_oracles=oracles,certificate_sha256=hashlib.sha256(stable(result['certificate']).encode()).hexdigest(),
                 certificate_bytes=len(stable(result['certificate']).encode()))
    gzip_dump(os.path.join(OUT,case['id']+'_certificate.json.gz'),result)
    gzip_dump(os.path.join(OUT,case['id']+'_frozen_certificate.json.gz'),frozen_result)
    dump(os.path.join(OUT,case['id']+'_summary.json'),payload)
    m.inf.support.cache_clear();m.inf.outcomes.cache_clear();frozen.inf.support.cache_clear();frozen.inf.outcomes.cache_clear()
    return payload

def main():
    os.makedirs(OUT,exist_ok=True)
    frozen=json.load(open(os.path.join(ROOT,'FROZEN_PROTOCOL.json')))
    assert frozen['protocol']==PROTOCOL and frozen['rich_protocol']==RICH_PROTOCOL
    results=[]
    for case in list(all_cases())+list(rich_cases()):
        path=os.path.join(OUT,case['id']+'_summary.json')
        if os.path.exists(path):
            row=json.load(open(path));print('RESUME',case['id'],row['status'],flush=True)
        else:
            row=run_case(case);print('DONE',case['id'],row['status'],row['statistics']['expanded'],flush=True)
        results.append(row);dump(os.path.join(OUT,'results.json'),dict(protocol=frozen,results=results));gc.collect()
    print('COUNTS',dict(Counter(r['status'] for r in results)),flush=True)
if __name__=='__main__':main()

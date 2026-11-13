#!/usr/bin/env python3
"""Independent dense-CSP and scalar physical replay. Does not import author engine."""
from pathlib import Path
from itertools import combinations, product
from fractions import Fraction
import hashlib,json,time
import numpy as np
ROOT=Path(__file__).resolve().parents[1]; EX=ROOT/'example'
def read(p):return json.loads(p.read_text())
def advance(c,a):return tuple(min(3,x+1) if y else 0 for x,y in zip(c,a))
def val(h,c):
    z=sum(int(c[p]>=r)<<j for j,(p,r) in enumerate(h['features']))
    return (h['table']>>z)&1
def catalogue(n):
    out=[{'features':[],'table':t} for t in (0,1)]
    out += [{'features':[(p,r)],'table':t} for p in range(n) for r in range(1,4) for t in (1,2)]
    tables=[t for t in range(16) if all(any(((t>>x)&1)!=((t>>(x^(1<<b)))&1) for x in range(4)) for b in range(2))]
    out += [{'features':[(p,r),(q,s)],'table':t} for p,q in combinations(range(n),2) for r,s in product(range(1,4),repeat=2) for t in tables]
    return out

def constructed():
    results=read(EX/'constructed_results.json'); reports=[]
    for row in results['runs']:
        m=row['response_count']; n=row['ports']; s=row['target_response_count']; tr=read(EX/row['trace_file']); truth=tr['generator_truth_for_independent_audit_only']; ticks=tr['physical_ticks']; recs=tr['records']; c=(3,)*n; energy=0
        for index,t in enumerate(ticks,1):
            assert index==t['t']; c=advance(c,t['commands']); assert c==tuple(t['counters']); energy+=sum(t['commands'])
            cap=1 if t['phase'] in ('initial_flush','calibration_flush','calibration_ramp') else (2 if t['phase'] in ('mission_preparation','fast_motion','slow_motion') else 4)
            assert sum(t['commands'])<=cap
        assert energy==row['command_energy_port_ticks'] and len(ticks)==row['whole_run_ticks']
        assert energy+len(ticks)==row['energy_units']
        cap=1+n*4+30+(s-1)*4+4;assert row['fixed_public_commissioning_cap']==cap and row['commissioning_ticks']<=cap
        assert row['mission_results'][0]['deadline_including_initialization']==cap+60*(s-1)
        assert row['coarse_first_mission_with_same_total_time_allowance']==(82*(s-1)<=cap+60*(s-1))
        transfers=row['safe_bay_transfers'];assert [(t['from'],t['to']) for t in transfers]==[('calibration','aggregate'),('aggregate','individual'),('individual','mission')]
        for transfer in transfers:
            segment=ticks[transfer['start_tick']:transfer['end_tick']];assert len(segment)==10
            v=Fraction(0);d=Fraction(0)
            for j,t in enumerate(segment):
                assert t['phase']=='slow_motion' and not any(t['commands'])
                vn=v+Fraction(1,4) if j<2 else v if j<8 else max(0,v-Fraction(1,4));d+=(v+vn)/8;v=vn;assert d<Fraction(21,20)
            assert d==1 and v==0
        for r in recs:
            location='calibration'
            for transfer in transfers:
                if r['tick']>=transfer['end_tick']:location=transfer['to']
            assert location==('aggregate' if r['kind']=='aggregate' else 'individual' if r['phase']=='individual_diagnostic' else 'calibration')
        for r in recs:
            assert r['context']==ticks[r['tick']-1]['counters']
            expected=val(truth[r['output']],r['context']) if r['kind']=='coordinate' else sum(val(truth[i],r['context']) for i in r['edge'])
            assert r['value']==expected
        # Independently filter complete local class from coordinate calibration.
        cat=catalogue(n); domains=[]
        for i in range(s):
            rs=[r for r in recs if r['kind']=='coordinate' and r['output']==i and r['phase']=='calibration']
            ds=[h for h in cat if all(val(h,r['context'])==r['value'] for r in rs)]
            assert len(ds)==2 and sorted(h['table'] for h in ds)==[6,14]; domains.append(ds)
        aggregates=[r for r in recs if r['kind']=='aggregate']; worlds=[[]]
        for i in range(s):
            new=[]
            for w in worlds:
                for h in domains[i]:
                    candidate=w+[h]
                    if all(sum(val(candidate[u],r['context']) for u in r['edge'])==r['value'] for r in aggregates if max(r['edge'])<=i):new.append(candidate)
            worlds=new
        assert len(worlds)==2
        diag=next(r for r in recs if r.get('phase')=='individual_diagnostic')
        assert {val(w[0],diag['context']) for w in worlds}=={0,1}
        for bc in row['branch_certificate']:
            compatible=[w for w in worlds if val(w[0],diag['context'])==bc['diagnostic_value']]; assert compatible
            # Full counterfactual causal execution, not just reported saturated guard query.
            cc=tuple(diag['context']); aa=[0]*n
            for _ in range(10):cc=advance(cc,aa)
            for mission in row['mission_results']:
                elapsed=0
                for job in mission['jobs']:
                    item=next(x for x in bc['completion'] if x['edge']==job['job']); i=min(item['certified_options']); fs=domains[i][0]['features']; command=[0]*n
                    for p,r in fs:command[p]=1
                    while any(cc[p]<r for p,r in fs) or aa!=command:cc=advance(cc,command);aa=command;elapsed+=1
                    v=Fraction(0);d=Fraction(0)
                    for t in range(43):
                        cc=advance(cc,aa);assert all(val(w[i],cc)==1 for w in compatible)
                        vn=v+Fraction(1,4) if t<4 else v if t<41 else max(0,v-Fraction(1,2));d+=(v+vn)/8;v=vn;assert d<Fraction(201,20)
                    assert v==0 and d==10;elapsed+=43
                assert elapsed<=mission['deadline']
        # Actual mission trace corresponds to the certified selections and guard is high every tick.
        previous=row['commissioning_ticks']
        for mission in row['mission_results']:
            assert mission['energy_units']<=mission['energy_budget']
            assert mission['energy_units']==sum(1+sum(t['commands']) for t in ticks[previous:mission['jobs'][-1]['finish_tick']])
            for job in mission['jobs']:
                segment=[t for t in ticks[previous:job['finish_tick']] if t['phase']=='fast_motion'];assert len(segment)==43
                assert all(val(truth[job['chosen']],t['counters'])==1 for t in segment);previous=job['finish_tick']
        reports.append({'m':m,'all_causal_ticks':len(ticks),'coordinate_or_aggregate_records':len(recs),'independently_filtered_local_candidates':len(cat),'persistent_residual_worlds':len(worlds),'all_diagnostic_branches_all_mission_orders_physically_replayed':True,'resource_scope':'all tick costs, causal bay access and 1m transfers checked; abstract nonbinding energy budget, no hardware calibration'})
    return reports

def partial():
    data=read(EX/'partial_acquisition_results.json');cat=catalogue(4);N=len(cat); cache={}
    def pred(c):
        c=tuple(c)
        if c not in cache:cache[c]=np.array([val(h,c) for h in cat],dtype=np.int8)
        return cache[c]
    def propagate(mats,domains=None):
        ds=[np.ones(N,dtype=bool) for _ in range(4)] if domains is None else [d.copy() for d in domains]
        change=True
        while change:
            change=False
            for (u,v),mat in mats.items():
                du=ds[u]&np.any(mat[:,ds[v]],axis=1);dv=ds[v]&np.any(mat[du,:],axis=0)
                if not np.array_equal(du,ds[u]) or not np.array_equal(dv,ds[v]):change=True
                ds[u]=du;ds[v]=dv
        return ds
    def assess(ds,mats,edge,c,future):
        branches=[];p=pred(c);i=edge[0]
        for b in (0,1):
            if not np.any(ds[i]&(p==b)):continue
            dd=[d.copy() for d in ds];dd[i]&=p==b
            if mats:dd=propagate(mats,dd)
            eligible=[u for u in edge if all(np.all(pred(x)[dd[u]]==1) for x in future)]
            branches.append((b,eligible))
        return branches
    totals={'trials':0,'exact_success':0,'rectangular_success':0,'exact_only_success':0}
    for run in data['runs']:
        truth=run['truth_for_generator_and_scoring_only'];c=(3,)*4
        for t in run['flush_trace']:c=advance(c,t['command']);assert list(c)==t['counters_after']
        mats={e:np.ones((N,N),dtype=bool) for e in [(0,1),(1,2),(2,3)]}
        for r in run['base_acquisition_records']:
            c=advance(c,r['command']);assert list(c)==r['counters_after'];e=tuple(r['observed_edge']);p=pred(c)
            assert sum(val(truth[i],c) for i in e)==r['observed_sum'];mats[e]&=(p[:,None]+p[None,:]==r['observed_sum'])
        base=c
        for tr in run['trials']:
            c=base
            for cc in tr['prep_counter_trace']:c=advance(c,tr['held_command']);assert list(c)==cc
            assert list(c)==tr['diagnostic_context'];e=tuple(tr['edge']);p=pred(c);mm=dict(mats);mm[e]=mats[e]&(p[:,None]+p[None,:]==tr['observed_sum']);ds=propagate(mm)
            assert sum(val(truth[i],c) for i in e)==tr['observed_sum'];tail=c;future=[]
            for _ in range(43):tail=advance(tail,tr['held_command']);future.append(tail)
            future=list(dict.fromkeys(future));assert [list(x) for x in future]==tr['unique_future_contexts']
            outcomes=[]
            for name,relations in [('exact',mm),('rectangular',{})]:
                branches=assess(ds,relations,e,c,future);stored=tr[name]['branches'];assert branches==[(b['coordinate_outcome'],b['certified_endpoints']) for b in stored]
                success=bool(branches) and all(opts for bit,opts in branches);assert success==tr[name]['guaranteed_choice_for_every_branch'];outcomes.append(success)
            totals['trials']+=1;totals['exact_success']+=bool(outcomes[0]);totals['rectangular_success']+=bool(outcomes[1]);totals['exact_only_success']+=bool(outcomes[0] and not outcomes[1])
    assert all(v==data['counts'][k] for k,v in totals.items());return totals
if __name__=='__main__':
    start=time.perf_counter();out={'constructed':constructed(),'partial_dense_independent_csp':partial()};out['seconds']=time.perf_counter()-start
    out['source_hashes']={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in EX.glob('*.py')};out['scope']='Independent arithmetic/data/finite-class policy check; not physical contract calibration or mission significance endorsement.'
    target=ROOT/'review'/'independent_execution_results.json';target.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))

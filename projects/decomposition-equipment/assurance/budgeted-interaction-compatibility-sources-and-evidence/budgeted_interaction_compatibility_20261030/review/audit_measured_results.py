"""Independent audit of every currently complete offered result; rerunnable.
Does not run or alter the experiment. Uses separate dense semantics.
"""
import gzip,json,pathlib,hashlib,sys,time,gc
from independent_execution_audit import Reference,canon,freeze,nid,audit_exports
ROOT=pathlib.Path(__file__).resolve().parents[1]
OUT=ROOT/'review'/'independent_case_audits';OUT.mkdir(exist_ok=True)

def replay(ref,result):
    if result['status']!='WIN':return None
    count=0;ticks=0;work_early=0;partial_finish=0;energy=[];pulse=[];uncredited=[];maxloads=[];finalknown=[];dur=[];traces=set()
    for w in ref.worlds:
        s=ref.initial();used=0;npulse=0;nextra=0;maxload=0;firstwork=None;firstfull=None;trace=[]
        while True:
            record=result['certificate'][nid(s)]
            if all(d.bit_count()==1 for d in s[4]) and firstfull is None:firstfull=s[0]
            if record['kind']=='terminal':
                assert ref.terminal(s)[0]=='WIN';break
            a=freeze(record['action']);controls,credits=a
            assert a in ref.actions(s)
            loads=tuple(controls[i]+(0 if p<0 else s[2][p]) for i,p in enumerate(w))
            assert max(loads)<=3;maxload=max(maxload,max(loads));used+=sum(controls)
            assert used<=ref.energy and sum(controls)<=ref.power
            if any(c>=0 for c in credits) and firstwork is None:firstwork=s[0]
            npulse+=controls.count(1);nextra+=controls.count(2)-sum(c>=0 for c in credits)
            edge=next(e for e in record['outcomes'] if tuple(e['observation'])==loads)
            sn=freeze(result['certificate'][edge['next']]['state'])
            # Validate persistent actual world belongs to all successive evidence.
            assert all(sn[4][i]&(1<<ref.choices[i].index(p)) for i,p in enumerate(w))
            trace.append((controls,credits,loads));s=sn;ticks+=1
        assert firstwork is not None
        count+=1;work_early+=firstfull is None or firstwork<firstfull;partial_finish+=firstfull is None
        energy.append(used);pulse.append(npulse);uncredited.append(nextra);maxloads.append(maxload);finalknown.append(sum(d.bit_count()==1 for d in s[4]));dur.append(s[0]);traces.add(hashlib.sha256(canon(trace).encode()).hexdigest())
    def agg(vals):return dict(min=min(vals),max=max(vals),mean=sum(vals)/len(vals))
    return dict(worlds_replayed=count,physical_ticks=ticks,distinct_traces=len(traces),violations=0,work_before_full_identification=work_early,complete_without_full_identification=partial_finish,energy=agg(energy),pulses=agg(pulse),uncredited_full=agg(uncredited),ticks=agg(dur),final_identified=agg(finalknown),max_twice_load=agg(maxloads))

def interface_metrics(ref,result):
    totals=dict(nodes=0,identified_parent_coordinates=0,prior_action_constant_rows=0,additional_evidence_constant_rows=0,remaining_nonconstant_rows=0,productive_rows_safe_only_after_evidence=0);maximum=0
    for rec in result['certificate'].values():
        s=freeze(rec['state']);support=ref.supported(s[4]);totals['nodes']+=1;maximum=max(maximum,len(ref.compatible(s[4])))
        totals['identified_parent_coordinates']+=sum(d.bit_count()==1 for d in support)
        for i in range(ref.n):
            before={0 if p<0 else s[2][p] for p in ref.choices[i]}
            after={0 if p<0 else s[2][p] for b,p in enumerate(ref.choices[i]) if support[i]&(1<<b)}
            key='prior_action_constant_rows' if len(before)==1 else ('additional_evidence_constant_rows' if len(after)==1 else 'remaining_nonconstant_rows');totals[key]+=1
            if rec['kind']=='choice' and rec['action'][0][i]==2 and 2 in before and 2 not in after:totals['productive_rows_safe_only_after_evidence']+=1
    return {'totals':{k:v for k,v in totals.items() if v},'maxima':{'worlds_consistent':maximum} if maximum else {}}

def clear(ref):
    for name in ('compatible','_actions_key','delayed_groups','supported'):getattr(ref,name).cache_clear()

start=time.time();counts={};allrows=[]
for path in sorted((ROOT/'example'/'results').glob('*_summary.json')):
    row=json.loads(path.read_text())
    if 'case' not in row:continue
    case=row['case'];id=case['id'];out=OUT/(id+'.json')
    certpath=path.parent/(id+'_certificate.json.gz');frozenpath=path.parent/(id+'_frozen_certificate.json.gz')
    fingerprints={'summary':hashlib.sha256(path.read_bytes()).hexdigest(),'certificate':hashlib.sha256(certpath.read_bytes()).hexdigest(),'frozen':hashlib.sha256(frozenpath.read_bytes()).hexdigest()}
    result=json.loads(gzip.decompress(certpath.read_bytes()));fr=json.loads(gzip.decompress(frozenpath.read_bytes()))
    assert result['case']==case and result['jobs']==row['jobs'] and result['status']==row['status']
    assert fr['status']==row['frozen_evidence_status']
    if out.exists() and json.loads(out.read_text())['fingerprints']==fingerprints:
        saved=json.loads(out.read_text());allrows.append(saved);continue
    ref=Reference(case['n'],row['jobs'],case['power'],case['energy'])
    assert hashlib.sha256(canon(result['certificate']).encode()).hexdigest()==row['certificate_sha256']
    verified=ref.certificate(result);rp=replay(ref,result)
    assert rp==row['world_replay'],(id,'replay mismatch',rp,row['world_replay'])
    metrics=interface_metrics(ref,result)
    assert metrics['maxima']==row['interface_metrics']['maxima'],(id,'maxima mismatch')
    assert all(metrics['totals'].get(k,0)==row['interface_metrics']['totals'].get(k,0) for k in set(metrics['totals'])|set(row['interface_metrics']['totals'])),(id,'metrics mismatch',metrics,row['interface_metrics'])
    clear(ref)
    rf=Reference(case['n'],row['jobs'],case['power'],case['energy'],frozen=True);fv=rf.certificate(fr);clear(rf)
    saved=dict(id=id,n=case['n'],status=row['status'],certificate=verified,frozen_certificate=fv,replay=rp,interface_metrics=metrics,fingerprints=fingerprints)
    out.write_text(json.dumps(saved,sort_keys=True,indent=2));allrows.append(saved)
    print('PASS',id,row['status'],verified['nodes'],flush=True);gc.collect()
protocol=json.loads((ROOT/'example'/'FROZEN_PROTOCOL.json').read_text())
expected={x['id']:x for x in protocol['offered_pair_cases']+protocol['offered_rich_cases']}
assert set(r['id'] for r in allrows)<=set(expected)
if '--require-complete' in sys.argv:assert set(r['id'] for r in allrows)==set(expected)
summary={'cases_audited':len(allrows),'status_counts':{k:sum(r['status']==k for r in allrows) for k in ('WIN','LOSE','UNKNOWN')},'certified_nodes':sum(r['certificate']['nodes'] for r in allrows),'frozen_certified_nodes':sum(r['frozen_certificate']['nodes'] for r in allrows),'physical_ticks':sum(r['replay']['physical_ticks'] for r in allrows if r['replay']),'world_replays':sum(r['replay']['worlds_replayed'] for r in allrows if r['replay']),'seconds_this_run':time.time()-start,'case_files':[r['id']+'.json' for r in allrows]}
(ROOT/'review'/'independent_execution_results.json').write_text(json.dumps(summary,sort_keys=True,indent=2));print(json.dumps(summary,indent=2))

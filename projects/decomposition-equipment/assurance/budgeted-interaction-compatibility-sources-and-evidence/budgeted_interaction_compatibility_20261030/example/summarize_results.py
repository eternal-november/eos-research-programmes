import json,collections,statistics,os
ROOT=os.path.dirname(os.path.abspath(__file__))
rows=json.load(open(os.path.join(ROOT,'results/results.json')))['results']

def summarize(rs):
    c=collections.Counter(x['status'] for x in rs)
    matched=collections.Counter((x['status'],x['frozen_evidence_status']) for x in rs)
    strict=[x['case']['id'] for x in rs if x['status']=='WIN' and x['frozen_evidence_status']=='LOSE']
    out=dict(offered=len(rs),status_counts=dict(c),matched_frozen={a+'/'+b:n for (a,b),n in matched.items()},strict_learning_cases=strict,
             sampled_oracle_status_counts=dict(collections.Counter(o['status'] for x in rs for o in x['sampled_oracles'])),
             solved_certificates=sum(x['status']!='UNKNOWN' for x in rs),
             unknown_reasons={'node_cap':sum(x['status']=='UNKNOWN' and x['statistics']['expanded']>=5000 for x in rs),
                              'wall_cap':sum(x['status']=='UNKNOWN' and x['statistics']['expanded']<5000 for x in rs)},
             planner_seconds=sum(x['statistics']['elapsed_seconds'] for x in rs),
             certificate_bytes=sum(x['certificate_bytes'] for x in rs))
    win=[x for x in rs if x['status']=='WIN']
    out['replay']={k:sum(x['world_replay'][k] for x in win) for k in ('worlds_replayed','physical_ticks','violations','complete_without_full_identification','work_before_full_identification')}
    out['interface_totals']=dict(sum((collections.Counter(x['interface_metrics']['totals']) for x in rs),collections.Counter()))
    out['paired_checkers']={}
    for mode in ('local','smart_global','full_scope'):
        items=[x['checker_results'][mode] for x in rs if mode in x['checker_results']]
        out['paired_checkers'][mode]=dict(cases=len(items),median_run_total_seconds=sum(statistics.median(z['seconds'] for z in reps) for reps in items),
                physical_rows=sum(reps[0]['model_stats'].get('physical_rows_checked',0) for reps in items),
                parent_values=sum(reps[0]['model_stats'].get('parent_values_checked',0) for reps in items),
                inference_pair_tests=sum(reps[0]['inference_stats'].get('separator_pair_tests',0)+reps[0]['inference_stats'].get('outcome_separator_tests',0) for reps in items))
    out['local_smart_global_identical_operation_counts']=all(x['checker_results']['local'][0]['model_stats']==x['checker_results']['smart_global'][0]['model_stats'] and x['checker_results']['local'][0]['inference_stats']==x['checker_results']['smart_global'][0]['inference_stats'] for x in rs if x['status']!='UNKNOWN')
    return out
out={family:summarize([x for x in rows if (x['case'].get('family')=='rich')==(family=='rich')]) for family in ('pair','rich')}
out['combined']=summarize(rows)
json.dump(out,open(os.path.join(ROOT,'results/aggregate_summary.json'),'w'),indent=2,sort_keys=True)
print(json.dumps(out,indent=2))

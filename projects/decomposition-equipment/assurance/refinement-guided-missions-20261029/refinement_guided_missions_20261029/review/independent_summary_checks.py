"""Read-only independent verification of final cost and matched summaries."""
import json
from pathlib import Path
from collections import Counter
P=Path(__file__).resolve().parents[1]/'example'
R=json.loads((P/'final_results.json').read_text())['results']
C=json.loads((P/'cost_summary.json').read_text())
M=json.loads((P/'matched_analysis.json').read_text())
key=lambda r:tuple(r[k] for k in ('n','L','s','seed','regime'))
for e in C['aggregates']:
    rr=[r for r in R if r['method']==e['method']];bb=[b for r in rr for b in r['batches']]
    assert e['streams']==len(rr) and e['batches']==len(bb)
    assert e['completed']==sum(r['completed'] for r in rr)
    assert e['ticks']==sum(r['total_ticks'] for r in rr)
    assert e['violations']==sum(r['total_violations'] for r in rr)==0
    for field in ('column_probes','rehearsals'):
        assert e[field]==sum(r['knowledge_stats'][field] for r in rr)
    assert e['diagnostic_energy_quarters']==sum(b['diagnostic_energy_quarters'] for b in bb)
    assert e['statuses']==dict(Counter(b['status'] for b in bb))
    assert e['final_ranks']==[r['cache_stats']['rank'] for r in rr]
    assert e['final_known_counts']==[len(r['final_known_columns']) for r in rr]
    for kind,number in e['tick_breakdown'].items():
        assert number==sum(x['kind']==kind for r in rr for x in r['trace'])
    tails=sum(r['L'] for r in rr for b in r['batches'] if b['completed'])
    assert e['terminal_service_tail_ticks']==tails
    assert e['other_zero_service_ticks']==sum(x['kind']=='service' and not any(x['u_quarters']) for r in rr for x in r['trace'])-tails
    for label,expected in (('solver_seconds',sum(p['solver']['seconds'] for b in bb for p in b['proposals'])),('checking_seconds',sum(p.get('checking_seconds',0) for b in bb for p in b['proposals']))):
        assert abs(e[label]-expected)<1e-7
for method,e in M['comparisons'].items():
    counts=Counter();pairs=[];prefixes=[]
    for local in [r for r in R if r['method']=='local_column']:
        other=next(r for r in R if r['method']==method and key(r)==key(local))
        la=[];oa=[];lt=ot=0
        for a,b in zip(local['batches'],other['batches']):
            counts[str(int(a['completed']))+str(int(b['completed']))]+=1
            la.append(a['completed']);oa.append(b['completed']);lt+=a['elapsed_ticks'];ot+=b['elapsed_ticks']
            prefixes.append(dict(key=list(key(local)),through_batch=a['index'],same_completion_mask=la==oa,local_completed=sum(la),other_completed=sum(oa),local_ticks=lt,other_ticks=ot))
            if a['completed'] and b['completed']:
                pairs.append(dict(key=list(key(local)),batch=a['index'],local_ticks=a['elapsed_ticks'],other_ticks=b['elapsed_ticks']))
    assert e['joint_completion_counts_local_other']==dict(counts)
    assert e['joint_completed_batch_costs']==pairs and e['prefixes']==prefixes
for e in M['by_dimension_regime']:
    rr=[r for r in R if all(r[k]==e[k] for k in ('method','n','regime'))]
    bb=[b for r in rr for b in r['batches']]
    assert e['completed']==sum(b['completed'] for b in bb) and e['offered']==len(bb)
    assert e['first_completed']==sum(r['batches'][0]['completed'] for r in rr)
    assert e['later_completed']==sum(b['completed'] for r in rr for b in r['batches'][1:])
    assert e['statuses']==dict(Counter(b['status'] for b in bb))
print(json.dumps(dict(status='passed',aggregate_methods=len(C['aggregates']),matched_comparisons=len(M['comparisons']),dimension_regime_rows=len(M['by_dimension_regime'])),indent=2))

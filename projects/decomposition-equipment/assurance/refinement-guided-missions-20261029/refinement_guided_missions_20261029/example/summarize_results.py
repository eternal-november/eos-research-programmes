"""Descriptive fixed-suite aggregation; never filters seeds by outcome."""
import json, sys
from pathlib import Path
from collections import Counter
P=Path(__file__).resolve().parent
x=json.loads((P/(sys.argv[1] if len(sys.argv)>1 else 'final_results.json')).read_text()); rows=[]
for method in dict.fromkeys(r['method'] for r in x['results']):
 rr=[r for r in x['results'] if r['method']==method]; bb=[b for r in rr for b in r['batches']]
 row={'method':method,'streams':len(rr),'batches':len(bb),'completed':sum(b['completed'] for b in bb),'ticks':sum(r['total_ticks'] for r in rr),'violations':sum(r['total_violations'] for r in rr),'column_probes':sum(r['knowledge_stats']['column_probes'] for r in rr),'rehearsals':sum(r['knowledge_stats']['rehearsals'] for r in rr),'diagnostic_energy_quarters':sum(b['diagnostic_energy_quarters'] for b in bb),'solver_seconds':sum(p['solver']['seconds'] for b in bb for p in b['proposals']),'checking_seconds':sum(p.get('checking_seconds',0) for b in bb for p in b['proposals']),'statuses':dict(Counter(b['status'] for b in bb)),'tick_breakdown':{k:sum(b['tick_breakdown'][k] for b in bb) for k in ('startup_flush','column_probe','rehearsal','service')},'final_ranks':[r['cache_stats']['rank'] for r in rr],'final_known_counts':[len(r['final_known_columns']) for r in rr]}
 row['terminal_probe_tail_ticks']=sum(r['L']*r['knowledge_stats']['column_probes'] for r in rr)
 row['terminal_rehearsal_tail_ticks']=sum(r['L']*r['knowledge_stats']['rehearsals'] for r in rr)
 row['diagnostic_effort_ticks']=row['diagnostic_energy_quarters']/4
 row['direct_exact_unsafe_cuts']=sum('direct_exact_unsafe_cut' in p for b in bb for p in b['proposals'])
 row['terminal_service_tail_ticks']=sum(r['L']*r['completed'] for r in rr)
 row['other_zero_service_ticks']=sum(b['zero_service_ticks'] for b in bb)-row['terminal_service_tail_ticks']
 uncertain=[]
 for r in rr:
  for b in r['batches']:
   for prop in b['proposals']:
    proof=prop.get('certificate',{}).get('proof',[])
    if prop.get('verified') is False and proof and proof[-1]['kind']=='rational_LP':
     prefix=prop['trace_prefix']
     nextkind=r['trace'][prefix]['kind'] if prefix<b['trace_end'] else None
     uncertain.append({'probe': 'probe_column' in prop,'rehearsal':nextkind=='rehearsal'})
 row['inconclusive_relaxation_failures']=len(uncertain)
 row['probes_after_inconclusive_relaxation']=sum(z['probe'] for z in uncertain)
 row['rehearsals_after_inconclusive_relaxation']=sum(z['rehearsal'] for z in uncertain)
 rows.append(row)
comparisons=[]
for r in x['results']:
 if r['method']!='local_column':continue
 key=tuple(r[k] for k in ('n','L','s','seed','regime'))
 peers={q['method']:q for q in x['results'] if tuple(q[k] for k in ('n','L','s','seed','regime'))==key}
 comparisons.append({'key':key,'methods':{m:{'completed':q['completed'],'ticks':q['total_ticks'],'probes':q['knowledge_stats']['column_probes'],'rehearsals':q['knowledge_stats']['rehearsals']} for m,q in peers.items()}})
report={'protocol_sha256':x['protocol_sha256'],'source_sha256':x['source_sha256'],'source_sha256_by_method':x.get('source_sha256_by_method',{}),'aggregates':rows,'matched_streams':comparisons}
(P/'cost_summary.json').write_text(json.dumps(report,indent=2))
print(json.dumps(rows,indent=2))

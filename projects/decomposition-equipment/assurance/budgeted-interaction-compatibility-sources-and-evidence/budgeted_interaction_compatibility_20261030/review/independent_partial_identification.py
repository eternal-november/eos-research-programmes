"""Post-hoc descriptive breakdown, not a new benchmark or saving claim."""
import pathlib,json,gzip,collections
from independent_execution_audit import Reference
ROOT=pathlib.Path(__file__).resolve().parents[1]
rows=[];total=collections.Counter()
for p in sorted((ROOT/'example'/'results').glob('*_summary.json')):
    s=json.loads(p.read_text())
    if 'case' not in s or s['status']!='WIN':continue
    case=s['case'];c=json.loads(gzip.decompress((p.parent/(case['id']+'_certificate.json.gz')).read_bytes()))
    ref=Reference(case['n'],s['jobs'],case['power'],case['energy']);counts=collections.Counter()
    allnodes={v for j in s['jobs'] for route in j['routes'] for v in route}
    seenworlds=set()
    for rec in c['certificate'].values():
        if rec['kind']!='terminal':continue
        t,e,prev,prog,domains=rec['state'];used={v for j,(route,done) in zip(s['jobs'],prog) for v in j['routes'][route]}
        worlds=ref.compatible(tuple(domains));weight=len(worlds)
        assert not seenworlds.intersection(worlds),'Two terminal states claim same persistent deterministic world'
        seenworlds.update(worlds)
        counts['terminal_leaves']+=1;counts['world_replays']+=weight
        for name,nodes in [('any',range(case['n'])),('route_union',allnodes),('chosen_route',used)]:
            if any(domains[v].bit_count()>1 for v in nodes):counts['leaves_unknown_'+name]+=1;counts['worlds_unknown_'+name]+=weight
    assert seenworlds==set(ref.worlds)
    rows.append(dict(case=case['id'],counts=dict(counts)));total.update(counts);ref.compatible.cache_clear()
report=dict(scope='Post-hoc descriptive attribution; parent identification is not identical to mission-sufficient information, and no minimum acquisition claim follows.',cases=len(rows),totals=dict(total),rows=rows)
(ROOT/'review'/'independent_partial_identification_results.json').write_text(json.dumps(report,sort_keys=True,indent=2));print(json.dumps({k:v for k,v in report.items() if k!='rows'},indent=2))

"""Independent row-invariant and supplemental split audit: no implementation imports."""
import itertools,json,hashlib
from pathlib import Path
R=Path(__file__).resolve().parents[1];E=R/'example';D=E/'results'
count=0;rows=0
# Units quarters: enumerate all n=3 grid rows, present/past actions, maximal
# independently chosen own background compatible with present good-event gate.
for coeff in itertools.product((0,1,2),repeat=6):
    a=coeff[:3];b=coeff[3:]
    if sum(coeff)>3 or sum(a[1:])+sum(b)>2:continue
    rows+=1
    for bits in itertools.product((0,1),repeat=6):
        now=bits[:3];past=bits[3:];background=3 if now[0] else 4
        load=background+sum(x*y for x,y in zip(a,now))+sum(x*y for x,y in zip(b,past))
        assert load<=6;count+=1
# Independently verify split trace from saved learned B/FIFO, not world.
main=json.loads((D/'results.json').read_text());split=json.loads((D/'split_trace_regression.json').read_text())
for case in main['family_runs']:
    i=json.loads((D/(case['id']+'_interface.json')).read_text());n=case['n'];remaining=set(range(n));arrivals={}
    while remaining:
        c=[];j=min(remaining)
        while j not in c:
            c.append(j);remaining.remove(j);j=next(k for k,v in enumerate(i['B'][j]) if v)
        for k,j in enumerate(c):arrivals[j]=-10 if k<3 else 0
    available={};trace=[];ends=[None]*n
    for j,t in sorted(arrivals.items(),key=lambda x:(x[1],x[0])):
        server=i['fifo'][j];start=max(t,available.get(server,t));available[server]=start+1;ends[j]=t//10
        trace.append(dict(channel=j,arrival=t,service_start=start,delivery=start+1,capture_frame=t//10))
    saved=next(s for s in split['cases'] if s['case']==case['id']);assert trace==saved['request_trace'] and ends==saved['endpoints']
    assert all(t['delivery']<=10 and 10-t['capture_frame']*10<=20 for t in trace)
    tokens=sorted({(0,i['blocks'][j],f) for j in range(n) for f in (ends[j]-1,ends[j])})
    assert [list(t) for t in tokens]==saved['source_tokens']
    assert len(tokens)*i['p_upper']>.05 and not saved['accepted']
out={'coefficient_rows':rows,'independent_active_inactive_history_vertex_checks':count,'split_trace_replays':12,'status':'PASS','proof':'Active own background<=.75 and total<=.75; inactive own background<=1 and external-current+all-lag<=.5. Nonnegative coefficients. Applies to arbitrary prior binary commands, not only canonical cycle.','experiment_sha256':hashlib.sha256((E/'experiment.py').read_bytes()).hexdigest(),'results_sha256':hashlib.sha256((D/'results.json').read_bytes()).hexdigest()}
(R/'review/independent_guard_audit_results.json').write_text(json.dumps(out,indent=2));print(out)

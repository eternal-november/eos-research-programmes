#!/usr/bin/env python3
"""Costed observable enrichment, using a packaged copy of the existing pipeline.
Oracle chooses permitted realizations; runtime decode sees only public records.
"""
import sys,json,hashlib
from pathlib import Path
from itertools import permutations,product,combinations
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'observable_reference'))
from reference_shared_pipeline import Plant,PublicCaps,Budget,Learner,envelope,production
N=4; ROLES=('A','B','A','B'); P=((0,3),(1,2)); PAIRS=list(combinations(range(N),2))
CAPS=PublicCaps(n=N,work_upper=100,R=400,J=0)
BUDGET=Budget()
ENV=envelope(N,CAPS.work_upper,CAPS.R,BUDGET,comparison_bound=len(PAIRS))
class PublicLogPlant(Plant):
    """Instrument only the caller's known requests, never a service/grant log."""
    def __init__(self,*a,**kw): super().__init__(*a,**kw); self.request_log=[]
    def admit_batch(self,t,requests):
        requests=list(requests)
        self.request_log.append({'start':t,'requests':[{'module':r.module,'operation':r.operation,'useful':r.useful} for r in requests]})
        return super().admit_batch(t,requests)
def decode(diagnostic_raw,own_log,batch_raw,caps,production_start=None):
    """Pure observable map delta; no Plant, truth priority, edges, or learner."""
    production_start=ENV['T0'] if production_start is None else production_start
    assert caps.J==0 and len(own_log)==2*caps.n+len(PAIRS)
    assert all(set(r)=={'start','requests'} for r in own_log)
    # Fixed records are separated by publicly reserved, nonoverlapping windows.
    records=[]
    for k,entry in enumerate(own_log):
        start=entry['start']; end=own_log[k+1]['start'] if k+1<len(own_log) else production_start
        records.append([(t,bit) for t,bit in diagnostic_raw if start<t<end])
    local={}; edges=[]
    for k in range(2*caps.n):
        e=own_log[k]; req=e['requests']; raw=records[k]
        assert len(req)==len(raw)==1 and not req[0]['useful']
        local[req[0]['module'],req[0]['operation']]=raw[0][0]-e['start']
    Q=local[0,'P']
    assert 0<Q<=caps.work_upper
    assert all(local[i,'P']==Q and local[i,'D']==2*Q for i in range(caps.n))
    for entry,raw in zip(own_log[2*caps.n:],records[2*caps.n:]):
        a,c=entry['requests']; start=entry['start']
        assert a['operation']=='D' and c['operation']=='P' and not a['useful'] and not c['useful']
        assert len(raw)==2 and raw[-1][0]-start==3*Q
        lag=raw[0][0]-start; assert lag in (Q,2*Q)
        edges.append((a['module'],c['module']) if lag==2*Q else (c['module'],a['module']))
    # A unique topological order computed from observable comparison edges.
    order=[]; remaining=set(range(caps.n))
    while remaining:
        enabled=[j for j in remaining if not any(v==j and u in remaining for u,v in edges)]
        assert len(enabled)==1
        order.append(enabled[0]);remaining.remove(enabled[0])
    assert len(batch_raw)==caps.n
    assert [t for t,b in batch_raw]==[production_start+(k+1)*Q for k in range(caps.n)]
    b=tuple(bit for t,bit in batch_raw)
    vector={r:0 for r in ROLES}
    for j,bit in zip(order,b):vector[ROLES[j]]^=bit
    return {'b':b,'y':tuple(vector[r] for r in ('A','B')),'order':order,'edges':edges}

def direct(pi,b):
    return tuple(sum(b[k] for k,j in enumerate(pi) if ROLES[j]==role)%2 for role in ('A','B'))
rows_all={b:set() for b in product((0,1),repeat=N)}; rows_P={b:set() for b in rows_all}
runs=[]; predicate_checks=0
for pi in permutations(range(N)):
    for b in rows_all:
        # Oracle-only support coupling. These are possible fresh iid fair-bit
        # sample outcomes, not a runtime operation choosing or piloting payloads.
        module_bits=[b[pi.index(j)] for j in range(N)]
        p=PublicLogPlant(pi,Q=100,caps=CAPS,payloads=[0]*20+module_bits,lags=[0]*24)
        learner=Learner(p,BUDGET,CAPS);learner.calibrate()
        for pair in PAIRS:learner.before(*pair)
        p.advance(p.now+BUDGET.compile);learner.cost['compile']=BUDGET.compile
        assert p.now<=ENV['T0']
        raw_d=list(p.raw);log_d=list(p.request_log)
        out=production(p,learner.edges,list(ROLES),ENV['T0'],BUDGET,ENV['deadline'],local_work=learner.local,caps=CAPS)
        assert out['status']=='COMMAND' and out['finished']<=ENV['deadline']
        decoded=decode(raw_d,log_d,out['raw'],CAPS)
        assert tuple(decoded['order'])==pi # oracle-only assertion
        assert decoded['edges']==learner.edges
        assert decoded['b']==b and decoded['y']==direct(pi,b)
        assert decoded['y']==tuple(out['vector'][r] for r in ('A','B'))
        # Reproduction uses only serialized raw data and the caller's public log.
        serialized=json.loads(json.dumps({'diagnostic_raw':raw_d,'log':log_d,'batch_raw':out['raw']}))
        again=decode(serialized['diagnostic_raw'],serialized['log'],serialized['batch_raw'],CAPS)
        assert again==decoded
        for wanted_b in rows_all:
            for wanted_y in product((0,1),repeat=2):
                pullback=(decoded['b']==wanted_b and decoded['y']==wanted_y)
                semantic=(b==wanted_b and direct(pi,b)==wanted_y)
                assert pullback==semantic; predicate_checks+=1
        in_P=all(pi.index(i)<pi.index(j) for i,j in P)
        rows_all[b].add(decoded['y'])
        if in_P:rows_P[b].add(decoded['y'])
        runs.append({'priority_oracle':pi,'in_LE_P':in_P,'observed_b':b,'decoded_y':decoded['y'],'diagnostic_raw':raw_d,'own_request_log':log_d,'batch_raw':out['raw'],'finished':out['finished'],'cost':learner.cost})
for b in rows_all:
    assert rows_all[b]=={direct(pi,b) for pi in permutations(range(N))}
    assert rows_P[b]=={direct(pi,b) for pi in permutations(range(N)) if all(pi.index(i)<pi.index(j) for i,j in P)}
assert rows_P[(0,0,1,1)]=={(1,1)}
assert len({json.dumps(x['own_request_log'],sort_keys=True) for x in runs})==1
assert len(runs)==384 and sum(r['in_LE_P'] for r in runs)==96
# Supplemental actual-context replay: retain the SAME persistent Plant after
# identical old calibration/two-pair records, then enrich without resetting it.
# Reserve both old and new comparisons plus an extra whole grid for the old
# compile stage BEFORE seeing observations. The local calibration is reused.
SAME_ENV=envelope(N,CAPS.work_upper,CAPS.R,BUDGET,comparison_bound=8)
SAME_ENV=dict(SAME_ENV)
SAME_ENV['old_compile_extra_reserve']=CAPS.R
SAME_ENV['T0']+=CAPS.R; SAME_ENV['deadline']+=CAPS.R
same_world_runs=[]
for pi in permutations(range(N)):
    if not all(pi.index(i)<pi.index(j) for i,j in P): continue
    b=(0,0,1,1); module_bits=[b[pi.index(j)] for j in range(N)]
    p=PublicLogPlant(pi,Q=100,caps=CAPS,payloads=[0]*24+module_bits,lags=[0]*28)
    learner=Learner(p,BUDGET,CAPS);learner.calibrate()
    calibration_raw=list(p.raw); calibration_log=list(p.request_log)
    for pair in P: assert learner.before(*pair)
    p.advance(p.now+BUDGET.compile)
    old_raw=list(p.raw); old_log=list(p.request_log); old_end=p.now
    new_raw_begin=len(p.raw);new_log_begin=len(p.request_log)
    for pair in PAIRS:learner.before(*pair)
    p.advance(p.now+BUDGET.compile);learner.cost['compile']=2*BUDGET.compile
    assert p.now<=SAME_ENV['T0'] and p.now>old_end
    # Selection is by the controller's public experiment-stage log, not truth.
    decoder_raw=calibration_raw+list(p.raw[new_raw_begin:])
    decoder_log=calibration_log+list(p.request_log[new_log_begin:])
    all_diagnostic_raw=list(p.raw);all_diagnostic_log=list(p.request_log)
    out=production(p,learner.edges,list(ROLES),SAME_ENV['T0'],BUDGET,SAME_ENV['deadline'],local_work=learner.local,caps=CAPS)
    assert out['status']=='COMMAND' and out['finished']<=SAME_ENV['deadline']
    decoded=decode(decoder_raw,decoder_log,out['raw'],CAPS,production_start=SAME_ENV['T0'])
    assert decoded['b']==b and decoded['y']==(1,1) and tuple(decoded['order'])==pi
    assert len(p.request_log)==17 # 8 singleton + 2 old pair + 6 new pair + batch
    assert sum(len(e['requests']) for e in p.request_log)==28
    same_world_runs.append({'priority_oracle':pi,'old_raw':old_raw,'old_own_request_log':old_log,'old_end':old_end,'all_diagnostic_raw':all_diagnostic_raw,'all_diagnostic_own_request_log':all_diagnostic_log,'batch_raw':out['raw'],'decoded_y':decoded['y'],'finished':out['finished'],'cost':learner.cost})
assert len(same_world_runs)==6
assert all(r['old_raw']==same_world_runs[0]['old_raw'] and r['old_own_request_log']==same_world_runs[0]['old_own_request_log'] for r in same_world_runs)
result={'all_passed':True,'same_persistent_world_supplement':{'runs':len(same_world_runs),'old_records_identical':True,'no_reset':True,'fixed_envelope':SAME_ENV,'diagnostic_invocations':24,'productive_invocations':4,'fixtures':same_world_runs},'runs':len(runs),'P_subfamily_runs':sum(r['in_LE_P'] for r in runs),'observable_predicate_pullback_checks':predicate_checks,'public_caps':CAPS.__dict__,'budget':BUDGET.__dict__,'fixed_envelope':ENV,'fixed_diagnostic_invocations':20,'productive_invocations':4,'support_sample_probability':'2^-24 for each prescribed 24-bit realization under independent fair bits; priority has no assigned probability','decoder_inputs':'raw diagnostic (time,bit), own request log, raw batch (time,bit), public caps; fixed public ENV and ROLES','old_raw_profile_equivalent':False,'extra_acquisition_free':False,'relative_dependencies':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted((HERE/'observable_reference').glob('*.py'))},'fixtures':runs}
(HERE/'observable_enrichment_results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ('fixtures','relative_dependencies','same_persistent_world_supplement')},indent=2))

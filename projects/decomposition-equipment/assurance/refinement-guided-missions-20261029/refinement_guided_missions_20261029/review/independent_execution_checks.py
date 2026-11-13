"""Independent exact execution replay primitives. No author implementation imports.

Command units are actual rational effort, kernel entries integer G, physical
kernel G/4. Flattened kernel/evidence order is lag-major then input.
"""
from fractions import Fraction as Q
from itertools import product
from math import floor
import json


def rational(x):
    if isinstance(x, dict):
        return Q(x['numerator'], x['denominator'])
    if isinstance(x, (tuple, list)) and len(x) == 2:
        return Q(*x)
    if isinstance(x, float):
        raise ValueError('Binary float is not an exact replay number')
    return Q(x)


def feature(history, t, n, lag):
    return tuple(rational(history[t-l][j]) if 0 <= t-l < len(history) else Q(0)
                 for l in range(lag+1) for j in range(n))


def convolve(history, G, n, lag):
    return [tuple(sum((rational(g)*u for g,u in zip(row,feature(history,t,n,lag))), Q(0))/4
                  for row in G) for t in range(len(history))]


def decode(z, amplitude, observation_error=Q(1,128)):
    """Uniquely recover integer response a.G, not noisy observations as equations."""
    scale = rational(amplitude)/4
    assert scale > 2*observation_error
    normalized = rational(z)/scale
    integer = floor(normalized + Q(1,2))
    assert abs(rational(z)-integer*scale) <= observation_error
    return integer


def sparse_bound(a, known, s, gmax=4):
    """known maps flattened coordinates to coefficients (whole known columns)."""
    assert all(rational(x) >= 0 for x in a)
    assert all(0 <= v <= gmax and int(v) == v for v in known.values())
    remaining = s-sum(v>0 for v in known.values())
    assert remaining >= 0
    fixed = sum((rational(a[j])*v for j,v in known.items()), Q(0))
    free = sorted((rational(v) for j,v in enumerate(a) if j not in known), reverse=True)
    return fixed + gmax*sum(free[:remaining], Q(0))


def dual_bound(A, b, a, y, lam, s, gmax=4):
    """Derive a fresh weak-duality bound rather than trust reported residual."""
    y, lam = list(map(rational,y)), rational(lam)
    assert lam >= 0 and len(A) == len(b) == len(y)
    assert all(len(row) == len(a) for row in A)
    residual = [rational(v)-lam-sum((y[k]*A[k][j] for k in range(len(A))),Q(0)) for j,v in enumerate(a)]
    bound = sum((v*rational(w) for v,w in zip(y,b)),Q(0)) + lam*gmax*s + gmax*sum((max(Q(0),r) for r in residual),Q(0))
    return floor(bound), bound


def matrix_rank(A):
    """Independent batch rational forward elimination, with normalized pivots."""
    if not A:
        return 0
    M = [list(map(rational,row)) for row in A]
    rank = 0
    for col in range(len(M[0])):
        pivot = next((i for i in range(rank,len(M)) if M[i][col]),None)
        if pivot is None:
            continue
        M[rank], M[pivot] = M[pivot], M[rank]
        divisor=M[rank][col]
        M[rank]=[x/divisor for x in M[rank]]
        for i in range(rank+1,len(M)):
            b=M[i][col]
            if b:
                M[i] = [x-b*y for x,y in zip(M[i],M[rank])]
        rank += 1
        if rank == len(M):
            break
    return rank


def check_span_value(A,b,a,value):
    """Consistency/rank criterion independent of author's RREF implementation."""
    r = matrix_rank(A)
    assert matrix_rank(A+[list(a)]) == r
    assert matrix_rank([list(x)+[v] for x,v in zip(A,b)]+[list(a)+[value]]) == r


def replay_ticks(commands,G,n,lag,s,physical=None,sensor=None,observed=None):
    assert all(len(row) == n*(lag+1) and all(type(g) is int and 0<=g<=4 for g in row) and sum(g>0 for g in row)<=s for row in G)
    power = max(2,n//3)
    nominal = convolve(commands,G,n,lag)
    for t,u in enumerate(commands):
        assert len(u)==n and all(rational(v) in (0,Q(1,4),1) for v in u)
        assert sum(map(rational,u)) <= power
        for i,v in enumerate(nominal[t]):
            assert v+Q(1,256) <= Q(6,4)+Q(1,256), (t,i,'robust physical capacity')
            if physical is not None:
                d = rational(physical[t][i])-v
                assert abs(d)<=Q(1,256)
            if observed is not None:
                assert abs(rational(observed[t][i])-v)<=Q(1,128)
                if physical is not None:
                    assert abs(rational(observed[t][i])-rational(physical[t][i]))<=Q(1,256)
    assert len(commands)>=lag and all(not any(map(rational,u)) for u in commands[-lag:]) if lag else True
    return nominal


def selftest():
    count=0
    for response in range(21):
        for amp in (Q(1,4),Q(1)):
            for noise in (-Q(1,128),Q(0),Q(1,128)):
                assert decode(response*amp/4+noise,amp)==response
                count+=1
    rows=list(product(range(5),repeat=3))
    comparisons=0
    for s in range(4):
        for a in product((Q(0),Q(1,4),Q(1)),repeat=3):
            for known in ({},{0:0},{0:1},{0:4},{0:1,1:0}):
                candidates=[g for g in rows if sum(v>0 for v in g)<=s and all(g[j]==v for j,v in known.items())]
                if not candidates: continue
                assert sparse_bound(a,known,s)==max(sum(x*y for x,y in zip(a,g)) for g in candidates)
                comparisons+=1
    A=[[1,1,0],[1,0,1],[0,1,1]]; b=[3,4,5]
    check_span_value(A,b,[1,0,0],1)
    assert matrix_rank(A)==3
    bound,_=dual_bound([[1,1,0]],[2],[1,0,1],[Q(31,29)],Q(1,7),1)
    for g in rows:
        if sum(g)<=4 and g[0]+g[1]==2: assert g[0]+g[2]<=bound
    # A delayed peak is checked at zero-command tail, not only active service.
    try:
        replay_ticks([[1,0],[0,1],[0,0],[0,0]],[[0,0,0,4,4,0]],2,2,2)
    except AssertionError:
        pass
    else:
        raise AssertionError('Unsafe delayed history accepted')
    return {'noise_endpoint_cases':count,'top_k_exhaustive_comparisons':comparisons,'status':'passed','scope':'primitive proof regressions, not mission outcomes'}



def verify_schedule(schedule,spec,n,L):
    tau,finish=schedule['start_clock'],schedule['finish_clock']
    U=schedule['U']; assert len(U)==finish-tau and finish<=spec['deadline']
    rebuilt=[[0]*n for _ in U]; chosen={}
    for ji,si,mi,start,duration,mode in schedule['chosen']:
        assert 0<=ji<len(spec['jobs'])
        job=spec['jobs'][ji]; assert 0<=si<len(job['stages'])
        stage=job['stages'][si]; assert 0<=mi<len(stage['modes'])
        assert mode==list(stage['modes'][mi]) and duration==stage['duration']
        assert (ji,si) not in chosen
        assert start>=max(tau,job['release']) and start+duration+L<=min(job['due'],finish)
        chosen[ji,si]=(start,duration)
        for t in range(start,start+duration):
            for j in mode: rebuilt[t-tau][j]+=1
    for ji,job in enumerate(spec['jobs']):
        for si in range(len(job['stages'])):
            assert (ji,si) in chosen
            if si: assert sum(chosen[ji,si-1])<=chosen[ji,si][0]
    assert rebuilt==U
    assert all(all(v in (0,1) for v in u) and sum(u)<=max(2,n//3) for u in U)
    assert all(not any(u) for u in U[-L:])


def replay_result(r):
    n,L,s=r['n'],r['L'],r['s']; G=[sum(row,[]) for row in r['kernel_for_independent_audit']]
    ticks=r['trace']; commands=[[Q(v,4) for v in x['u_quarters']] for x in ticks]
    physical=[[Q(a+b,256) for a,b in zip(x['nominal_load_256'],x['disturbance_256'])] for x in ticks]
    observed=[[Q(v,256) for v in x['observed_256']] for x in ticks]
    nominal=replay_ticks(commands,G,n,L,s,physical=physical,observed=observed)
    assert all(x['t']==t for t,x in enumerate(ticks))
    assert all([256*v for v in nominal[t]]==x['nominal_load_256'] for t,x in enumerate(ticks))
    assert all(all(a+b+c==z for a,b,c,z in zip(x['nominal_load_256'],x['disturbance_256'],x['sensor_noise_256'],x['observed_256'])) for x in ticks)
    assert r['total_ticks']==len(ticks) and r['total_violations']==0
    assert all(x['kind']=='startup_flush' and not any(x['u_quarters']) for x in ticks[:L])
    records=r.get('raw_records',r.get('cached_equations',[]))
    allA=[]; allB=[]; record_ends=[]; cursor=L
    for rec in records:
        assert len(rec['A'])==len(rec['B'])
        for a,b in zip(rec['A'],rec['B']):
            assert len(a)==n*(L+1) and len(b)==n
            assert all(v in (0,1) for v in a)
            assert all(sum(x*y for x,y in zip(a,g))==v for g,v in zip(G,b))
        segment=ticks[cursor:cursor+len(rec['A'])]
        assert len(segment)==len(rec['A']) and all(x['kind']==rec['kind'] for x in segment)
        amp=Q(1) if rec['kind']=='service' else Q(1,4)
        binary=[[rational(v)/4/amp for v in x['u_quarters']] for x in segment]
        assert all([int(v) for v in feature(binary,t,n,L)]==a for t,a in enumerate(rec['A']))
        assert all([decode(Q(v,256),amp) for v in x['observed_256']]==b for x,b in zip(segment,rec['B']))
        assert all(not any(u) for u in binary[-L:])
        cursor+=len(segment);record_ends.append(cursor)
        allA.extend(rec['A']); allB.extend(rec['B'])
    assert cursor==len(ticks)
    certificates=0; services=0; duals=0; evidence_maps={}
    for b in r['batches']:
        begin,end=b['trace_start'],b['trace_end']; segment=ticks[begin:end]
        assert end-begin==b['elapsed_ticks'] and b['elapsed_ticks']<=b['spec']['deadline']
        assert b['diagnostic_energy_quarters']==sum(sum(x['u_quarters']) for x in segment if x['kind']!='service')
        assert b['service_ticks']==sum(x['kind']=='service' for x in segment)
        if b['completed']:
            schedule=b['accepted_schedule']; verify_schedule(schedule,b['spec'],n,L)
            service=ticks[begin+schedule['start_clock']:begin+schedule['finish_clock']]
            assert len(service)==len(schedule['U'])
            assert all(x['kind']=='service' and x['u_quarters']==[4*v for v in u] for x,u in zip(service,schedule['U']))
            assert end==begin+schedule['finish_clock'];services+=1
        else: assert b['accepted_schedule'] is None
        for p in b['proposals']:
            prefix=p['trace_prefix']; assert prefix==begin+p['tau'] and begin<=prefix<=end
            if 'certificate' not in p:continue
            schedule=p.get('schedule')
            if schedule is None and p.get('verified'):schedule=b['accepted_schedule']
            if schedule is None:continue # Recorded as coverage limitation, never a passed check.
            verify_schedule(schedule,b['spec'],n,L)
            assert schedule['start_clock']==p['tau']
            U=schedule['U']; Ac=[list(feature(U,t,n,L)) for t in range(len(U))]
            known={l*n+j:G[0][l*n+j] for j in p['known_columns'] for l in range(L+1)}
            nr=p['evidence_records']; assert nr<=len(records)
            assert (record_ends[nr-1] if nr else L)<=prefix
            assert nr==len(records) or record_ends[nr]>prefix
            evidence_count=p['evidence_rows']; A=allA[:evidence_count]; B=allB[:evidence_count]
            if r['method'].startswith('cached'):
                assert evidence_count==sum(len(rec['A']) for rec in records[:nr])
            elif r['method']!='oracle':
                measured=set()
                for rec in records[:nr]:
                    if rec['kind']=='column_probe':
                        first=rec['A'][0][:n];assert sum(first)==1
                        measured.add(first.index(1))
                assert measured==set(p['known_columns'])
            assert evidence_count<=len(allA)
            if r['method'].startswith('cached'):
                if evidence_count not in evidence_maps:
                    evidence_maps[evidence_count]=independent_evidence_map(A,B)
                rank,infer=evidence_maps[evidence_count]
                for j in p['known_columns']:
                    for l in range(L+1):
                        unit=[0]*(n*(L+1));unit[l*n+j]=1
                        assert infer(unit)==[g[l*n+j] for g in G]
            if 'direct_exact_unsafe_cut' in p:
                cut=p['direct_exact_unsafe_cut'];assert r['method']=='cached_rehearsal'
                assert cut['trace_prefix']==prefix and cut['evidence_rows']==evidence_count
                assert cut['feature']==Ac[p['certificate']['t']]
                assert infer(cut['feature'])==cut['predicted'] and max(cut['predicted'])>6
                assert p['certificate']['proof'][-1]['kind']=='exact_rowspan'
                at=b['proposals'].index(p)
                if at+1<len(b['proposals']):assert b['proposals'][at+1]['tau']==p['tau']
                else:assert prefix==b['trace_end']
            if 'rehearsal_certificate' in p:
                rc=p['rehearsal_certificate']; rp=rc['trace_prefix']
                trial=ticks[prefix:rp]
                assert len(trial)==len(U)
                assert all(x['kind']=='rehearsal' and x['u_quarters']==u for x,u in zip(trial,U))
                decoded=[[decode(Q(v,256),Q(1,4)) for v in x['observed_256']] for x in trial]
                assert max(map(max,decoded))==rc['decoded_max_load']<=6
                assert b['accepted_schedule']['U']==U
                assert b['accepted_schedule']['start_clock']==schedule['start_clock']+len(U)
                assert rc['evidence_records']==nr+1 and rc['evidence_rows']==evidence_count+len(U)
            for proof in p['certificate']['proof']:
                a=Ac[proof['t']]
                top=[sparse_bound(a,{l*n+j:g[l*n+j] for j in p['known_columns'] for l in range(L+1)},s) for g in G]
                if proof['kind']=='column_topk':assert top==proof['upper']
                elif proof['kind']=='exact_rowspan':
                    assert infer(a)==proof['upper']
                elif proof['kind']=='rational_LP':
                    upper=top[:]
                    for item in proof['certs']:
                        i=item['output'];bound=item['bound'];cert=bound['certificate']
                        u,exact=dual_bound(A,[row[i] for row in B],a,cert['y'],cert['lambda_'],s)
                        assert u==bound['upper'] and exact==rational(cert['exact_upper'])
                        upper[i]=min(upper[i],u);duals+=1
                    assert upper==proof['upper']
                else:raise AssertionError('Unknown certificate kind')
                if p.get('verified'):assert max(proof['upper'])<=6
                certificates+=1
            if p.get('verified'):assert len(p['certificate']['proof'])==len(U)
    assert services==r['completed']
    return {'method':r['method'],'n':n,'seed':r['seed'],'regime':r['regime'],'ticks':len(ticks),'services':services,'certificate_ticks':certificates,'dual_certificates':duals}


def independent_evidence_map(A,B):
    """Forward elimination with augmented responses, independent replay implementation."""
    basis=[]
    for ar,br in zip(A,B):
        row=list(map(rational,ar))+list(map(rational,br))
        d=len(ar)
        for pivot,existing in basis:
            if row[pivot]:
                factor=row[pivot]/existing[pivot]
                row=[v-factor*w for v,w in zip(row,existing)]
        pivot=next((j for j in range(d) if row[j]),None)
        if pivot is None:
            assert not any(row[d:])
        else:
            basis.append((pivot,row));basis.sort(key=lambda item:item[0])
    def response(a):
        row=list(map(rational,a)); values=[Q(0)]*(len(B[0]) if B else 0)
        for pivot,existing in basis:
            if row[pivot]:
                factor=row[pivot]/existing[pivot]
                row=[v-factor*w for v,w in zip(row,existing[:len(a)])]
                values=[v+factor*w for v,w in zip(values,existing[len(a):])]
        return None if any(row) else values
    return len(basis),response


def audit_file(path,require_complete=True):
    from pathlib import Path
    import hashlib
    data=json.loads(Path(path).read_text()); results=data['results']
    assert hashlib.sha256(Path(path).with_name('FROZEN_PROTOCOL.md').read_bytes()).hexdigest()==data['protocol_sha256']
    if data.get('source_sha256') is not None:
        assert hashlib.sha256(Path(path).with_name('delayed_missions.py').read_bytes()).hexdigest()==data['source_sha256']
    else:
        available_hashes={hashlib.sha256(p.read_bytes()).hexdigest() for p in (Path(path).with_name('delayed_missions.py'),Path(path).parent/'v1'/'delayed_missions.py')}
        source_data={}
        for result in results:
            source=result['source_sha256']; assert source in available_hashes
            assert data['source_sha256_by_method'][result['method']]==source
            filename=result['source_result_file']; assert filename in ('mission_results.json','corrected_rehearsal_results.json')
            if filename not in source_data:source_data[filename]=json.loads(Path(path).with_name(filename).read_text())
            original=source_data[filename]; assert original['source_sha256']==source
            match=[r for r in original['results'] if all(r[k]==result[k] for k in ('n','L','s','seed','regime','method'))]
            assert len(match)==1 and match[0]=={k:v for k,v in result.items() if k not in ('source_sha256','source_result_file')}
    identity=lambda r:(r['n'],r['L'],r['s'],r['seed'],r['regime'],r['method'])
    expected={(n,L,s,seed,regime,method) for n,L,s in ((6,2,3),(10,3,4),(14,4,5)) for seed in (202610292300,202610292301) for regime in ('roomy','tight') for method in ('coarse_initial','local_column','dense_column','cached_column','cached_rehearsal','oracle')}
    actual={identity(r) for r in results}
    assert len(actual)==len(results) and actual<=expected
    if require_complete: assert actual==expected, (len(actual),len(expected))
    checks=[replay_result(r) for r in results]
    witnesses_path=Path(path).with_name('coarse_infeasibility_witnesses.json')
    witness_count=0
    if witnesses_path.exists():
        witnesses=json.loads(witnesses_path.read_text())
        specs={(r['n'],r['L'],r['s'],r['seed'],r['regime'],b['index']):b['spec'] for r in results for b in r['batches']}
        for w in witnesses:
            key=tuple(w[k] for k in ('n','L','s','seed','regime','index'))
            if key not in specs:
                assert not require_complete
                continue
            ji,si,duration=w['witness_job_stage_duration']
            stage=specs[key]['jobs'][ji]['stages'][si]
            assert stage['duration']==duration>=2 and w['s']>=2 and w['L']>=1
            assert len(stage['modes'])==2 and all(len(mode)>=1 for mode in stage['modes'])
            for mode in stage['modes']:
                j=mode[0];assert 0<=j<w['n']
                g=[0]*(w['n']*(w['L']+1));g[j]=g[w['n']+j]=4
                command=[[int(k in mode) for k in range(w['n'])] for t in range(duration)]
                a=feature(command,1,w['n'],w['L'])
                assert sum(v*x for v,x in zip(g,a))==8>6
            witness_count+=1
        if require_complete:assert witness_count==72==len(witnesses)
    for r in results:
        for row in r['kernel_for_independent_audit']:
            taps=[(l,j) for l,lagrow in enumerate(row) for j,v in enumerate(lagrow) if v]
            assert len(taps)==r['s'] and len({l for l,j in taps})>=2 and len({j for l,j in taps})>=2
        for other in results:
            if (r['n'],r['seed'])==(other['n'],other['seed']):
                assert r['kernel_for_independent_audit']==other['kernel_for_independent_audit']
                if r['regime']==other['regime']:assert [b['spec'] for b in r['batches']]==[b['spec'] for b in other['batches']]
    paired=0
    index={identity(r):r for r in results}
    for key,r in index.items():
        if r['method']!='local_column': continue
        other=index.get(key[:-1]+('dense_column',))
        if other is None:continue
        for field in ('trace','cached_equations','final_known_columns','completed','total_ticks'):
            assert r[field]==other[field], (key,field)
        for a,b in zip(r['batches'],other['batches']):
            for field in ('spec','status','accepted_schedule','known_columns','elapsed_ticks'):
                assert a[field]==b[field], (key,field)
            assert [p.get('probe_column') for p in a['proposals']]==[p.get('probe_column') for p in b['proposals']]
        paired+=1
    summary={}
    for r,c in zip(results,checks):
        key=r['method']; z=summary.setdefault(key,dict(streams=0,completed_batches=0,completed_jobs=0,ticks=0,diagnostic_energy_quarters=0,column_probes=0,rehearsals=0,startup_ticks=0,column_probe_tail_ticks=0,rehearsal_tail_ticks=0,service_tail_ticks=0,uncertified_lp_query_actions=0))
        z['streams']+=1;z['completed_batches']+=r['completed'];z['ticks']+=r['total_ticks']
        z['completed_jobs']+=sum(len(b['spec']['jobs']) for b in r['batches'] if b['completed'])
        z['diagnostic_energy_quarters']+=sum(b['diagnostic_energy_quarters'] for b in r['batches'])
        z['column_probes']+=r['knowledge_stats']['column_probes'];z['rehearsals']+=r['knowledge_stats']['rehearsals']
        records=r['cached_equations']
        z['startup_ticks']+=r['L']
        for rec in records:
            kind=rec['kind']
            z[{'column_probe':'column_probe_tail_ticks','rehearsal':'rehearsal_tail_ticks','service':'service_tail_ticks'}[kind]]+=r['L']
        for batch in r['batches']:
            for proposal in batch['proposals']:
                proof=proposal.get('certificate',{}).get('proof',[])
                if not proposal.get('verified') and proof and proof[-1]['kind']=='rational_LP':
                    prefix=proposal['trace_prefix']
                    if prefix<len(r['trace']) and r['trace'][prefix]['kind'] in ('column_probe','rehearsal') and prefix<batch['trace_end']:
                        z['uncertified_lp_query_actions']+=1
        assert r['knowledge_stats']['column_probes']==sum(rec['kind']=='column_probe' for rec in records)<=r['n']
        assert r['knowledge_stats']['rehearsals']==sum(rec['kind']=='rehearsal' for rec in records)
        if r['method'].startswith('cached'):
            A=[a for rec in records for a in rec['A']]
            assert r['cache_stats']['rows']==len(A)
            assert r['cache_stats']['rank']==matrix_rank(A)
    return dict(status='passed',complete=len(actual)==len(expected),streams=len(results),batches=sum(len(r['batches']) for r in results),source_sha256=data['source_sha256'],source_sha256_by_method=data.get('source_sha256_by_method'),protocol_sha256=data['protocol_sha256'],results_sha256=hashlib.sha256(Path(path).read_bytes()).hexdigest(),independent_source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),regressions=selftest(),local_dense_exact_pairs=paired,coarse_fixed_schedule_witnesses=witness_count,summary=summary,replay=checks)

if __name__=='__main__':
    import argparse
    parser=argparse.ArgumentParser();parser.add_argument('--results');parser.add_argument('--output');parser.add_argument('--partial',action='store_true');args=parser.parse_args()
    report=audit_file(args.results,not args.partial) if args.results else selftest()
    if args.output:
        from pathlib import Path
        Path(args.output).write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='replay'},indent=2))

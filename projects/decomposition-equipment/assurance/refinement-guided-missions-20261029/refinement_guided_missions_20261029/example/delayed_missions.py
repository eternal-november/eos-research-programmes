"""Refinement-guided synthetic delayed-resource missions.

All coefficients and accepted certificate arithmetic use integers. SciPy MILP
only proposes schedules. Plant truth is used only inside Plant.step and in the
explicit known-kernel reference. Fixed-schedule CEGIS, not general feedback.
"""
from __future__ import annotations
import copy, hashlib, json, math, time
from pathlib import Path
from fractions import Fraction
import numpy as np
from scipy.optimize import milp, Bounds, LinearConstraint
from scipy.sparse import coo_matrix
from rehearsal_cache import CachedLinearEvidence

ROOT=Path(__file__).resolve().parent
METHODS=('coarse_initial','local_column','dense_column','cached_column','cached_rehearsal','oracle')
DIMENSIONS=((6,2,3),(10,3,4),(14,4,5))
SEEDS=(202610292300,202610292301)
CAP=6


def serial(x):
    if isinstance(x, Fraction): return [x.numerator,x.denominator]
    if isinstance(x,np.ndarray): return x.tolist()
    if isinstance(x,np.integer): return int(x)
    raise TypeError(type(x).__name__)


def digest(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def make_world(n,L,s,seed):
    rng=np.random.default_rng(seed+n*1000+L*100+s)
    G=np.zeros((n,L+1,n),dtype=np.int64)
    for i in range(n):
        while True:
            positions=rng.choice(n*(L+1),s,replace=False)
            if len(set(int(p)%n for p in positions))>=2 and len(set(int(p)//n for p in positions))>=2:break
        for p in positions:G[i,int(p)//n,int(p)%n]=int(rng.integers(1,5))
    return G


def make_jobs(n,L,seed,index,regime):
    rng=np.random.default_rng(seed+100000*n+1000*index+17*L)
    jobs=[]
    for k in range(max(2,n//3)):
        stages=[]
        for r in range(int(rng.integers(2,4))):
            modes=[]
            while len(modes)<2:
                size=int(rng.integers(1,3))
                mode=tuple(sorted(map(int,rng.choice(n,size,replace=False))))
                if mode not in modes:modes.append(mode)
            stages.append(dict(duration=int(rng.integers(1,4)),modes=modes))
        jobs.append(dict(id=k,release=int(rng.integers(0,4)),stages=stages,due_offset=int(rng.integers(0,4))))
    work=sum(st['duration'] for j in jobs for st in j['stages'])
    H=(2*work+L+6) if regime=='roomy' else (work+L+4)
    A=L+n*(L+1) if index==0 else 0
    D=A+H
    for j in jobs:j['due']=max(D-j.pop('due_offset'),j['release']+sum(st['duration'] for st in j['stages'])+L)
    # The generated minimum cannot exceed D for the declared positive workloads;
    # assert a protocol fact, not a hidden feasible-plant assumption.
    assert all(j['due']<=D for j in jobs)
    return dict(jobs=jobs,deadline=D,service_allowance=H,commissioning_allowance=A,work=work)


class Plant:
    def __init__(self,G,L,seed):
        self._kernel=G.copy();self.n=G.shape[2];self.m=G.shape[0];self.L=L
        self.history=[np.zeros(self.n,dtype=np.int64) for _ in range(L)]
        self.rng=np.random.default_rng(seed);self.trace=[];self.clock=0
    def step(self,command_quarters,kind):
        u=np.array(command_quarters,dtype=np.int64)
        assert u.shape==(self.n,) and np.all((0<=u)&(u<=4))
        feature=np.stack([u]+self.history)
        load=np.einsum('ilj,lj->i',self._kernel,feature).astype(np.int64)
        disturbance=self.rng.integers(-1,2,self.m);sensor=self.rng.integers(-1,2,self.m)
        observed=16*load+disturbance+sensor
        # Physical capacity is 385/256. Worst additive disturbance is 1/256.
        robust_safe=bool(np.all(16*load+1<=385))
        self.trace.append(dict(t=self.clock,kind=kind,u_quarters=u.tolist(),observed_256=observed.tolist(),
            nominal_load_256=(16*load).tolist(),disturbance_256=disturbance.tolist(),sensor_noise_256=sensor.tolist(),worst_envelope_safe=robust_safe))
        self.clock+=1
        if self.L:self.history=[u.copy()]+self.history[:-1]
        return observed.tolist()
    def rest(self):return not any(np.any(h) for h in self.history)


def features(U,L):
    U=np.asarray(U,dtype=np.int64);T,n=U.shape
    A=[]
    for t in range(T):
        A.append(np.concatenate([U[t-l] if t>=l else np.zeros(n,dtype=np.int64) for l in range(L+1)]))
    return np.asarray(A,dtype=np.int64)


class Knowledge:
    def __init__(self,n,L,s,method):
        self.n=n;self.L=L;self.s=s;self.method=method
        self.G=np.zeros((n,L+1,n),dtype=np.int64);self.known=np.zeros(n,dtype=bool)
        self.cache=CachedLinearEvidence(n,n,L,s);self.raw=[];self.patterns=set()
        self.stats=dict(topk_checks=0,cache_checks=0,cache_bounds=0,column_probes=0,rehearsals=0,certificates=0)
        self.certificates=[]
    def observe(self,A,B,kind):
        self.raw.append(dict(kind=kind,A=np.asarray(A).tolist(),B=np.asarray(B).tolist()))
        if self.method.startswith('cached'):
            self.cache.add_rows(A,B)
            # Promote only exactly identified whole columns, never guessed zeros.
            for j in range(self.n):
                if self.known[j]:continue
                vals=[]
                for l in range(self.L+1):
                    a=[0]*self.cache.d;a[l*self.n+j]=1
                    v=self.cache.infer_vector(a)
                    if v is None:break
                    if any(x.denominator!=1 or not 0<=x<=4 for x in v):raise ValueError('Invalid identified coefficient')
                    vals.append([int(x) for x in v])
                if len(vals)==self.L+1:
                    self.G[:,:,j]=np.asarray(vals).T;self.known[j]=True
    def probe(self,j,plant):
        assert not self.known[j] and plant.rest()
        U=np.zeros((self.L+1,self.n),dtype=np.int64);U[0,j]=1
        B=[]
        for u in U:
            obs=plant.step(u,'column_probe')
            # eps*Delta = 1/16; total observation error <=2/256.
            b=[int(round(v/16)) for v in obs]
            assert all(abs(v-16*x)<=2 for v,x in zip(obs,b))
            B.append(b)
        self.G[:,:,j]=np.asarray(B).T;self.known[j]=True
        self.stats['column_probes']+=1
        self.observe(features(U,self.L),B,'column_probe')
        assert plant.rest()
    def topk(self,a):
        a=np.asarray(a,dtype=np.int64).reshape(self.L+1,self.n)
        vals=[];witnesses=[]
        for i in range(self.n):
            known=(sum(int(self.G[i,l,j])*int(a[l,j]) for l,j in zip(*np.nonzero(self.G[i]))) if self.method=='local_column' else int(np.sum(self.G[i]*a)))
            k=self.s-int(np.count_nonzero(self.G[i]))
            assert k>=0
            unknown=[(int(a[l,j]),l,j) for l in range(self.L+1) for j in range(self.n) if not self.known[j]]
            unknown.sort(reverse=True)
            selected=[(l,j) for weight,l,j in unknown[:k] if weight>0]
            vals.append(known+4*sum(int(a[l,j]) for l,j in selected));witnesses.append(selected)
        self.stats['topk_checks']+=1
        return vals,witnesses
    def certify(self,U):
        A=features(U,self.L);proof=[]
        for t,a in enumerate(A):
            upper,witness=self.topk(a)
            if self.method.startswith('cached') and max(upper,default=0)>CAP:
                self.stats['cache_checks']+=1
                exact=self.cache.infer_vector(a)
                if exact is not None:
                    assert all(x.denominator==1 for x in exact)
                    upper=[int(x) for x in exact]
                    proof.append(dict(t=t,kind='exact_rowspan',upper=upper))
                else:
                    certs=[]
                    for i in range(self.n):
                        if upper[i]<=CAP:continue
                        bound=self.cache.bound_vector(a,i)
                        self.stats['cache_bounds']+=1
                        upper[i]=min(upper[i],bound['upper'])
                        certs.append(dict(output=i,bound=bound))
                    proof.append(dict(t=t,kind='rational_LP',upper=upper,certs=certs))
            else:proof.append(dict(t=t,kind='column_topk',upper=upper))
            if max(upper,default=0)>CAP:
                i=max(range(self.n),key=lambda i:upper[i])
                candidates=[j for l,j in witness[i] if not self.known[j]]
                return False,dict(t=t,output=i,upper=upper[i],unknown_columns=sorted(set(candidates)),proof=proof)
        self.stats['certificates']+=1
        self.certificates.append(proof)
        return True,dict(proof=proof)


def plan(jobspec,n,L,P,tau,G,patterns,limit=10,initial_robust=False):
    tic=time.perf_counter();D=jobspec['deadline'];jobs=jobspec['jobs']
    variants=[];groups=[];stage_meta=[]
    for ji,job in enumerate(jobs):
        for si,stage in enumerate(job['stages']):
            group=[]
            for mi,mode in enumerate(stage['modes']):
                for start in range(max(tau,job['release']),job['due']-L-stage['duration']+1):
                    group.append(len(variants));variants.append((ji,si,mi,start,stage['duration'],tuple(mode)))
            if not group:return None,dict(status='empty_stage_window',seconds=time.perf_counter()-tic)
            groups.append(group);stage_meta.append((ji,si))
    z=len(variants);N=z+1
    occupancy=[[{} for _ in range(D)] for _ in range(n)]
    for k,(_,_,_,start,dur,mode) in enumerate(variants):
        for j in mode:
            for t in range(start,start+dur):occupancy[j][t][k]=1
    rows=[];lo=[];hi=[]
    def add(row,lower=-np.inf,upper=np.inf):rows.append(row);lo.append(lower);hi.append(upper)
    for group in groups:add({k:1 for k in group},1,1)
    indices={pair:group for pair,group in zip(stage_meta,groups)}
    for ji,job in enumerate(jobs):
        for si in range(len(job['stages'])-1):
            row={k:variants[k][3]+variants[k][4] for k in indices[(ji,si)]}
            row.update({k:-variants[k][3] for k in indices[(ji,si+1)]});add(row,upper=0)
        last=indices[(ji,len(job['stages'])-1)]
        row={k:variants[k][3]+variants[k][4]+L for k in last};row[z]=-1;add(row,upper=0)
    for j in range(n):
        for t in range(D):
            if occupancy[j][t]:add(occupancy[j][t],upper=1)
    for t in range(D):
        row={}
        for j in range(n):
            for k,v in occupancy[j][t].items():row[k]=row.get(k,0)+v
        if row:add(row,upper=P)
    if initial_robust:
        # Exact initial top-k condition for binary loads, s>=2 and CAP=6<8.
        for t in range(D):
            row={}
            for l in range(L+1):
                if t<l:continue
                for j in range(n):
                    for k,v in occupancy[j][t-l].items():row[k]=row.get(k,0)+v
            if row:add(row,upper=1)
    for i in range(n):
        taps=list(zip(*np.nonzero(G[i])))
        for t in range(D):
            row={}
            for l,j in taps:
                if t<l:continue
                for k,v in occupancy[j][t-l].items():row[k]=row.get(k,0)+int(G[i,l,j])*v
            if row:add(row,upper=CAP)
    # Any superset of a measured unsafe activation pattern is unsafe by positivity.
    for pattern in patterns:
        for t in range(D):
            row={};possible=True
            for flat in pattern:
                l,j=divmod(flat,n)
                if t<l:possible=False;break
                for k,v in occupancy[j][t-l].items():row[k]=row.get(k,0)+v
            if possible and row:add(row,upper=len(pattern)-1)
    rr=[];cc=[];dd=[]
    for r,row in enumerate(rows):
        for c,v in row.items():rr.append(r);cc.append(c);dd.append(v)
    mat=coo_matrix((dd,(rr,cc)),shape=(len(rows),N)).tocsc()
    objective=np.zeros(N);objective[z]=1
    bounds=Bounds(np.zeros(N),np.r_[np.ones(z),D])
    result=milp(objective,integrality=np.ones(N),bounds=bounds,
        constraints=LinearConstraint(mat,np.asarray(lo),np.asarray(hi)),
        options=dict(time_limit=limit,mip_rel_gap=0))
    info=dict(status=int(result.status),message=result.message,seconds=time.perf_counter()-tic,
        variables=N,constraints=len(rows),solver_objective=None if result.fun is None else float(result.fun))
    if result.x is None:return None,info
    chosen=[variants[k] for k in range(z) if result.x[k]>.5]
    if len(chosen)!=len(groups):return None,{**info,'certificate_rejected':'nonintegral selection'}
    U=np.zeros((D,n),dtype=np.int64)
    for _,_,_,start,dur,mode in chosen:
        for j in mode:U[start:start+dur,j]+=1
    finish=max(start+dur+L for _,_,_,start,dur,_ in chosen)
    schedule=dict(chosen=[list(v[:5])+[list(v[5])] for v in chosen],U=U[tau:finish].tolist(),
        start_clock=tau,finish_clock=finish)
    ok,reason=check_schedule(schedule,jobspec,n,L,P)
    if not ok:return None,{**info,'certificate_rejected':reason}
    return schedule,info


def check_schedule(schedule,jobspec,n,L,P):
    chosen=schedule['chosen'];tau=schedule['start_clock'];finish=schedule['finish_clock']
    U=np.asarray(schedule['U'],dtype=np.int64)
    if U.shape!=(finish-tau,n) or np.any((U<0)|(U>1)):return False,'command domain'
    if np.any(U.sum(axis=1)>P):return False,'power'
    if finish>jobspec['deadline']:return False,'batch deadline'
    by={}
    rebuilt=np.zeros_like(U)
    for ji,si,mi,start,dur,mode in chosen:
        if (ji,si) in by:return False,'duplicate stage'
        try:job=jobspec['jobs'][ji];stage=job['stages'][si]
        except IndexError:return False,'stage index'
        if dur!=stage['duration'] or tuple(mode)!=tuple(stage['modes'][mi]):return False,'mode'
        if start<max(tau,job['release']) or start+dur+L>job['due']:return False,'release/due'
        if start+dur+L>finish:return False,'tail'
        for j in mode:rebuilt[start-tau:start-tau+dur,j]+=1
        by[ji,si]=(start,dur)
    for ji,job in enumerate(jobspec['jobs']):
        for si in range(len(job['stages'])):
            if (ji,si) not in by:return False,'missing service'
            if si and by[ji,si-1][0]+by[ji,si-1][1]>by[ji,si][0]:return False,'precedence'
    if not np.array_equal(rebuilt,U):return False,'command reconstruction'
    if L and np.any(U[-L:]):return False,'uncleared tail'
    return True,'accepted'


def execute_binary(plant,U,kind,scale_quarters):
    assert plant.rest()
    U=np.asarray(U,dtype=np.int64);B=[]
    divisor=16*scale_quarters
    for u in U:
        obs=plant.step(u*scale_quarters,kind)
        b=[int(round(v/divisor)) for v in obs]
        assert all(abs(v-divisor*x)<=2 for v,x in zip(obs,b))
        B.append(b)
    assert plant.rest()
    return features(U,plant.L),np.asarray(B,dtype=np.int64)


def run_method(G,L,s,seed,regime,method):
    n=G.shape[0];P=max(2,n//3);plant=Plant(G,L,seed+501)
    knowledge=Knowledge(n,L,s,method)
    if method=='oracle':knowledge.G=G.copy();knowledge.known[:]=True
    batches=[]
    for index in range(6):
        spec=make_jobs(n,L,seed,index,regime);begin=plant.clock
        if index==0:
            for _ in range(L):plant.step(np.zeros(n,dtype=int),'startup_flush')
        proposals=[];status='proposal_limit';accepted=None
        for iteration in range(2*n+12):
            tau=plant.clock-begin
            schedule,solver=plan(spec,n,L,P,tau,knowledge.G,knowledge.patterns,initial_robust=(method=='coarse_initial'))
            record=dict(iteration=iteration,tau=tau,solver=solver,evidence_records=len(knowledge.raw),evidence_rows=len(knowledge.cache.A),trace_prefix=plant.clock,known_columns=np.where(knowledge.known)[0].tolist())
            proposals.append(record)
            if schedule is None:
                status='planner_'+str(solver['status']);break
            record['schedule']=schedule
            checking_start=time.perf_counter()
            ok,certificate=knowledge.certify(np.asarray(schedule['U']))
            record['checking_seconds']=time.perf_counter()-checking_start
            record['verified']=ok;record['certificate']=certificate
            if ok:
                # A cache/rehearsal may previously have consumed time; schedule is current.
                A,B=execute_binary(plant,schedule['U'],'service',4)
                knowledge.observe(A,B,'service');accepted=schedule;status='completed';break
            if method=='coarse_initial':
                status='initial_robust_certificate_rejected';break
            if method=='cached_rehearsal':
                # Exact observed linear consequences are known unsafe, not uncertain.
                # Exclude the positive activation pattern without a physical replay.
                last=certificate['proof'][-1]
                if last['kind']=='exact_rowspan':
                    feature=features(schedule['U'],L)[certificate['t']]
                    pattern=tuple(map(int,np.where(feature>0)[0]))
                    assert pattern and max(last['upper'])>CAP
                    knowledge.patterns.add(pattern)
                    record['direct_exact_unsafe_cut']=dict(feature=feature.tolist(),predicted=last['upper'],evidence_rows=len(knowledge.cache.A),trace_prefix=plant.clock)
                    continue
                duration=len(schedule['U'])
                if tau+2*duration>spec['deadline']:
                    status='rehearsal_and_service_budget';break
                A,B=execute_binary(plant,schedule['U'],'rehearsal',1)
                knowledge.stats['rehearsals']+=1;knowledge.observe(A,B,'rehearsal')
                violations=np.argwhere(B>CAP)
                if not len(violations):
                    # Execute identical causal commands later; releases remain valid,
                    # but all job-specific deadlines must be rechecked after the shift.
                    shifted=copy.deepcopy(schedule)
                    shifted['chosen']=[[ji,si,mi,start+duration,dur,mode] for ji,si,mi,start,dur,mode in schedule['chosen']]
                    shifted['start_clock']+=duration;shifted['finish_clock']+=duration
                    valid,why=check_schedule(shifted,spec,n,L,P)
                    if valid:
                        record['rehearsal_certificate']={'trace_prefix':plant.clock,'evidence_records':len(knowledge.raw),'evidence_rows':len(knowledge.cache.A),'decoded_max_load':int(B.max()),'response_lattice_units':16,'observation_error_units':2,'physical_limit':CAP}
                        A2,B2=execute_binary(plant,shifted['U'],'service',4)
                        knowledge.observe(A2,B2,'service');accepted=shifted;status='completed';break
                    record['rehearsal_shift_rejected']=why
                for t,i in violations:
                    pattern=tuple(map(int,np.where(A[int(t)]>0)[0]))
                    if pattern:knowledge.patterns.add(pattern)
                continue
            unknown=certificate.get('unknown_columns',[])
            if not unknown:
                # A known counterexample indicates numerical scheduling/certificate failure.
                status='known_counterexample';break
            if tau+L+1>spec['deadline']:
                status='probe_budget';break
            j=min(unknown)
            record['probe_column']=j
            knowledge.probe(j,plant)
        assert plant.rest()
        trace=plant.trace[begin:]
        batches.append(dict(index=index,spec=spec,status=status,completed=status=='completed',
            elapsed_ticks=plant.clock-begin,proposals=proposals,accepted_schedule=accepted,
            known_columns=np.where(knowledge.known)[0].tolist(),stats=copy.deepcopy(knowledge.stats),
            cache_stats=copy.deepcopy(knowledge.cache.stats),trace_start=begin,trace_end=plant.clock,
            diagnostic_energy_quarters=sum(sum(x['u_quarters']) for x in trace if x['kind']!='service'),
            service_ticks=sum(x['kind']=='service' for x in trace),
            active_service_ticks=sum(x['kind']=='service' and any(x['u_quarters']) for x in trace),
            zero_service_ticks=sum(x['kind']=='service' and not any(x['u_quarters']) for x in trace),
            tick_breakdown={kind:sum(x['kind']==kind for x in trace) for kind in ('startup_flush','column_probe','rehearsal','service')},
            retained_coefficient_slots=int(knowledge.G.size),identified_coefficient_slots=int(sum(knowledge.known)*n*(L+1)),
            sparse_known_nonzeros=int(np.count_nonzero(knowledge.G)),
            retained_raw_entries=sum(np.asarray(r['A']).size+np.asarray(r['B']).size for r in knowledge.raw),
            violations=sum(not x['worst_envelope_safe'] for x in trace)))
    return dict(method=method,n=n,L=L,s=s,seed=seed,regime=regime,batches=batches,
        kernel_for_independent_audit=G.tolist(),trace=plant.trace,knowledge_stats=knowledge.stats,
        cache_stats=knowledge.cache.stats,final_known_columns=np.where(knowledge.known)[0].tolist(),
        cached_equations=knowledge.raw,
        completed=sum(b['completed'] for b in batches),total_ticks=plant.clock,
        total_violations=sum(not x['worst_envelope_safe'] for x in plant.trace))


def main():
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--output',default='mission_results.json');p.add_argument('--quick',action='store_true');p.add_argument('--method',choices=METHODS);args=p.parse_args()
    dims=DIMENSIONS[:1] if args.quick else DIMENSIONS
    seeds=SEEDS[:1] if args.quick else SEEDS
    regimes=('roomy',) if args.quick else ('roomy','tight')
    methods=(args.method,) if args.method else METHODS
    results=[];tic=time.perf_counter()
    for n,L,s in dims:
      for seed in seeds:
       G=make_world(n,L,s,seed)
       for regime in regimes:
        for method in methods:
         result=run_method(G,L,s,seed,regime,method);results.append(result)
         print(json.dumps({k:result[k] for k in ('method','n','L','s','seed','regime','completed','total_ticks','total_violations')}),flush=True)
         (ROOT/args.output).write_text(json.dumps(dict(protocol_sha256=digest(ROOT/'FROZEN_PROTOCOL.md'),source_sha256=digest(__file__),results=results,elapsed_seconds=time.perf_counter()-tic),default=serial))
    summary={method:dict(streams=sum(r['method']==method for r in results),completed=sum(r['completed'] for r in results if r['method']==method),ticks=sum(r['total_ticks'] for r in results if r['method']==method),violations=sum(r['total_violations'] for r in results if r['method']==method)) for method in methods}
    (ROOT/args.output.replace('.json','_summary.json')).write_text(json.dumps(summary,indent=2))
    print(json.dumps(summary),flush=True)
if __name__=='__main__':main()

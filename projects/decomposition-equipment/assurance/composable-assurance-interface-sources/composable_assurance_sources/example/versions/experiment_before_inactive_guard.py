"""Frozen synthetic acquisition/composition experiment. Truth confined to World/replay audit."""
from dataclasses import dataclass, asdict
from collections import Counter
import json, math, time, hashlib
from pathlib import Path
import numpy as np
from calibration import calibrate

E=1/32; REF=1/128
@dataclass
class Evidence:
    id:str; kind:str; records:int; lease:int=10; valid:bool=True

class World:
    def __init__(self,n,seed,sharing):
        self.n=n; self.seed=seed; self.sharing=sharing; self.rng=np.random.default_rng(seed); self.cost=Counter(); self.archive=[]
        order=self.rng.permutation(n); self.cycles=[list(map(int,order[k:k+5])) for k in range(0,n,5)]
        self.A=np.eye(n)*.5; self.B=np.zeros((n,n))
        for c in self.cycles:
            for i,j in zip(c,c[-1:]+c[:-1]):self.B[i,j]=.25
        q=self.rng.permutation(n); self.servers=np.empty(n,int)
        for k,i in enumerate(q):self.servers[i]=k//5
        self.blocks=np.zeros(n,int)
        if sharing=='independent':
            for k,c in enumerate(self.cycles):self.blocks[c]=k
        self.p=.02; self.width=2; self.capture='request'
    def state(self,u,prev,d=.25):return np.full(self.n,d)+self.A@u+self.B@prev
    def reference(self,x):
        self.cost['reference_scalar_readings']+=len(x)
        return x+self.rng.uniform(-REF,REF,len(x))
    def physical_probe(self,j):
        z=np.zeros(self.n);u=z.copy();u[j]=.25
        xs=[self.state(z,z),self.state(u,z),self.state(z,u),self.state(z,z)]
        assert max(map(np.max,xs))<=1.5
        refs=[self.reference(x) for x in xs]; self.cost['physical_slots']+=4
        self.cost['pulse_probes']+=1;self.archive.append(('pulse',j,[x.tolist() for x in refs]))
        return refs
    def queue_trace(self,requests):
        # Causal FIFO recurrence from drained state; output includes service start/end.
        available={};trace=[]
        for channel,arrival in requests:
            server=int(self.servers[channel]);start=max(arrival,available.get(server,arrival))
            available[server]=start+1;trace.append((channel,arrival,start,start+1))
        return trace
    def fifo_probe(self,i,j):
        # Empty queue; deterministic i then j arrivals at same microtick. Each service costs one.
        trace=self.queue_trace([(i,0),(j,0)]);ends=tuple(row[3] for row in trace)
        self.cost['fifo_pair_probes']+=1;self.cost['telemetry_packets']+=2
        self.cost['queue_microticks']+=max(ends);self.archive.append(('fifo',i,j,ends))
        return ends
    def diagnostic(self,i,j,peer,kind):
        # Physically reachable .5 pulse on learned instantaneous .5 input. Boundary states .25 -> .5.
        zero=np.zeros(self.n);u=zero.copy();u[j]=.5
        old=self.state(zero,zero);new=self.state(u,zero)
        assert max(np.max(new),np.max(self.state(zero,u)))<=1.5
        # width diagnostic request/service both at same frame; capture diagnostic waits9->10.
        if kind=='width': vals=[old[i],new[i]]; actual=sum(vals[-self.width:])/self.width
        else:
            trace=self.queue_trace([(peer,9),(i,9)])
            assert trace[1][2]==10 # actual contention crosses sampling boundary
            vals=[old[i],old[i],new[i]]
            event=trace[1][1] if self.capture=='request' else trace[1][2]
            end=1+event//10
            actual=sum(vals[end-self.width+1:end+1])/self.width
        z=actual+E*(1-2*self.rng.binomial(self.width,self.p)/self.width) # packet noise; decoder uses full envelope.
        refs=[float(self.reference(np.array([v]))[0]) for v in vals]
        self.cost['diagnostic_slots']+=4;self.cost['telemetry_packets']+=1+(kind=='capture')
        self.cost['queue_microticks']+=2 if kind=='capture' else 1
        self.archive.append((kind,i,j,peer,z,refs))
        return z,refs
    def calibration(self,N):
        # Only returned values are observable decoded averaged packet residuals, not primitive draws.
        state=self.rng.bit_generator.state
        b=int(max(self.blocks))+1
        bad=self.rng.binomial(2,self.p,size=(N,b)).astype(np.int8)
        categories=(1-bad)[:,self.blocks]
        # physical reference error bounded by REF cannot change nearest residual category.
        # Batch algebra exactly implements packet minus physical-reference average.
        referr=(self.rng.uniform(-REF,REF,(N,b))+self.rng.uniform(-REF,REF,(N,b)))/2
        residual=categories*E-referr[:,self.blocks]
        decoded=np.rint(residual/E).astype(np.int8)
        assert np.array_equal(decoded,categories)
        self.cost['calibration_physical_frames']+=2*N
        self.cost['calibration_packets']+=N*self.n
        self.cost['reference_scalar_readings']+=2*N*self.n
        self.cost['calibration_queue_microticks']+=N*5
        self.cost['calibration_category_bytes']+=decoded.nbytes
        file=Path(__file__).parent/'results'/f'n{self.n}_seed{self.seed}_{self.sharing}_categories.npz'
        np.savez_compressed(file,categories=decoded)
        self.cost['retained_categories_compressed_bytes']+=file.stat().st_size
        self.archive.append(('calibration',N,hashlib.sha256(decoded.tobytes()).hexdigest(),
            {'numpy_version':np.__version__,'bit_generator_state':state,'reference_trace_regeneration':'Two independent uniform[-REF,REF] arrays averaged; full generation in World.calibration',
             'residual_sha256':hashlib.sha256(residual.tobytes()).hexdigest(),'decoded_observations_file':file.name}))
        return decoded

@dataclass
class Interface:
    A:list; B:list; fifo:list; widths:list; capture:list; blocks:list
    p_lower:float; p_upper:float; evidence:list; confidence_failure:float
    units:str='physical-load'; clock_microticks:int=10; noise_amplitude:float=E
    def sources(self,endpoints,generation=0):
        return {(generation,self.blocks[i],f) for i,r in enumerate(endpoints) for f in range(r-self.widths[i]+1,r+1)}

def discover(w):
    n=w.n;A=np.zeros((n,n));B=A.copy()
    for j in range(n):
        refs=w.physical_probe(j)
        for lag,M in [(1,A),(2,B)]:
            diff=refs[lag]-refs[0]
            for i in range(n):
                possibilities=[v for v in (0,.25,.5) if abs(diff[i]-.25*v)<=2*REF+1e-12]
                if len(possibilities)!=1:raise ValueError('physical ambiguity retained: no certificate')
                M[i,j]=possibilities[0]
    fifo=list(range(n))
    for i in range(n):
        for j in range(i+1,n):
            if w.fifo_probe(i,j)[1]==2:
                old=fifo[j];new=fifo[i];fifo=[new if x==old else x for x in fifo]
    widths=[];captures=[]
    for i in range(n):
        js=np.where(A[i]==.5)[0]
        peers=[j for j in range(n) if j!=i and fifo[j]==fifo[i]]
        if not len(js) or not peers:raise ValueError('safe separator unavailable: abstain')
        j=int(js[0]);peer=peers[0];z,refs=w.diagnostic(i,j,peer,'width')
        candidates=[width for width in (1,2) if abs(z-np.mean(refs[-width:]))<=E+REF+1e-12]
        if len(candidates)!=1:raise ValueError('width ambiguity')
        width=candidates[0];widths.append(width)
        z,refs=w.diagnostic(i,j,peer,'capture')
        choices=[name for name,end in [('request',1),('service',2)] if abs(z-np.mean(refs[end-width+1:end+1]))<=E+REF+1e-12]
        if len(choices)!=1:raise ValueError('capture ambiguity')
        captures.append(choices[0])
    obs=w.calibration(1_000_000)
    stats=calibrate(obs,delta_rate=.002,delta_block=.002)
    return A,B,fifo,widths,captures,stats

class Ledger:
    def __init__(self,budget=.05):self.budget=budget;self.charges={};self.exposed=set()
    @property
    def used(self):return sum(self.charges.values())
    def reserve(self,tokens,p):
        fresh=set(tokens)-self.charges.keys()
        if fresh & self.exposed:raise ValueError('retroactive charge')
        if self.used+len(fresh)*p>self.budget+1e-12:return False
        self.charges.update({t:p for t in fresh});return True
    def expose(self,tokens):
        if not set(tokens)<=self.charges.keys():raise ValueError('uncharged exposure')
        self.exposed.update(tokens)

class DependencyCache:
    """Original evidence retained; all downstream caches dirty across arbitrary updates."""
    def __init__(self,n):
        self.factors={f'physical{i}':True for i in range(n)}|{'protocol':True,'sources':True,'graph':True}
        self.dependencies={f'cell{i}':{f'physical{i}','protocol','graph'} for i in range(n)}
        self.dependencies['mission']=set(self.dependencies)|{'sources','graph'}
        self.cache={};self.dirty=set(self.dependencies);self.ops=0
    def change(self,key,value):
        self.factors[key]=value;front={key}
        while front:
            more={k for k,ds in self.dependencies.items() if ds&front};self.dirty|=more;front=more
    def query(self,key):
        if key in self.factors:return self.factors[key]
        if key in self.dirty or key not in self.cache:
            vals=[self.query(d) for d in sorted(self.dependencies[key])]
            self.cache[key]=all(vals);self.dirty.discard(key);self.ops+=1
        return self.cache[key]
    def dense(self,key):
        if key in self.factors:return self.factors[key]
        vals=[self.dense(d) for d in sorted(self.dependencies[key])];return all(vals)

def validate_interface(interface):
    n=len(interface.A)
    if n==0 or len(interface.B)!=n or len(interface.blocks)!=n:return False
    if len(interface.widths)!=n or len(interface.capture)!=n or len(interface.fifo)!=n:return False
    if not 0<=interface.p_lower<=interface.p_upper<=1:return False
    for a,b in zip(interface.A,interface.B):
        if len(a)!=n or len(b)!=n or any(v not in (0,.25,.5) for v in a+b):return False
        if sum(a)+sum(b)>.75+1e-12:return False
    return all(w==2 for w in interface.widths) and all(c=='request' for c in interface.capture)

def polling_trace(interface,order):
    # Learned protocol observer, not world partition oracle. Drained queue required.
    available={};trace=[];endpoints=[None]*len(order)
    for i in order:
        arrival=-10;server=interface.fifo[i];start=max(arrival,available.get(server,arrival))
        available[server]=start+1
        endpoint=arrival//10 if interface.capture[i]=='request' else start//10
        endpoints[i]=endpoint;trace.append((i,arrival,start,start+1,endpoint))
    if max(row[3] for row in trace)>0:raise ValueError('deadline exceeded')
    return endpoints,trace

def check(interface,endpoints,lease_end,cache=None,conservative=False):
    if not validate_interface(interface):return False,'invalid_native_interface',0
    if lease_end<3:return False,'lease_does_not_cover_tail',0
    if cache and not cache.query('mission'):return False,'support_invalid',0
    tokens=interface.sources(endpoints)
    if conservative:tokens={(0,i,f) for i,r in enumerate(endpoints) for f in range(r-1,r+1)}
    bound=len(tokens)*interface.p_upper
    return bound<=.05,'certified' if bound<=.05 else 'global_source_budget',bound

def replay(w,interface,ends,d,seed):
    ledger=Ledger();tokens=interface.sources(ends)
    if not ledger.reserve(tokens,interface.p_upper):return {'committed':False,'jobs':0}
    ledger.expose(tokens);rng=np.random.default_rng(seed)
    xi={t:E if rng.random()>=w.p else -E for t in tokens}
    z=np.array([d+np.mean([xi[(0,interface.blocks[i],f)] for f in range(r-1,r+1)]) for i,r in enumerate(ends)])
    u=(z-E<=.75).astype(float);zero=np.zeros(w.n)
    trajectory=[w.state(u,zero,d),w.state(u,u,d),w.state(zero,u,d),w.state(zero,zero,d)]
    return {'committed':True,'jobs':int(sum(u)),'peak':float(max(map(np.max,trajectory))),'violations':int(any(np.max(x)>1.5+1e-12 for x in trajectory)),'charged':ledger.used,'tokens':len(tokens)}

# main supplied after calibration API is finalized.
def coherent(interface,ends,lease,factors):
    # Whole interface recomputation, separate from cached query/ledger implementation.
    coherent.rows_checked=0;coherent.incidences_checked=0
    if lease<3 or not all(factors.values()):return False
    n=len(ends)
    if len(interface.A)!=n or len(interface.B)!=n or len(interface.capture)!=n:return False
    if any(len(row)!=n for row in interface.A+interface.B):return False
    if any(v not in (0,.25,.5) for row in interface.A+interface.B for v in row):return False
    if any(w!=2 for w in interface.widths):return False
    if not 0<=interface.p_lower<=interface.p_upper<=1:return False
    for a,b in zip(interface.A,interface.B):
        coherent.rows_checked+=1
        if sum(a)+sum(b)>.75+1e-12:return False
    incidence=[]
    for i in range(len(ends)):
        if interface.capture[i]!='request':return False
        for f in range(ends[i]-interface.widths[i]+1,ends[i]+1):
            coherent.incidences_checked+=1
            key=(interface.blocks[i],f)
            if key not in incidence:incidence.append(key)
    return len(incidence)*interface.p_upper<=.05

def tests():
    l=Ledger();assert l.reserve({(0,0,0),(0,0,1)},.024);l.expose(l.charges)
    assert l.reserve({(0,0,0)},.024) and abs(l.used-.048)<1e-12
    assert not l.reserve({(0,0,2)},.024)
    try:l.expose({(9,9,9)});raise AssertionError('uncharged allowed')
    except ValueError:pass
    l.exposed.add((3,3,3))
    try:l.reserve({(3,3,3)},.001);raise AssertionError('late charge allowed')
    except ValueError:pass
    cache=DependencyCache(20);rng=np.random.default_rng(302);checks=0
    keys=list(cache.factors);qs=list(cache.dependencies)
    for _ in range(3000):
        for _ in range(int(rng.integers(1,5))):cache.change(str(rng.choice(keys)),bool(rng.integers(2)))
        q=str(rng.choice(qs));assert cache.query(q)==cache.dense(q);checks+=1
    return {'dirty_cache_multiupdate_checks':checks,'ledger_duplicates_and_no_refund':'pass','retroactive_exposure_rejected':True}

def run():
    output=Path(__file__).parent/'results';output.mkdir(exist_ok=True)
    results=[]
    for n in (5,10,20):
      for seed in (731,947):
       for sharing in ('global','independent'):
        start=time.perf_counter();w=World(n,seed,sharing)
        A,B,fifo,widths,caps,stats=discover(w)
        if stats['status']!='certified':raise ValueError(stats['status'])
        blocks=[None]*n
        for b,g in enumerate(stats['groups']):
            for i in g:blocks[i]=b
        interface=Interface(A.tolist(),B.tolist(),fifo,widths,caps,blocks,*stats['p_interval'],
            [asdict(Evidence(k,t,r)) for k,t,r in [('physical','bounded_reference',4*n),('protocol','causal_fifo_window',n*(n-1)//2+2*n),('sources','fixed_sample',1_000_000),('graph','supplied_candidate_universe',1)]],.004)
        assert np.allclose(A,w.A) and np.allclose(B,w.B) # auditor only; not input to discovery.
        assert max(np.sum(A+B,axis=1))<=.75
        # Recover cycles solely from discovered lag adjacency, not world's cluster labels.
        remaining=set(range(n));cycles=[]
        while remaining:
            c=[];i=min(remaining)
            while i not in c:
                c.append(i);remaining.remove(i);i=int(np.flatnonzero(B[i])[0])
            cycles.append(c)
        aligned,original_trace=polling_trace(interface,list(range(n)))
        reordered,reordered_trace=polling_trace(interface,list(reversed(range(n))))
        assert original_trace!=reordered_trace and aligned==reordered
        # Audit real FIFO event recurrence agrees with learned observer on both orders.
        assert [t[:4] for t in original_trace]==w.queue_trace([(i,-10) for i in range(n)])
        assert [t[:4] for t in reordered_trace]==w.queue_trace([(i,-10) for i in reversed(range(n))])
        split=aligned.copy()
        for c in cycles:
            for i in c[3:]:split[i]=0
        cache=DependencyCache(n);outcomes=[]
        for name,ends,lease,updates in [
            ('aligned',aligned,10,[]),('reordered_same_windows',reordered,10,[]),
            ('split_windows',split,10,[]),('expiry_before_tail',aligned,2,[]),
            ('source_retracted',aligned,10,[('sources',False)]),
            ('multiple_retractions',aligned,10,[('physical0',False),('protocol',False)]),
            ('partial_restore',aligned,10,[('sources',True),('physical0',True)]),
            ('restore',aligned,10,[('protocol',True)]),
            ('graph_retracted',aligned,10,[('graph',False)]),
            ('graph_restored',aligned,10,[('graph',True)])]:
            for key,value in updates:cache.change(key,value)
            before=cache.ops;accepted,reason,bound=check(interface,ends,lease,cache)
            full=coherent(interface,ends,lease,cache.factors)
            assert accepted==full
            inc=cache.query('mission') and lease>=3 and len(interface.sources(ends))*interface.p_upper<=.05
            assert accepted==inc
            record={'variant':name,'accepted':accepted,'reason':reason,'operational_union_bound':bound,
                    'full_coherent':full,'same_support_incremental':inc,'cache_nodes_recomputed':cache.ops-before,
                    'coherent_physical_rows_checked':coherent.rows_checked,'coherent_source_incidences_checked':coherent.incidences_checked,'conservative_accepts':check(interface,ends,lease,cache,True)[0]}
            if accepted:record['nominal']=replay(w,interface,ends,.5,seed+100)
            if name in ('aligned','reordered_same_windows'):
                record['polling_trace']=original_trace if name=='aligned' else reordered_trace
                record['native_interface_rows_revalidated']=n
            outcomes.append(record)
        key=f'n{n}_seed{seed}_{sharing}'
        (output/f'{key}_evidence.json').write_text(json.dumps(w.archive))
        (output/f'{key}_interface.json').write_text(json.dumps(asdict(interface),indent=2))
        row={'id':key,'n':n,'seed':seed,'sharing_world_audit_only':sharing,'learned_blocks':len(stats['groups']),
             'calibration':stats,'costs':dict(w.cost),'outcomes':outcomes,'elapsed_seconds':time.perf_counter()-start,
             'evidence_archive_bytes':(output/f'{key}_evidence.json').stat().st_size,
             'interface_bytes':(output/f'{key}_interface.json').stat().st_size}
        results.append(row);print(key,stats['p_interval'],[o['accepted'] for o in outcomes],flush=True)
    summary={'software_tests':tests(),'family_runs':results,'protocol_sha256':hashlib.sha256((Path(__file__).parent/'PROTOCOL.md').read_bytes()).hexdigest()}
    (output/'results.json').write_text(json.dumps(summary,indent=2));return summary

if __name__=='__main__':run()

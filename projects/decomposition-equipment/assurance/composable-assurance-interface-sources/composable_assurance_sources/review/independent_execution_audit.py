"""Artifact/math audit. Deliberately imports no implementation modules."""
import json, math, hashlib, itertools
from fractions import Fraction as F
from pathlib import Path
import numpy as np
ROOT=Path(__file__).resolve().parents[1]; R=ROOT/'example/results'
def equal(a,b):
    assert abs(a-b)<1e-12,(a,b)
def main():
    result=json.loads((R/'results.json').read_text()); cases=[]; total=0
    assert len(result['family_runs'])==12
    for row in result['family_runs']:
        name=row['id'];n=row['n'];N=1000000
        interface=json.loads((R/f'{name}_interface.json').read_text())
        archive=json.loads((R/f'{name}_evidence.json').read_text())
        a=np.load(R/f'{name}_categories.npz')['categories'];assert a.shape==(N,n)
        assert set(np.unique(a))<={-1,0,1}
        assert hashlib.sha256(a.tobytes()).hexdigest()==archive[-1][2]
        # Reproduce physical-reference residual from persisted RNG state, independently.
        gen=np.random.default_rng(row['seed']);order=gen.permutation(n)
        physical_blocks=np.zeros(n,dtype=int)
        if row['sharing_world_audit_only']=='independent':
            for b in range(n//5):physical_blocks[order[5*b:5*b+5]]=b
        gen.bit_generator.state=archive[-1][3]['bit_generator_state'];b=max(physical_blocks)+1
        draws=gen.binomial(2,.02,size=(N,b)).astype(np.int8)
        refs=(gen.uniform(-1/128,1/128,(N,b))+gen.uniform(-1/128,1/128,(N,b)))/2
        residual=((1-draws)/32-refs)[:,physical_blocks]
        assert hashlib.sha256(residual.tobytes()).hexdigest()==archive[-1][3]['residual_sha256']
        assert np.array_equal(np.rint(residual*32).astype(np.int8),a)
        estimates=np.count_nonzero(a==0,axis=0)/(2*N)+np.count_nonzero(a==-1,axis=0)/N
        radius=math.sqrt(math.log(1000*n)/(2*N))
        lo=max(.01,max(estimates)-radius);hi=min(.03,min(estimates)+radius)
        equal(lo,interface['p_lower']);equal(hi,interface['p_upper'])
        assert lo<=.02<=hi and 2*hi<.05 and 1-(1-lo)**3>.05
        for i,j in itertools.combinations(range(n),2):
            assert (interface['blocks'][i]==interface['blocks'][j])==np.array_equal(a[:,i],a[:,j])
        # Recover physical matrices from archived reference records, never world matrices.
        for kind,j,refs in archive[:n]:
            assert kind=='pulse'
            for lag,key in [(1,'A'),(2,'B')]:
                for i in range(n):
                    matches=[v for v in (0,.25,.5) if abs(refs[lag][i]-refs[0][i]-.25*v)<=1/64+1e-12]
                    assert matches==[interface[key][i][j]]
        # Every FIFO pair diagnostic agrees with exported equivalence relation.
        for rec in archive[n:n+n*(n-1)//2]:
            _,i,j,ends=rec;assert (ends[1]==2)==(interface['fifo'][i]==interface['fifo'][j])
        assert interface['widths']==[2]*n and interface['capture']==['request']*n
        # Independently interpret all recorded width/capture diagnostics.
        start=n+n*(n-1)//2
        for kind,i,j,peer,z,refs in archive[start:-1]:
            if kind=='width':assert [k for k in (1,2) if abs(z-sum(refs[-k:])/k)<=5/128+1e-12]==[2]
            else:assert [k for k,end in [('request',1),('service',2)] if abs(z-sum(refs[end-1:end+1])/2)<=5/128+1e-12]==['request']
        # Independently reconstruct actual forward/reverse FIFO service traces.
        traces=[]
        for variant,order in [('aligned',list(range(n))),('reordered_same_windows',list(reversed(range(n))))]:
            available={};trace=[]
            for channel in order:
                server=interface['fifo'][channel]
                start=max(-10,available.get(server,-10));available[server]=start+1
                trace.append([channel,-10,start,start+1,-1])
            assert trace==next(o for o in row['outcomes'] if o['variant']==variant)['polling_trace']
            assert max(t[3] for t in trace)<=-5
            traces.append(trace)
        assert traces[0]!=traces[1]
        blocks=len(set(interface['blocks']));active=True
        for o in row['outcomes']:
            v=o['variant']
            good=v in ('aligned','reordered_same_windows','restore','graph_restored')
            expected=good and 2*blocks*hi<=.05
            assert o['accepted']==o['full_coherent']==o['same_support_incremental']==expected
            assert not o['conservative_accepts']
            if expected:
                nominal=o['nominal'];assert nominal['jobs']==n and nominal['violations']==0;equal(nominal['peak'],1.25)
                equal(nominal['charged'],2*blocks*hi)
            total+=1
        c=row['costs'];assert c['reference_scalar_readings']==2*N*n+4*n*n+5*n
        assert c['calibration_packets']==N*n and c['calibration_physical_frames']==2*N
        assert c['fifo_pair_probes']==n*(n-1)//2 and c['physical_slots']==4*n and c['diagnostic_slots']==8*n
        cases.append({'id':name,'interval':[lo,hi],'aligned_bound':2*blocks*hi,'split_bound':3*blocks*hi,'split_exact_lower':1-(1-lo)**3,'accepted':sum(o['accepted'] for o in row['outcomes'])})
    # Rational physical execution, no simulator import, including full delayed tail.
    physical=[]
    for background in (F(1,2),F(77,100)):
      for split in (False,True):
        windows=[(-2,-1)]*5 if not split else [(-2,-1)]*3+[(-1,0)]*2
        frames=sorted(set(sum(windows,())));risk=F(0)
        for bits in itertools.product((0,1),repeat=len(frames)):
            signs=dict(zip(frames,[F(1-2*b,32) for b in bits]));prob=F(1)
            for bit in bits:prob*=F(1,50) if bit else F(49,50)
            commands=[int(background+sum(signs[f] for f in w)/2-F(1,32)<=F(3,4)) for w in windows]
            prev=[0]*5;hazard=False
            for current in (commands,commands,[0]*5,[0]*5):
                states=[background+F(current[i],2)+F(prev[(i-1)%5],4) for i in range(5)]
                hazard|=max(states)>F(3,2);prev=current
            if hazard:risk+=prob
        expected=F(0) if background==F(1,2) else (F(7351,125000) if split else F(99,2500))
        assert risk==expected;physical.append({'background':float(background),'split':split,'risk':float(risk),'exact':str(risk)})
    online=json.loads((R/'online_regressions.json').read_text()) if (R/'online_regressions.json').exists() else None
    if online:
        for r in online['cases']:
            d=r['background'];equal(r['risk_charge_retained'],.046)
            if r['detected_before_second_actuation']:
                equal(r['peak'],max(d+.5,d+.25,d));assert r['completed_two_slot_jobs']==0 and r['interrupted_jobs']==5
            else:equal(r['second_slot_peak'],d+.75);assert r['status']=='assurance_loss' and r['physical_violation']
    out={'independent_of_implementation_imports':True,'acquisition_artifact_replays':12,'outcome_comparisons':total,'independent_polling_traces':24,'experiment_sha256':hashlib.sha256((ROOT/'example/experiment.py').read_bytes()).hexdigest(),'results_sha256':hashlib.sha256((R/'results.json').read_bytes()).hexdigest(),'cases':cases,'physical_exact':physical,'online_checked':online is not None,'status':'PASS within recorded scope'}
    (ROOT/'review/independent_execution_audit_results.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
if __name__=='__main__':main()

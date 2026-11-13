"""Independent source-to-certificate check. Does not import author scripts."""
from pathlib import Path
from itertools import product, combinations
from fractions import Fraction as F
from collections import defaultdict
import json, math
import numpy as np
BASE=Path(__file__).resolve().parents[1]/'examples'
PAIRS=list(product(range(2),repeat=2))
def load(stem,suffix):return json.loads((BASE/(stem+'_'+suffix+'.json')).read_text())
def prediction(c,pol,coords,variant='learned'):
    masks=c['masks']; tab=[[F(x) for x in r] for r in c['local']]; lam=F(c['shared_weight'])
    def local(z,y,a,i):
        vals=y+z+a; key=0
        for k in masks[i]:key=2*key+vals[k]
        return tab[i][key]
    def law(z,y):
        a=tuple(1-v for v in y) if pol=='clear' else y if pol=='busy' else (y[1],1-y[0]) if pol=='crossed' else tuple(x^v for x,v in zip(z,y))
        p,q=(local(z,y,a,i) for i in range(2))
        if variant=='no_memory':p=sum(local((b,z[1]),y,a,0) for b in range(2))/2;q=sum(local((z[0],b),y,a,1) for b in range(2))/2
        if variant=='no_message':p=sum(local(z,(y[0],b),a,0) for b in range(2))/2;q=sum(local(z,(b,y[1]),a,1) for b in range(2))/2
        l=0 if variant=='independent' else lam
        both=l*min(p,q)+(1-l)*p*q
        ans=[1-p-q+both,q-both,p-both,both]
        assert min(ans)>=0 and sum(ans)==1
        return ans
    laws={(z,y):law(z,y) for z,y in product(PAIRS,repeat=2)}
    den=math.lcm(*(v.denominator for row in laws.values() for v in row))
    weights={s:[int(v*den) for v in row] for s,row in laws.items()}
    nu=[F(x) for x in c['initial']]; dd=math.lcm(*(v.denominator for v in nu)); assert sum(nu)==1 and min(nu)>=0
    # Append selected observed bits chronologically, rather than assigning word positions.
    def append(word,y,t):
        for port in range(2):
            if 2*t+port in coords:word=2*word+y[port]
        return word
    mass={(z,y,append(0,y,0)):int(nu[j]*dd) for j,(z,y) in enumerate(product(PAIRS,repeat=2))}
    for t in range(1,max(coords)//2+1):
        nxt=defaultdict(int)
        for (z,y,w),v in mass.items():
            for yy,k in zip(PAIRS,weights[z,y]):nxt[y,yy,append(w,yy,t)]+=v*k
        mass=nxt;dd*=den
    vals=[0]*(2**len(coords))
    for (z,y,w),v in mass.items():vals[w]+=v
    assert sum(vals)==dd
    return [F(v,dd) for v in vals]
def monitor_prediction(c,pol,symbol):
    # Obtain exact one-step laws via the same frozen tables, separately from projection DP.
    tab=[[F(v) for v in row] for row in c['local']];lam=F(c['shared_weight']);nu=[F(v) for v in c['initial']]
    trans={}
    for z,y in product(PAIRS,repeat=2):
        a=tuple(1-v for v in y) if pol=='clear' else y if pol=='busy' else (y[1],1-y[0]) if pol=='crossed' else tuple(x^v for x,v in zip(z,y))
        probs=[]
        for i in range(2):
            key=0
            for k in c['masks'][i]:key=key*2+(y+z+a)[k]
            probs.append(tab[i][key])
        p,q=probs;b=lam*min(p,q)+(1-lam)*p*q
        trans[z,y]=[1-p-q+b,q-b,p-b,b]
    denominator=math.lcm(*(v.denominator for row in trans.values() for v in row)); weights={key:[int(v*denominator) for v in row] for key,row in trans.items()}
    initialden=math.lcm(*(v.denominator for v in nu));cdf=[F(0)]
    for limit in range(1,11):
        # Compute P(maxrun < limit) by killing every path at its first prohibited run.
        state={}
        for j,(z,y) in enumerate(product(PAIRS,repeat=2)):
            run=int(y==symbol)
            if run<limit:state[z,y,run]=int(nu[j]*initialden)
        for _ in range(8):
            nxt=defaultdict(int)
            for (z,y,run),mass in state.items():
                for yy,w in zip(PAIRS,weights[z,y]):
                    newrun=run+1 if yy==symbol else 0
                    if newrun<limit:nxt[y,yy,newrun]+=mass*w
            state=nxt
        cdf.append(F(sum(state.values()),initialden*denominator**8))
    assert cdf[-1]==1
    return [cdf[k+1]-cdf[k] for k in range(10)]
outputs=[]
for stem in ['sparse_service','joint_time_service','monitor_service']:
    result=load(stem,'results'); candidate=load(stem,'frozen_candidate'); hs=load(stem,'holdout_histograms'); ps=load(stem,'exact_predictions');N=result['heldout_episodes_per_controller'];r=F(result['confidence_radius']);worst=F(0);checked=0
    for group,preds in zip(hs,ps):
        pol=group['policy'];assert pol==preds['policy']
        data=np.load(BASE/(stem+'_holdout_'+pol+'.npz'));raw=data['readouts'];flat=raw[:,1:].reshape(N,-1);aa=data['actions'];assert raw.shape==(N,10,2)
        for t in range(8):
            z,y=raw[:,t],raw[:,t+1]
            expected=1-y if pol=='clear' else y if pol=='busy' else np.stack((y[:,1],1-y[:,0]),axis=1) if pol=='crossed' else z^y
            assert np.array_equal(expected,aa[:,t])
        expected_coords=list(combinations(range(18),3)) if stem=='sparse_service' else [tuple(j for t in ts for j in (2*t,2*t+1)) for ts in combinations(range(9),3)]
        assert [tuple(row[0]) for row in group['histograms']]==expected_coords
        for j,((coords,counts),(pc,nums,den)) in enumerate(zip(group['histograms'],preds['probabilities'])):
            assert coords==pc;word=np.zeros(N,dtype=int)
            for k in coords:word=2*word+flat[:,k]
            assert np.array_equal(np.bincount(word,minlength=len(counts)),counts)
            q=[F(v,den) for v in nums]; assert sum(q)==1 and min(q)>=0
            fit=sum(abs(F(v,N)-p) for v,p in zip(counts,q))/2;worst=max(worst,fit)
            # All stronger-run distributions; 5 dispersed weak-run distributions/policy.
            if stem!='sparse_service' or j in [0,41,315,600,815]:assert prediction(candidate,pol,coords)==q;checked+=1
        for name,ab in result['ablations'].items():
            if ab['policy']!=pol:continue
            coords=ab['coordinates'];counts=next(v for c,v in group['histograms'] if c==coords)
            q=prediction(candidate,pol,coords,name);lower=max(F(0),sum(abs(F(v,N)-p) for v,p in zip(counts,q))/2-r)
            assert lower==F(ab['exact_heldout_TV_lower_bound']) and lower>F(1,20)
    if stem=='monitor_service':
        assert candidate==load('joint_time_service','frozen_candidate')
        assert result['fresh_validation_seeds']==[202610301611+i for i in range(4)]
        monitor_groups=load(stem,'monitor_results')
        for mg in monitor_groups:
            pol=mg['policy'];raw=np.load(BASE/(stem+'_holdout_'+pol+'.npz'))['readouts'][:,1:]
            for mr in mg['max_run_monitors']:
                symbol=tuple(mr['symbol']);match=np.all(raw==symbol,axis=2);maxrun=np.zeros(N,dtype=int)
                # Independent window test, not the author's running-counter histogram algorithm.
                for width in range(1,10):
                    occurs=np.zeros(N,dtype=bool)
                    for start in range(10-width):occurs|=np.all(match[:,start:start+width],axis=1)
                    maxrun[occurs]=width
                counts=np.bincount(maxrun,minlength=10);assert counts.tolist()==mr['counts']
                q=monitor_prediction(candidate,pol,symbol)
                assert q==[F(v,mr['prediction_denominator']) for v in mr['prediction_numerators']]
                fit=sum(abs(F(int(v),N)-p) for v,p in zip(counts,q))/2;assert fit==F(mr['TV_fit']);worst=max(worst,fit)
        assert result['cumulative_study_episodes']==500000
    s=result['projection_alphabet'];expo=2*N*r*r
    bound=F(4*(result['projection_count']*(2**s-2)+(4*(2**10-2) if stem=='monitor_service' else 0)))/sum((expo**j/F(math.factorial(j)) for j in range(100)),F(0))
    assert bound==F(result['exact_confidence_failure_bound'])
    assert bound<F(1,20) and worst+r<F(1,20)
    assert abs(float(worst+r)-result['uniform_certificate'])<1e-15
    outputs.append({'run':stem,'raw_histograms_checked':4*result['projection_count'],'additional_monitor_histograms_and_predictions_checked':16 if stem=='monitor_service' else 0,'independent_exact_DP_checks':checked,'certificate_exact':str(worst+r),'certificate':float(worst+r),'failure_bound':float(bound)})
print(json.dumps(outputs,indent=2))

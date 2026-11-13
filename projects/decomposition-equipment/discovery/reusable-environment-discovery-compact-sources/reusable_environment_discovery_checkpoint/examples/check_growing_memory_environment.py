#!/usr/bin/env python3
"""Discover reusable finite-input-memory environments without enumerating global state.

Run: OPENBLAS_NUM_THREADS=2 python check_growing_memory_environment.py --sizes 12 24 48 96
Input records contain actions/readouts only. Hidden truth is isolated to generate()/audit().
No inference or statistical certificate uses simulator parameters or a probability grid.
The support certificate requires the explicit integer-polynomial + symmetric binary-noise
structural universe. It is deliberately NOT a model-free certificate of that universe.
"""
import argparse, hashlib, itertools, json, math, os, time
from fractions import Fraction
from pathlib import Path
import numpy as np

L = 4

def dump(path, x):
    Path(path).write_text(json.dumps(x, indent=2, sort_keys=True) + '\n')

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def run_columns(actions, stop=None):
    """Known search dictionary, not sufficient state: all channel run indicators 1..L."""
    stop = len(actions) if stop is None else stop
    n = actions.shape[1]
    x = np.empty((stop-L, n*(L+1)), dtype=np.float32)
    x[:, :n] = actions[L:stop]
    mask = np.ones((stop-L,n), dtype=bool)
    for k in range(1,L+1):
        mask &= actions[L-k:stop-k] == 1
        x[:, k*n:(k+1)*n] = mask
    return x

def evaluate_terms(actions, models):
    x = run_columns(actions)
    out = np.empty((len(x),len(models)), dtype=np.int16)
    for i,m in enumerate(models):
        val = np.full(len(x),m['intercept'],dtype=np.float64)
        for c,w in m['linear']:
            val += w*x[:,c]
        for a,b,w in m['interactions']:
            val += w*x[:,a]*x[:,b]
        out[:,i] = np.rint(val).astype(np.int16)
    return out

def true_models(n, seed):
    rng=np.random.default_rng(seed)
    order=rng.permutation(n)
    models=[]
    for i in range(n):
        p=int(order[i]); j=int(order[(i+1)%n]); k=int(order[(i+3)%n])
        r=1+((i+1)%L); s=1+((i+3)%L)
        models.append({'intercept':0,'linear':[[p,2]]+
                       [[h*n+j,2] for h in range(1,r+1)]+
                       [[h*n+k,-2] for h in range(1,s+1)],
                       'interactions':[[p,h*n+j,1] for h in range(1,r+1)]})
    members=list(map(int,rng.permutation(n))); groups=[]; pos=0; gi=0
    while pos<n:
        b=2 if gi%3==1 else 3
        b=min(b,n-pos)
        if n-pos-b==1: b=2
        g=sorted(members[pos:pos+b]); pos+=b
        kind='pair' if b==2 else ('triple_only' if gi%3==0 else 'common')
        if b==1: kind='single'
        rows=list(itertools.product((-1,1),repeat=b)); probs=[]
        for z in rows:
            if kind=='pair': p=(1+.43*z[0]*z[1])/4
            elif kind=='triple_only': p=(1+.37*math.prod(z))/8
            elif kind=='common': p=.39/8 + (.61/2 if len(set(z))==1 else 0)
            else: p=.5
            probs.append(p)
        groups.append({'members':g,'kind':kind,'rows':rows,'probabilities':probs})
        gi+=1
    return models,groups

def generate(n, ntrain, nvalidate, ncal, seed, out):
    rng=np.random.default_rng(seed+101)
    total=ntrain+nvalidate+ncal
    actions=rng.choice(np.array([-1,1],dtype=np.int8),size=(total+L,n))
    models,groups=true_models(n,seed)
    y=evaluate_terms(actions,models)
    for g in groups:
        rows=np.asarray(g['rows'],dtype=np.int16)
        ix=rng.choice(len(rows),size=total,p=g['probabilities'])
        y[:,g['members']]+=rows[ix]
    np.savez_compressed(out/'records.npz',actions=actions,readouts=y)
    dump(out/'public_manifest.json',{'channels':n,'action_alphabet':[-1,1],
        'readout_alphabet':'integer','communication_permissions':'broadcast labeled actions and certified joint-event projections',
        'memory_search_budgets':list(range(L+1)), 'max_innovation_block':3,
        'train_rows':ntrain,'validation_rows':nvalidate,'calibration_rows':ncal,
        'structural_universe':'integer multilinear response degree <=5 over last4/current binary actions; fresh independent-in-time residual vectors, coordinate symmetric +/-1; unknown independent blocks size<=3',
        'probability_grid_assumed':False,
        'promised_minimum_finest_block_split_TV_gap':.18,
        'gap_is_structural_premise_not_learned_fact':True})
    return models,groups

def discover_mean(actions,y,ntrain):
    n=y.shape[1]; x=run_columns(actions,stop=ntrain+L)
    # Orthogonal run-history contrasts, variance 2^{-(k-1)} under randomized inputs.
    h=np.empty_like(x);h[:,:n]=x[:,:n]
    for k in range(1,L+1):
        prev=1 if k==1 else x[:,(k-1)*n:k*n]
        h[:,k*n:(k+1)*n]=2*x[:,k*n:(k+1)*n]-prev
    scores=(h.T@y[:ntrain].astype(np.float32))/ntrain
    for k in range(1,L+1): scores[k*n:(k+1)*n]*=2**(k-1)
    models=[]; counters={'screened_feature_output_pairs':int(scores.size),'local_design_columns':0}
    for i in range(n):
        cols=np.flatnonzero(np.abs(scores[:,i])>.5).tolist()
        current=[c for c in cols if c<n]; history=[c for c in cols if c>=n]
        products=[(a,b) for a in current for b in history]
        design=np.column_stack([np.ones(ntrain)]+[x[:,c] for c in cols]+
                               [x[:,a]*x[:,b] for a,b in products])
        coeff=np.linalg.lstsq(design,y[:ntrain,i],rcond=None)[0]
        rounded=np.rint(coeff).astype(int)
        linear=[[int(c),int(w)] for c,w in zip(cols,rounded[1:1+len(cols)]) if w]
        inter=[[int(a),int(b),int(w)] for (a,b),w in zip(products,rounded[1+len(cols):]) if w]
        models.append({'intercept':int(rounded[0]),'linear':linear,'interactions':inter})
        counters['local_design_columns']+=design.shape[1]
    return models,counters

def response_degree(model,n):
    deg=max([0]+[1 if c<n else c//n for c,w in model['linear']]+[1+b//n for a,b,w in model['interactions']])
    assert all(a<n and b>=n for a,b,w in model['interactions'])
    return deg

def quotient_for_channel(models,n,channel):
    """Learn recursive predictive memory from fitted response functions, not lag mask.
    Two suffixes initially agree when every response term sees equal history features.
    Refine by deterministic shift under both possible next actions. Unreachable suffixes
    are absent: all 2^L binary suffixes are reachable under exploration.
    """
    lags=sorted({c//n for m in models for c,w in m['linear'] if c>=n and c%n==channel}|
                {b//n for m in models for a,b,w in m['interactions'] if b%n==channel})
    words=list(itertools.product((-1,1),repeat=L)) # oldest to newest
    index={w:i for i,w in enumerate(words)}
    signatures=[tuple(int(all(v==1 for v in w[-k:])) for k in lags) for w in words]
    def label(ss):
        seen={}; return [seen.setdefault(s,len(seen)) for s in ss]
    partition=label(signatures); iterations=0
    while True:
        signatures=[(partition[i],*(partition[index[w[1:]+(a,)]] for a in (-1,1))) for i,w in enumerate(words)]
        new=label(signatures); iterations+=1
        if new==partition: break
        partition=new
    reps=[partition.index(i) for i in range(max(partition)+1)]
    trans=[[partition[index[words[r][1:]+(a,)]] for a in (-1,1)] for r in reps]
    # Minimality witness is ordinary deterministic partition refinement from complete
    # current-response signatures. Coefficients guarantee these features are relevant.
    return {'channel':channel,'selected_order':max(lags,default=0),'suffix_states':2**L,
            'quotient_states':len(reps),'partition':partition,'representatives':[words[r] for r in reps],
            'transition_minus_plus':trans,'refinement_rounds':iterations}

def support_validate(actions,y,models,ntrain,nvalidate,delta=.002):
    pred=evaluate_terms(actions,models); n=y.shape[1]
    assert max(response_degree(m,n) for m in models)<=L+1
    # Frozen before validation. Independent action windows are L+1 apart.
    ids=np.arange(ntrain+L,ntrain+nvalidate,L+1)
    residual=y[ids].astype(np.int32)-pred[ids].astype(np.int32)
    violations=np.sum(np.abs(residual)!=1,axis=0)
    degree=L+1
    failure_bound=min(1.,n*math.exp(-len(ids)*2**(-degree-1)))
    return pred,{'independent_windows':len(ids),'stride':L+1,'per_output_violations':violations.tolist(),
        'passed':bool(not violations.any()),'false_acceptance_bound':failure_bound,
        'specified_delta':delta,'scope':'exact response equality within declared integer degree<=5 / symmetric binary-noise universe, not validation of universe'}

def all_moments(residual):
    N,n=residual.shape
    assert set(np.unique(residual)).issubset({-1,1})
    bits=[int.from_bytes(np.packbits(residual[:,i]<0,bitorder='little').tobytes(),'little') for i in range(n)]
    m={}; total=0
    for size in (1,2,3):
        for S in itertools.combinations(range(n),size):
            b=0
            for i in S:b^=bits[i]
            m[S]=1-2*b.bit_count()/N; total+=1
    return m,total

def split_distance_triple(pair1,pair2,triple):
    # Known symmetric marginal class: D(P_ijk,P_i * P_jk).
    return sum(abs(pair1*a+pair2*b+triple*a*b) for a,b in itertools.product((-1,1),repeat=2))/8

def recover_groups(residual,delta=.004):
    N,n=residual.shape;mom,count=all_moments(residual)
    radius=math.sqrt(2*math.log(2*count/delta)/N)
    parent=list(range(n))
    def find(a):
        while parent[a]!=a:parent[a]=parent[parent[a]];a=parent[a]
        return a
    def union(S):
        p=find(S[0])
        for i in S[1:]:parent[find(i)]=p
    edges=[]; pair_edges=0; triple_only=[]; min_lower=1.
    for a,b in itertools.combinations(range(n),2):
        lower=(abs(mom[a,b])-radius)/2
        if lower>0:edges.append([a,b]);union((a,b));pair_edges+=1;min_lower=min(min_lower,lower)
    for S in itertools.combinations(range(n),3):
        a,b,c=S; t=mom[S]
        ds=[split_distance_triple(mom[a,b],mom[a,c],t),
            split_distance_triple(mom[a,b],mom[b,c],t),
            split_distance_triple(mom[a,c],mom[b,c],t)]
        lower=min(ds)-1.5*radius
        if lower>0:
            edges.append(list(S));union(S);min_lower=min(min_lower,lower)
            if all(abs(mom[tuple(sorted(p))])<=radius for p in itertools.combinations(S,2)):
                triple_only.append(list(S))
    components={}
    for i in range(n):components.setdefault(find(i),[]).append(i)
    groups=sorted(components.values())
    # A complete irreducibility recovery needs the stated finest-block split gap.
    # Every certified edge lies in a true block on the simultaneous confidence event.
    # We do not infer that absence of an edge proves independence without gap premise.
    return groups,{'tested_subsets':count,'tested_nontrivial_bipartitions':math.comb(n,2)+3*math.comb(n,3),
        'simultaneous_moment_radius':radius,'delta':delta,'certified_irreducible_hyperedges':len(edges),
        'pair_edges':pair_edges,'pairwise_invisible_certified_triples':triple_only,
        'minimum_irreducibility_lower_bound':min_lower,
        'required_true_block_split_gap_for_completeness':3*radius,
        'promised_minimum_true_block_split_gap':.18,
        'gap_premise_sufficient_at_sample_size':bool(.18>3*radius),
        'completeness_is_conditional_on_gap_and_block_bound':True,
        'maximum_discovered_group':max(map(len,groups))},mom

def estimate_kernels(residual,groups,delta=.004):
    N,n=residual.shape; kernels=[];cells=sum(2**len(g) for g in groups)
    log=math.log(4*cells/delta); total_kl=0.
    for g in groups:
        rows=list(itertools.product((-1,1),repeat=len(g)))
        code=np.zeros(N,dtype=np.int64)
        for j,i in enumerate(g):code|=((residual[:,i]+1)//2).astype(np.int64)<<j
        count=np.bincount(code,minlength=2**len(g))
        # Row encoding is little endian; store matching executable order.
        rows=[tuple(1 if c&(1<<j) else -1 for j in range(len(g))) for c in range(len(count))]
        q=count/N
        # Unbiased empirical variance and Maurer-Pontil empirical Bernstein bound.
        var=q*(1-q)*N/(N-1)
        rad=np.sqrt(2*var*log/N)+7*log/(3*(N-1))
        if np.any(q==0):kl=float('inf')
        else:kl=float(np.sum(rad*rad/q))
        total_kl+=kl
        kernels.append({'members':g,'rows':rows,'probabilities':q.tolist(),
                        'counts':count.tolist(),'cell_radius':rad.tolist(),'kl_upper_bound':kl})
    # PRIMARY certificate: Agrawal (2020), Theorem I.3, applied independently
    # to the fresh histograms of the recovered TRUE blocks. D=sum(k_g-1).
    # The gamma MGF implies P(N sum KL(Q_g||P_g) > D+sqrt(2D*l)+l)<=exp(-l).
    # l=6 and integer outward ceil_sqrt make the threshold exact; e^6>400 is
    # verified below by a rational lower Taylor sum. No probability grid is used.
    D=sum(2**len(g)-1 for g in groups)
    s=math.isqrt(12*D)
    if s*s<12*D:s+=1
    threshold=D+s+6
    partial=Fraction(0);term=Fraction(1);terms=0
    while partial<=400:
        partial+=term;terms+=1;term*=Fraction(6,terms)
    assert partial>400
    def outward_tv(H):
        scale=10**6;num=H*threshold*scale*scale;den=2*N
        r=math.isqrt(num//den)
        if r*r*den<num:r+=1
        return min(1.,r/scale)
    return kernels,{'delta':.0025,'calibration_rows':N,'cells':cells,
        'one_step_joint_KL_bound':threshold/N,'KL_direction':'empirical_to_true',
        'gamma_shape_dimension':D,'integer_threshold_N_times_KL':threshold,
        'ceil_sqrt_12D':s,'exponential_tail_exponent':6,
        'exact_rational_exp6_lower_bound_terms':terms,
        'failure_bound_rational':'1/400',
        'trajectory_TV_bounds':{str(H):outward_tv(H) for H in (1,10,100)},
        'TV_values_rounded_outward_to_denominator':10**6,
        'bound':'Agrawal gamma MGF across independent block histograms; feedback chain rule KL(Q_traj||P_traj)<=H*sum KL(Q_g||P_g); Pinsker; same initial memory; arbitrary nonanticipating legal controllers',
        'primary_source':'https://arxiv.org/html/1904.02291v4#S1.Thmtheorem3',
        'alternative_Bernstein_bound_not_simultaneously_claimed':{
            'delta':delta,'KL_direction':'true_to_empirical','one_step_joint_KL_bound':total_kl,
            'trajectory_TV_bounds':{str(H):min(1.,math.sqrt(H*total_kl/2)) for H in (1,10,100)},
            'role':'comparison only, not minimized with the primary bound and not included in the primary confidence claim'},
        'probability_grid_used':False}

def scalar_value(m,actions,n):
    def v(c):
        if c<n:return int(actions[-1,c])
        k,j=divmod(c,n);return int(np.all(actions[-1-k:-1,j]==1))
    return m['intercept']+sum(w*v(c) for c,w in m['linear'])+sum(w*v(a)*v(b) for a,b,w in m['interactions'])

def audit(truth,truthgroups,models,kernels,n):
    checks=0;maxerr=0.
    for true,fit in zip(truth,models):
        # Equality of sparse polynomial representations after canonical zero removal.
        def canonical(m):
            return (m['intercept'],sorted(map(tuple,m['linear'])),sorted(map(tuple,m['interactions'])))
        assert canonical(true)==canonical(fit)
        checks+=1
    assert sorted([g['members'] for g in truthgroups])==sorted([g['members'] for g in kernels])
    for g in truthgroups:
        fit=next(k for k in kernels if k['members']==g['members'])
        true={tuple(r):p for r,p in zip(g['rows'],g['probabilities'])}
        err=sum(abs(p-true[tuple(r)]) for r,p in zip(fit['rows'],fit['probabilities']))/2
        maxerr=max(maxerr,err)
    return {'response_polynomials_exactly_equal':checks,'group_partition_matches_synthetic_truth':True,
            'maximum_actual_block_kernel_TV':maxerr,
            'status':'simulator-side audit ONLY; not the source of observational confidence'}

def compile_description(owners,models,memory,kernels,n):
    components=[]
    for owner in sorted(set(owners)):
        outputs=[i for i,o in enumerate(owners) if o==owner]
        hist=set();current=set()
        for i in outputs:
            m=models[i]
            for c,w in m['linear']:
                (current if c<n else hist).add(c if c<n else c%n)
            for a,b,w in m['interactions']:current.add(a);hist.add(b%n)
        subscriptions=[]
        for g,k in enumerate(kernels):
            projection=[[i,k['members'].index(i)] for i in outputs if i in k['members']]
            if projection:subscriptions.append({'event_group':g,'output_position_pairs':projection})
        components.append({'owner':owner,'outputs':outputs,'current_action_inputs':sorted(current),
            'memory_channels':sorted(hist),'memory_states':{j:memory[j]['partition'][0] for j in hist},
            'joint_event_projections':subscriptions})
    return components

def execute_description(components,action,events,models,memory,n):
    result=np.zeros(n,dtype=int)
    for component in components:
        states=component['memory_states']
        def feature(c):
            if c<n:return int(action[c])
            k,j=divmod(c,n); rep=memory[j]['representatives'][states[j]]
            return int(all(v==1 for v in rep[-k:]))
        for i in component['outputs']:
            m=models[i]
            result[i]=m['intercept']+sum(w*feature(c) for c,w in m['linear'])+sum(w*feature(a)*feature(b) for a,b,w in m['interactions'])
        for sub in component['joint_event_projections']:
            event=events[sub['event_group']]
            for output,position in sub['output_position_pairs']:result[output]+=event[position]
        # This owner's private copies update only from permitted broadcast actions.
        for j,st in list(states.items()):states[j]=memory[j]['transition_minus_plus'][st][int(action[j]==1)]
    return result

def feedback_checks(models,kernels,memory,n,seed):
    rng=np.random.default_rng(seed+991)
    # Two crossing ownership descriptions. Neither may resample projected group rows.
    ownerA=[i%3 for i in range(n)];ownerB=[(i//3)%4 for i in range(n)]
    splitA=sum(len({ownerA[i] for i in g['members']})>1 for g in kernels)
    splitB=sum(len({ownerB[i] for i in g['members']})>1 for g in kernels)
    tests=[]
    for kind in ('neighbor_sign','alternating_threshold','cross_group_majority','history_switch'):
        history=np.full((L,n),-1,dtype=np.int8);last=np.zeros(n);prev=np.zeros(n);checks=0
        states=[m['partition'][0] for m in memory]
        descriptionA=compile_description(ownerA,models,memory,kernels,n)
        descriptionB=compile_description(ownerB,models,memory,kernels,n)
        for t in range(128):
            if kind=='neighbor_sign':a=np.where(np.roll(last,1)>=0,-1,1)
            elif kind=='alternating_threshold':a=np.where(last+np.roll(last,3)>(t%7)-3,1,-1)
            elif kind=='cross_group_majority':a=np.where(np.roll(last,2)+np.roll(last,7)+np.roll(last,11)>=0,1,-1)
            else:a=np.where((last-prev)*np.roll(last,5)>=0,1,-1)
            ah=np.vstack([history,a]);mean=np.array([scalar_value(m,ah,n) for m in models])
            def feature(c):
                if c<n:return int(a[c])
                k,j=divmod(c,n)
                rep=memory[j]['representatives'][states[j]]
                return int(all(v==1 for v in rep[-k:]))
            compiled_mean=np.array([m['intercept']+sum(w*feature(c) for c,w in m['linear'])+sum(w*feature(c)*feature(d) for c,d,w in m['interactions']) for m in models])
            assert np.array_equal(compiled_mean,mean)
            states=[m['transition_minus_plus'][st][int(a[j]==1)] for j,(m,st) in enumerate(zip(memory,states))]
            events={j:np.asarray(g['rows'][rng.choice(len(g['rows']),p=g['probabilities'])]) for j,g in enumerate(kernels)}
            noise=np.zeros(n,dtype=int)
            for j,g in enumerate(kernels):
                for k,i in enumerate(g['members']):noise[i]=events[j][k]
            outA=execute_description(descriptionA,a,events,models,memory,n)
            outB=execute_description(descriptionB,a,events,models,memory,n)
            assert np.array_equal(outA,outB) and np.array_equal(outA,mean+noise)
            checks+=n;prev,last=last,outA;history=ah[-L:]
        tests.append({'controller':kind,'steps':128,'pathwise_cross_description_equalities':checks})
    return {'ownership_A':'channel mod3','ownership_B':'floor(channel/3) mod4',
        'noise_groups_crossing_A':splitA,'noise_groups_crossing_B':splitB,
        'independently_executed_owner_local_transducers':True,
        'checks':tests,'role':'software smoke tests; all-feedback statistical guarantee comes from local certificate and chain rule, not these controllers'}

def wrong_memory_witnesses(actions,y,models,ntrain,nvalidate):
    n=y.shape[1];results=[]
    for budget in range(L):
        truncated=[]
        for m in models:
            truncated.append({'intercept':m['intercept'],
                'linear':[[c,w] for c,w in m['linear'] if c<n or c//n<=budget],
                'interactions':[[a,b,w] for a,b,w in m['interactions'] if b//n<=budget]})
        pred=evaluate_terms(actions,truncated)
        ids=np.arange(ntrain+L,ntrain+nvalidate,L+1)
        violation=np.abs(y[ids].astype(int)-pred[ids].astype(int))!=1
        results.append({'budget':budget,'rejected_output_channels':int(np.any(violation,axis=0).sum()),
                        'support_violations':int(violation.sum())})
    return results

def coverage_and_obstructions(actions,models,memory,kernels,group_cert,ntrain):
    n=len(models); x=run_columns(actions,stop=ntrain+L); cover=[]
    for i,m in enumerate(models):
        currents=sorted({c for c,w in m['linear'] if c<n}|{a for a,b,w in m['interactions']})
        orders={}
        for c,w in m['linear']:
            if c>=n:orders[c%n]=max(orders.get(c%n,0),c//n)
        for a,b,w in m['interactions']:orders[b%n]=max(orders.get(b%n,0),b//n)
        code=np.zeros(ntrain,dtype=int); radix=1
        for c in currents:code+=radix*((x[:,c]+1)//2).astype(int);radix*=2
        for j,r in sorted(orders.items()):
            run=sum(x[:,k*n+j] for k in range(1,r+1)).astype(int)
            code+=radix*run;radix*=r+1
        counts=np.bincount(code,minlength=radix)
        cover.append({'output':i,'distinct_predictive_contexts':radix,'minimum_training_count':int(counts.min())})
    triples=group_cert['pairwise_invisible_certified_triples']
    witness=None
    if triples:
        g=triples[0]; kernel=next(k for k in kernels if k['members']==g)
        p=sum(p for row,p in zip(kernel['rows'],kernel['probabilities']) if math.prod(row)==1)
        witness={'channels':g,'two_correct_fragment_families':[[g[:2],[g[2]]],[[g[0],g[2]],[g[1]]]],
          'missing_joint_distinction':'all one- and two-coordinate projections of the synthetic triple are independent uniform, while the triple is not',
          'novel_feedback_controller':'after one readout, subtract learned conditional means and set a selected next action to the product of these three residuals',
          'learned_probability_next_action_positive':p,'independent_projection_prediction':.5,
          'synthetic_true_probability':.685,
          'source_of_true_probability':'synthetic audit, not inference',
          'repair':'retain the learned positive three-coordinate joint event and project it coherently through both crossing fragment families'}
    memory_w=[]
    for r in range(1,L+1):
        j=next(m['channel'] for m in memory if m['selected_order']==r)
        i=next(i for i,m in enumerate(models) if any(b//n==r and b%n==j for a,b,w in m['interactions']))
        m=models[i]; current=next(a for a,b,w in m['interactions'] if b%n==j)
        h1=np.full((L+1,n),-1,dtype=np.int8);h2=h1.copy()
        h1[-1-r:-1,j]=1;h2[-1-r:-1,j]=1;h2[-1-r,j]=-1
        h1[-1,current]=1;h2[-1,current]=1
        v1=scalar_value(m,h1,n);v2=scalar_value(m,h2,n)
        assert v1!=v2
        memory_w.append({'source_action_channel':j,'output_channel':i,'necessary_order':r,
          'two_histories_share_last_actions':r-1,'conditional_means':[v1,v2],
          'same_current_actions':True,'noise_supports_disjoint':abs(v1-v2)>2})
    pairchecks=0; witness_by_channel=[]
    for j,mem in enumerate(memory):
        examples=[]
        for a,b in itertools.combinations(range(mem['quotient_states']),2):
            h1=np.full((L+1,n),-1,dtype=np.int8);h2=h1.copy()
            h1[:-1,j]=mem['representatives'][a];h2[:-1,j]=mem['representatives'][b]
            h1[-1,:]=1;h2[-1,:]=1
            differences=[i for i,m in enumerate(models) if scalar_value(m,h1,n)!=scalar_value(m,h2,n)]
            assert differences, ('nonminimal feature quotient',j,a,b)
            examples.append([a,b,differences[0]]);pairchecks+=1
        witness_by_channel.append({'channel':j,'state_pairs_and_distinguishing_output':examples})
    return {'local_context_coverage':cover,'minimum_all_outputs':min(v['minimum_training_count'] for v in cover),
            'wrong_grouping_novel_feedback_witness':witness,'memory_lower_budget_witnesses':memory_w,
            'exact_memory_distinguishability_pairs_checked':pairchecks,
            'per_channel_memory_minimality_witnesses':witness_by_channel,
            'minimality_scope':'each channel suffix quotient separately, relative to the learned response family and all allowed other-channel contexts; not a unique global physical state'}

def run(n,args):
    start=time.time();out=Path(args.output)/f'n{n}';out.mkdir(parents=True,exist_ok=True)
    truth,tgroups=generate(n,args.train,args.validate,args.calibration,args.seed+n,out)
    records=np.load(out/'records.npz');actions=records['actions'];y=records['readouts']
    t=time.time();models,search=discover_mean(actions,y,args.train);fit_seconds=time.time()-t
    frozen={'models':models,'training_records_sha256':sha(out/'records.npz'),
            'uses_truth':False,'probability_grid_used':False}
    dump(out/'frozen_mean.json',frozen);frozenhash=sha(out/'frozen_mean.json')
    pred,support=support_validate(actions,y,models,args.train,args.validate)
    assert support['passed'],support
    # Mean remains frozen; calibration is disjoint from training and support validation.
    residual=y[args.train+args.validate:].astype(np.int32)-pred[args.train+args.validate:].astype(np.int32)
    split=len(residual)//2
    t=time.time();groups,group_cert,mom=recover_groups(residual[:split]);group_seconds=time.time()-t
    group_cert['calibration_rows']=split
    assert max(map(len,groups))<=3
    assert group_cert['gap_premise_sufficient_at_sample_size']
    kernels,prob_cert=estimate_kernels(residual[split:],groups)
    memory=[quotient_for_channel(models,n,j) for j in range(n)]
    result={'n':n,'records':{'training':args.train,'support_validation_stream':args.validate,'noise_calibration':args.calibration,
                           'total':len(y),'saved_bytes':(out/'records.npz').stat().st_size},
        'discovery_search':search,'support_certificate':support,'joint_group_certificate':group_cert,
        'probability_certificate':prob_cert,'discovered_noise_groups':groups,
        'per_response_memory_orders':[max([0]+[c//n for c,w in m['linear'] if c>=n]+[b//n for a,b,w in m['interactions']]) for m in models],
        'discovered_memory_orders':[m['selected_order'] for m in memory],
        'recursive_memory_state_counts':[m['quotient_states'] for m in memory],
        'specific_truncated_candidate_rejections':wrong_memory_witnesses(actions,y,models,args.train,args.validate),
        'coverage_and_obstructions':coverage_and_obstructions(actions,models,memory,kernels,group_cert,args.train),
        'simulator_audit':audit(truth,tgroups,models,kernels,n),
        'cross_description_checks':feedback_checks(models,kernels,memory,n,args.seed+n),
        'global_raw_lag_state_count':'2^'+str(L*n),
        'global_transition_table_built':False,'coherent_interface':'one fresh empirical joint-row event per discovered group and time; owners receive projections, never independent copies',
        'fit_seconds':fit_seconds,'joint_search_seconds':group_seconds,'elapsed_seconds':time.time()-start,
        'frozen_mean_sha256':frozenhash,
        'conditional_failure_probability_upper_bound':support['false_acceptance_bound']+.004+.0025}
    dump(out/'executable_candidate.json',{'mean':models,'memory_transducers':memory,'joint_innovation_interfaces':kernels,
        'ownership_A':compile_description([i%3 for i in range(n)],models,memory,kernels,n),
        'ownership_B':compile_description([(i//3)%4 for i in range(n)],models,memory,kernels,n)})
    dump(out/'results.json',result)
    print(json.dumps({'n':n,'seconds':result['elapsed_seconds'],'groups':len(groups),
                      'invisible_triples':len(group_cert['pairwise_invisible_certified_triples']),
                      'min_order':min(result['discovered_memory_orders']),'max_order':max(result['discovered_memory_orders']),
                      'TV10':prob_cert['trajectory_TV_bounds']['10']}),flush=True)
    return result

def main():
    p=argparse.ArgumentParser();p.add_argument('--sizes',nargs='+',type=int,default=[12,24,48,96]);p.add_argument('--train',type=int,default=65536)
    p.add_argument('--validate',type=int,default=20480);p.add_argument('--calibration',type=int,default=262144)
    p.add_argument('--seed',type=int,default=20261029);p.add_argument('--output',default=str(Path(__file__).parent/'runs'));a=p.parse_args()
    results=[run(n,a) for n in a.sizes];dump(Path(a.output)/'summary.json',results)
if __name__=='__main__':main()

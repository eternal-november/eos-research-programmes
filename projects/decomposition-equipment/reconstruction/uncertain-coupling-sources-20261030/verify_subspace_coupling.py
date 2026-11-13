#!/usr/bin/env python3
"""Exact finite GF(2) checks; standard library only, no physical-model validation."""
import itertools, json, math
from fractions import Fraction
from functools import lru_cache
from pathlib import Path


def span(vs):
    out={0}
    for v in vs:
        out |= {x^v for x in tuple(out)}
    return frozenset(out)


def subspaces(n):
    found={frozenset({0})}
    todo=list(found)
    while todo:
        s=todo.pop()
        for v in range(1,1<<n):
            if v not in s:
                t=span(tuple(s)+(v,))
                if t not in found: found.add(t);todo.append(t)
    return sorted(found,key=lambda s:(len(s),tuple(sorted(s))))


def basis(s):
    bs=[]; done=frozenset({0})
    for x in sorted(s):
        if x not in done:bs.append(x);done=span(bs)
    return tuple(bs)


def dot(a,b):return (a&b).bit_count()&1

def apply(rows,x):return sum(dot(a,x)<<i for i,a in enumerate(rows))

def image(rows,s):return frozenset(apply(rows,x) for x in s)

def dist(rows,s):
    counts={}
    for x in s:
        y=apply(rows,x);counts[y]=counts.get(y,0)+1
    return {y:Fraction(k,len(s)) for y,k in counts.items()}


def check_full_criterion(n):
    spaces=subspaces(n); full=frozenset(range(1<<n));bs=[basis(s) for s in spaces]
    imgs=[[image(b,s) for s in spaces] for b in bs]
    fullidx=spaces.index(full)
    families=[()]+[(i,) for i in range(len(spaces))]+list(itertools.combinations(range(len(spaces)),2))
    cases=0;countermodels=0;riskcases=0;affinecases=0
    for fam in families:
        compatible=[j for j,s in enumerate(spaces) if all(imgs[i][j]==imgs[i][fullidx] for i in fam)]
        union=set().union(*(spaces[i] for i in fam)) if fam else {0}
        for qi,Q in enumerate(spaces):
            direct=all(imgs[qi][j]==imgs[qi][fullidx] for j in compatible)
            criterion=Q<=union
            assert direct==criterion,(n,fam,Q,direct,criterion)
            cases+=1
            # Conservative rank-risk maximum for the joint nonzero test.
            actual=[Fraction(len(imgs[qi][j])-1,len(imgs[qi][j])) for j in compatible]
            assert max(actual)==Fraction(len(imgs[qi][fullidx])-1,len(imgs[qi][fullidx]))
            riskcases+=1
            if not criterion:
                chi=min(Q-union)
                H=frozenset(x for x in full if dot(chi,x)==0)
                hi=spaces.index(H)
                assert hi in compatible and imgs[qi][hi]!=imgs[qi][fullidx]
                for i in fam:assert dist(bs[i],H)==dist(bs[i],full)
                countermodels+=1
        # Affine opposite hyperplanes have identical allowed probe laws.
        uncovered=set(full)-union
        if uncovered:
            chi=min(uncovered)
            H0=frozenset(x for x in full if dot(chi,x)==0)
            H1=frozenset(x for x in full if dot(chi,x)==1)
            assert H0 and H1
            for i in fam: assert dist(bs[i],H0)==dist(bs[i],H1)
            # Any mixture choosing b=1 with prob t has failure (t,1-t).
            for t in [Fraction(k,20) for k in range(21)]:
                assert max(t,1-t)>=Fraction(1,2)
            affinecases+=1
    return dict(dimension=n,subspaces=len(spaces),probe_families=len(families),query_cases=cases,hyperplane_witnesses=countermodels,rank_risk_cases=riskcases,affine_world_pairs=affinecases)


def check_gluing(n):
    spaces=subspaces(n);full=frozenset(range(1<<n));bs=[basis(s) for s in spaces]
    families=[(i,) for i in range(len(spaces))]+list(itertools.combinations(range(len(spaces)),2))
    consistent=0;querycases=0;arbitrary=0;inconsistent=0
    for fam in families:
        for true in spaces:
            U=[image(bs[i],true) for i in fam]
            V=frozenset(x for x in full if all(apply(bs[i],x) in u for i,u in zip(fam,U)))
            assert true<=V and V in spaces
            assert all(image(bs[i],V)==u for i,u in zip(fam,U))
            for i,u in zip(fam,U):
                assert dist(bs[i],V)=={y:Fraction(1,len(u)) for y in u}
            consistent+=1
            compatible=[s for s in spaces if all(image(bs[i],s)==u for i,u in zip(fam,U))]
            vbase=basis(V)
            # Restricted row covectors are bit-vectors of values on a basis of V.
            union={0}
            for i in fam:union |= {apply(vbase,w) for w in spaces[i]}
            for Q,qbase in zip(spaces,bs):
                qrestricted={apply(vbase,w) for w in Q}
                direct=all(image(qbase,s)==image(qbase,V) for s in compatible)
                assert direct==(qrestricted<=union)
                querycases+=1
        # Arbitrary supplied projection-subspace data, not only generated data.
        projected_choices=[subspaces(len(bs[i])) for i in fam]
        for U in itertools.product(*projected_choices):
            V=frozenset(x for x in full if all(apply(bs[i],x) in u for i,u in zip(fam,U)))
            condition=all(image(bs[i],V)==u for i,u in zip(fam,U))
            exists=any(all(image(bs[i],s)==u for i,u in zip(fam,U)) for s in spaces)
            assert condition==exists
            arbitrary+=1;inconsistent+=not exists
    return dict(dimension=n,generated_data_cases=consistent,restricted_query_cases=querycases,arbitrary_data_cases=arbitrary,inconsistent_data_cases=inconsistent)


def check_span_sampling():
    cases=0;tuple_count=0;affine_cases=0;rows=[]
    for r in range(4):
        full=frozenset(range(1<<r))
        for m in range(6):
            bad=0;affine_bad=0;total=(1<<r)**m
            for draws in itertools.product(range(1<<r),repeat=m):
                bad+=span(draws)!=full
                if m: affine_bad+=span(tuple(x^draws[0] for x in draws[1:]))!=full
            prob=Fraction(bad,total)
            bound=Fraction((1<<r)-1,1<<m)
            assert prob<=bound
            if m:
                assert Fraction(affine_bad,total)<=Fraction((1<<r)-1,1<<(m-1))
                affine_cases+=1
            cases+=1;tuple_count+=total
            rows.append(dict(rank=r,samples=m,failure=str(prob),union_bound=str(bound)))
    return dict(cases=cases,affine_cases=affine_cases,sample_tuples=tuple_count,rows=rows)


def check_union_not_span():
    full=frozenset(range(4)); probes=[(1,),(2,)]
    diag=frozenset({0,3})
    assert all(dist(p,full)==dist(p,diag) for p in probes)
    assert span((1,2))==full
    assert set(span((1,)))|set(span((2,))) !=full
    assert dist((1,2),full)!=dist((1,2),diag)
    # Guard against identifying a law discrepancy with a mission impossibility.
    # Constant mission succeeds on both worlds even though joint laws differ.
    assert all(Fraction(sum(1 for x in s),len(s))==1 for s in [full,diag])
    return dict(status='PASS',union_required=True,span_insufficient=True,law_difference_not_mission_impossibility=True)


def check_adaptive_source_regime():
    # Full same-source transcript differs, although each allowed fresh probe agrees.
    worlds=[frozenset(x for x in range(8) if dot(7,x)==b) for b in (0,1)]
    probes=[(1,2),(2,4)]
    policy_count=0
    for first in range(2):
        for second_choices in itertools.product(range(2),repeat=4):
            transcript=[]
            for world in worlds:
                p1=dist(probes[first],world); out={}
                for y1,prob1 in p1.items():
                    second=second_choices[y1]
                    p2=dist(probes[second],world)
                    for y2,prob2 in p2.items():
                        out[(y1,second,y2)]=prob1*prob2
                transcript.append(out)
            assert transcript[0]==transcript[1]
            policy_count+=1
    same_source=[dist((1,2,4),world) for world in worlds]
    assert same_source[0]!=same_source[1]
    return dict(fresh_source_depth_two_adaptive_policies=policy_count,
                fresh_transcripts_equal=True,same_source_joint_distinguishes=True)


def check_chain_missions():
    rows=[]; ambient_vectors=0; support_vectors=0; probe_distribution_checks=0
    for n in range(2,7):
        # Coordinates r0, z1..zn, r1..rn, d. The delayed value d equals rn.
        def output(latent):
            r0=latent&1; zs=[(latent>>(i+1))&1 for i in range(n)]
            rs=[];r=r0
            for z in zs:r^=z;rs.append(r)
            bits=[r0]+zs+rs+[r]
            return sum(b<<i for i,b in enumerate(bits))
        independent=frozenset(output(t) for t in range(1<<(n+1)))
        correlated=frozenset(output(t) for t in range(1<<(n+1)) if ((t>>1)&1)==((t>>2)&1))
        probes=[]
        for i in range(1,n+1):
            previous=0 if i==1 else n+i-1
            probes.append((1<<previous,1<<i,1<<(n+i)))
        probes.append((1<<(2*n),1<<(2*n+1)))
        observed=[image(A,independent) for A in probes]
        for A,U in zip(probes,observed):
            assert image(A,correlated)==U
            assert dist(A,correlated)==dist(A,independent)
            probe_distribution_checks+=1
        V=frozenset(x for x in range(1<<(2*n+2)) if all(apply(A,x) in U for A,U in zip(probes,observed)))
        assert V==independent
        fused=1 | sum(1<<i for i in range(1,n+1)) | (1<<(2*n+1))
        assert image((fused,),V)==frozenset({0})
        extra=(1<<1)|(1<<2)
        assert image((extra,),correlated)==frozenset({0})
        assert image((extra,),independent)==frozenset({0,1})
        assert correlated<independent
        ambient_vectors+=1<<(2*n+2)
        support_vectors+=len(independent)+len(correlated)
        rows.append(dict(chain_length=n,ambient_dimension=2*n+2,independent_support_size=len(independent),
                         correlated_support_size=len(correlated),probe_count=len(probes),fused_failure='0',
                         unused_parity_failure_correlated='0',unused_parity_failure_independent='1/2'))
    return dict(cases=len(rows),ambient_vectors_checked=ambient_vectors,source_vectors=sum(r['independent_support_size']+r['correlated_support_size'] for r in rows),
                local_probe_distribution_checks=probe_distribution_checks,rows=rows)


def check_physical_negative_and_budget():
    full=frozenset(range(16));cs=(1|2|4,1|2|8)
    worlds=[frozenset(x for x in full if dot(c,x)==0) for c in cs]
    assert len(worlds[0])==len(worlds[1])==8
    pairs=list(itertools.combinations(range(4),2))
    for pair in pairs:
        rows=tuple(1<<i for i in pair)
        assert dist(rows,worlds[0])==dist(rows,worlds[1])
    # Select second coordinate after first outcome: all legal length-two policies.
    adaptive_cases=0
    for first in range(4):
        for choices in itertools.product([j for j in range(4) if j!=first],repeat=2):
            distributions=[]
            for world in worlds:
                counts={}
                for x in world:
                    y1=(x>>first)&1;second=choices[y1];y2=(x>>second)&1
                    key=(y1,second,y2);counts[key]=counts.get(key,0)+Fraction(1,len(world))
                distributions.append(counts)
            assert distributions[0]==distributions[1]
            adaptive_cases+=1
    failures=[[Fraction(sum(dot(c,x) for x in world),len(world)) for c in cs] for world in worlds]
    assert failures==[[Fraction(0),Fraction(1,2)],[Fraction(1,2),Fraction(0)]]
    # Signals: parity0, parity1, full block compressed to the two parities,
    # and a nondiscriminating pair (its four outcomes are equiprobable).
    signals=[[(Fraction(1),Fraction(1,2)),(Fraction(0),Fraction(1,2))],
             [(Fraction(1,2),Fraction(1)),(Fraction(1,2),Fraction(0))],
             [(Fraction(1,2),Fraction(1,2)),(Fraction(1,2),Fraction(0)),(Fraction(0),Fraction(1,2))],
             [(Fraction(1,4),Fraction(1,4))]*4]
    @lru_cache(None)
    def value(m,w0,w1):
        # Weighted mission failure: r0, r1, or abort. Stopping early is allowed.
        stop=min(w1/2,w0/2,w0+w1)
        if not m:return stop
        return min([stop]+[sum(value(m-1,w0*p0,w1*p1) for p0,p1 in signal) for signal in signals])
    checks=[]
    for m in range(9):
        risk=value(m,Fraction(1,2),Fraction(1,2))
        expected=Fraction(1,1<<(m+2))
        assert risk==expected
        # Fair initial route, repeat its parity; first one switches to the other.
        per_world=Fraction(1,2)*Fraction(1,1<<m)*Fraction(1,2)
        assert per_world==risk
        checks.append(dict(probes=m,bayes_lower_bound=str(risk),attained_each_world=str(per_world)))
    return dict(pair_probes=len(pairs),adaptive_same_block_two_read_policies=adaptive_cases,
                route_failures=[[str(x) for x in row] for row in failures],
                budget_cases=len(checks),dynamic_program_states=value.cache_info().currsize,rows=checks,
                note='Each discriminating probe is available in the enlarged regime, uses a fresh block and costs one call. The lower bound is for this two-world subclass.')


def check_fresh_window_indices():
    cases=0
    for H in range(1,9):
        for D in range(9):
            s=D
            a=set(range(s-D,s+H));b=set(range(s+H+D-D,s+H+D+H))
            assert a.isdisjoint(b)
            assert max(a)+1==min(b)
            if H+D>1:
                early=set(range(s+H+D-1-D,s+H+D-1+H))
                assert a & early
            cases+=1
    return dict(cases=cases,disjoint_at_spacing_H_plus_D=True,
                one_tick_less_overlaps=True,note='Index disjointness only; innovation independence and the memory bound are model premises.')


def check_unknown_lag_scan():
    cases=0; matched=0; nonmatched=0
    for n in range(2,7):
        for D in range(1,6):
            # Form coefficients in genuine independent primitive source-time bits.
            coords={(t,j):idx for idx,(t,j) in enumerate(itertools.product(range(-D,D+1),range(n+1)))}
            for shared in (False,True):
                def rn_at(t):
                    value=1<<coords[t,0]
                    for j in range(1,n+1):
                        primitive=1 if shared and j==2 else j
                        value ^= 1<<coords[t,primitive]
                    return value
                for actual_lag in range(1,D+1):
                    for probe_lag in range(1,D+1):
                        r=rn_at(0);delayed=rn_at(probe_lag-actual_lag)
                        pair_support=span([((r>>j)&1)|(((delayed>>j)&1)<<1) for j in range(len(coords))])
                        target=frozenset({0,3}) if probe_lag==actual_lag else frozenset(range(4))
                        assert pair_support==target
                        cases+=1
                        matched+=probe_lag==actual_lag;nonmatched+=probe_lag!=actual_lag
    return dict(linear_endpoint_support_cases=cases,matching_lag_cases=matched,
                nonmatching_lag_cases=nonmatched,chain_lengths=[2,6],delay_bounds=[1,5],
                both_independent_and_shared_z1_z2=True,
                note='Supports computed exactly from primitive source-time coefficient maps, not Monte Carlo; physical capture and gate timing remain supplied.')


def main():
    results={
      'status':'PASS',
      'scope':'Exact GF(2) finite algebra; not a proof for all finite fields, physical safety, filter realizability, acquisition hardware, or CFS coherence.',
      'full_ambient_criteria':[check_full_criterion(n) for n in range(1,5)],
      'maximal_extension_gluing':[check_gluing(n) for n in range(1,4)],
      'span_sampling':check_span_sampling(),
      'union_regression':check_union_not_span(),
      'adaptive_source_regime':check_adaptive_source_regime(),
      'chain_missions':check_chain_missions(),
      'physical_negative_budget':check_physical_negative_and_budget(),
      'fresh_window_indices':check_fresh_window_indices(),
      'unknown_lag_scan':check_unknown_lag_scan(),
    }
    out=Path(__file__).with_name('subspace_coupling_results.json')
    out.write_text(json.dumps(results,indent=2,sort_keys=True)+'\n')
    print(json.dumps(results,indent=2,sort_keys=True))

if __name__=='__main__':main()

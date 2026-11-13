#!/usr/bin/env python3
"""Exact reference for costly calibration of shared report faults.
Standard-library-only. All numerical assertions use rational arithmetic.
The DP does not assume the proposed closed-form policy is optimal.
"""
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from pathlib import Path
import json

P_CAL=F(1,5)
P_OP=F(1,50)
EPS=F(9,200)
A=1-(1-P_OP)**2
B=1-(1-P_OP)**3
S=F(93,125)
RAW=((0,0),(1,1),(0,1),(1,0))


def enc(x):return {'fraction':str(x),'decimal':float(x)}


def raw_outcome(bits,aligned):
    a=int(bool(bits[0] or bits[1]))
    b=a if aligned else int(bool(bits[1] or bits[2]))
    return a,b


def primitive_dist(p,aligned):
    out={y:F(0) for y in RAW}
    for bits in product((0,1),repeat=3):
        mass=F(1)
        for bit in bits:mass*=p if bit else 1-p
        out[raw_outcome(bits,aligned)]+=mass
    assert sum(out.values())==1
    return out

CAL={True:primitive_dist(P_CAL,True),False:primitive_dist(P_CAL,False)}
OP={True:primitive_dist(P_OP,True),False:primitive_dist(P_OP,False)}
# independent hand-derived likelihood table, used by the planner
L_AL=(F(16,25),F(9,25),F(0))
L_SP=(F(64,125),F(29,125),F(32,125))
# collapsed third outcome is either discordance, which has identical likelihood
# ratio/cost/physical consequences. Keeping its bit orientation cannot improve
# the Bayes optimum: the two children have the same posterior and action set.
for aligned,table in [(True,L_AL),(False,L_SP)]:
    assert tuple([CAL[aligned][(0,0)],CAL[aligned][(1,1)],
                  CAL[aligned][(0,1)]+CAL[aligned][(1,0)]])==table
assert 1-OP[True][(0,0)]==A and 1-OP[False][(0,0)]==B
assert sum(min(a,b) for a,b in zip(L_AL,L_SP))==S


def likelihood(theta,r):return L_AL if theta==r else L_SP


@lru_cache(None)
def dp(q,n):
    """Equal-prior start but arbitrary posterior during planning.
    Returns Bayes probability of selecting the wrong operation mode.
    Actions: stop mode0, stop mode1, or calibrate mode0/1 (when n>0).
    Abort/wait cannot improve since they cause Bad=1 or consume budget.
    """
    best=min(q,1-q)
    if n:
        for r in (0,1):
            val=F(0)
            for l0,l1 in zip(likelihood(0,r),likelihood(1,r)):
                prob=q*l0+(1-q)*l1
                if prob:
                    val+=prob*dp(q*l0/prob,n-1)
            best=min(best,val)
    return best


def enum_vectors(n):
    """All deterministic trees over 3 information-distinct outcomes.
    Terminal vectors are world-wise mode-selection errors, not risks.
    No pruning and duplicate trees retained for honest enumeration counts.
    """
    trees=[(F(0),F(1)),(F(1),F(0))]
    for _ in range(n):
        out=[(F(0),F(1)),(F(1),F(0))]
        for r in (0,1):
            a,b=likelihood(0,r),likelihood(1,r)
            for children in product(trees,repeat=3):
                out.append((sum(a[j]*children[j][0] for j in range(3)),
                            sum(b[j]*children[j][1] for j in range(3))))
        trees=out
    return trees


def replay(theta,n,reverse_production=False):
    """Raw 4-outcome path replay of explicit randomized policy.
    Independent primitive enumeration creates both calibration/operation laws.
    Policy: fair initial mode; repeat it, stop at first discordance and flip;
    after n agreements operate in initial mode.
    """
    bad=F(0);wrong=F(0);expected_tests=F(0);ambiguous=F(0);leaves=0
    worst_tests=0;mass_sum=F(0)
    theta_op=1-theta if reverse_production else theta
    def finish(mode,mass,used,unresolved):
        nonlocal bad,wrong,ambiguous,leaves,worst_tests,mass_sum
        op=primitive_dist(P_OP,mode==theta_op)
        bad+=mass*(1-op[(0,0)])
        wrong+=mass*(mode!=theta_op)
        ambiguous+=mass*unresolved
        mass_sum+=mass
        leaves+=1;worst_tests=max(worst_tests,used)
    def walk(r,k,mass,used):
        nonlocal expected_tests
        if k==0:
            finish(r,mass,used,True);return
        expected_tests+=mass
        for y,py in primitive_dist(P_CAL,r==theta).items():
            if not py:continue
            w=mass*py
            if y[0]!=y[1]:finish(1-r,w,used+1,False)
            else:walk(r,k-1,w,used+1)
    for r in (0,1):walk(r,n,F(1,2),0)
    assert mass_sum==1 and worst_tests<=n
    return {'bad':bad,'wrong':wrong,'expected_tests':expected_tests,
            'ambiguous':ambiguous,'leaves':leaves,'worst_tests':worst_tests}


def main():
    runs=[];audits=[]
    for n in range(7):
        exact_error=dp(F(1,2),n)
        formula=S**n/2
        assert exact_error==formula
        risk=A+(B-A)*formula
        r0,r1=replay(0,n),replay(1,n)
        assert r0['bad']==r1['bad']==risk
        assert r0['wrong']==r1['wrong']==formula
        assert r0['ambiguous']==r1['ambiguous']==(1+S**n)/2
        ex=F(n,2)+sum((S**j for j in range(n)),F(0))/2
        assert r0['expected_tests']==r1['expected_tests']==ex
        rev0,rev1=replay(0,n,True),replay(1,n,True)
        assert rev0['bad']==rev1['bad']==A+(B-A)*(1-formula)
        runs.append({'max_calibrations':n,'deadline':n+3,'energy_budget':n+2,
                     'optimal_mode_error':enc(exact_error),'optimal_bad':enc(risk),
                     'meets_0045':risk<=EPS,'expected_calibrations':enc(ex),
                     'probability_phase_still_ambiguous':enc(r0['ambiguous']),
                     'raw_replay_leaves_each_world':r0['leaves'],
                     'max_calibrations_in_replay':r0['worst_tests'],
                     'reversed_bridge_bad':enc(rev0['bad'])})
        if n<=2:
            trees=enum_vectors(n)
            v=min((x+y)/2 for x,y in trees)
            assert v==exact_error
            audits.append({'max_calibrations':n,'deterministic_trees':len(trees),
                           'minimum_equal_world_average_error':enc(v),'pass':True})
    # Equal marginals only admit a physically worse, disjoint pair of failures.
    marginal=A
    frechet=min(1,2*marginal)
    assert frechet==F(99,1250)
    # Removing the calibration-operation bridge admits stable/reversed pairs.
    # Both have same calibration transcript distribution; for any policy's
    # final mode distribution, average Bad probability is (A+B)/2.
    bridge_robust=(A+B)/2
    results={'description':'Exact costly raw-calibration shared-source case',
      'assumptions':{'primitive_calibration_fault':enc(P_CAL),
        'primitive_operation_fault':enc(P_OP),'aligned_operation_bad':enc(A),
        'split_operation_bad':enc(B),'likelihood_overlap':enc(S),'risk_limit':enc(EPS),
        'calibration_time':1,'calibration_energy':1,'production_time':3,'production_energy':2,
        'energy_convention':'one unit per calibration plus two units for production; stipulated fixture, not measured',
        'calibration_hazard':0,'fixed_hidden_phase':True,'fresh_independent_primitives_each_call':True,
        'calibration_operation_source_use_stable':True,'raw_calibration_outcomes_observed':True,
        'operation_payload_fault_information':False},
      'raw_calibration_likelihoods':{str(k):{str(y):enc(p) for y,p in v.items()} for k,v in CAL.items()},
      'runs':runs,'enumeration_audits':audits,
      'total_trees_checked':sum(a['deterministic_trees'] for a in audits),
      'marginals_only_worst_bad':enc(frechet),
      'unknown_stable_or_reversed_bridge_minimax_bad':enc(bridge_robust),
      'all_checks_passed':True,'dp_cache':str(dp.cache_info())}
    Path(__file__).with_name('calibration_results.json').write_text(json.dumps(results,indent=2)+'\n')
    print('PASS: exact DP, formula, raw primitive replay, mode-flip symmetry, budget, and bridge stress checks')
    print('Exhaustive deterministic trees:',results['total_trees_checked'])
    print('n, minimax risk, mode error, expected probes, ambiguous probability')
    for r in runs:
        print(r['max_calibrations'],r['optimal_bad']['decimal'],r['optimal_mode_error']['decimal'],
              r['expected_calibrations']['decimal'],r['probability_phase_still_ambiguous']['decimal'])
    print(dp.cache_info())

if __name__=='__main__':main()

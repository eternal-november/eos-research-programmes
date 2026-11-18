"""Exact conditional control/access/accounting evidence for CONTROL.md.

The universal source/runtime/renewal obligations are not replaced by these
finite checks. --write regenerates only control_results.json; --check compares.
"""
from __future__ import annotations
import sys
if sys.flags.optimize:
    raise RuntimeError('Unoptimized Python is required')
import argparse
from fractions import Fraction as F
import hashlib
from itertools import product
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
N, BAD = 34, 5
GAIN, RADIUS, RULE, ETA, ROUND = F(8,5), F(4,5), F(1,20), F(3,1000), F(1,1000)
DELTA, ALO, AHI = F(1,100000000), F(9,200), F(11,200)
PBAR = F(205,100000)
EXTERNAL = F(1,2)+F(1,100)+PBAR
DRIFT = 2+2*AHI+EXTERNAL
COMMAND_ERROR = GAIN*(RULE+2*ETA)+ROUND
SERVICE = F(3,10)


def qstr(x):
    x=F(x)
    return f'{x.numerator}/{x.denominator}'


def correction(m: int) -> int:
    sign = 1 if m>0 else (-1 if m<0 else 0)
    return sign*min(1500,(8*max(abs(m)-53,0))//5)


def ideal(y: F) -> F:
    sign = 1 if y>0 else (-1 if y<0 else 0)
    return sign*min(F(3,2),GAIN*max(abs(y)-(RULE+ETA),F(0)))


def trunc_milli(y: F) -> int:
    return (1 if y>=0 else -1)*(abs(y).numerator*1000//abs(y).denominator)


def policy_checks():
    maximum_round=F(0); maximum_effect_error=F(0); domain_cases=0
    for m in range(-4000,4001):
        q=correction(m); y=F(m,1000)
        assert q==trunc_milli(ideal(y))
        assert abs(q)<=1500
        maximum_round=max(maximum_round,abs(F(q,1000)-ideal(y)))
        if q>0:
            assert y-ETA>=RULE
        if q<0:
            assert y+ETA<=-RULE
        if -803<=m<=803:
            assert abs(q)<=1200
            assert abs(5*q-8*m)<=429
            lo,hi=max(-RADIUS,y-ETA),min(RADIUS,y+ETA)
            if lo<=hi:
                for actual in (lo,hi):
                    error=abs(F(q,1000)-GAIN*actual)
                    assert error<=COMMAND_ERROR
                    maximum_effect_error=max(maximum_effect_error,error)
                    domain_cases+=1
    # Without the extra error guard, a legitimate inaccurate observation can
    # induce an otherwise intact program to violate the factive sign duty.
    misleading,actual=51,F(491,10000)
    naive=(8*(misleading-50))//5
    assert abs(F(misleading,1000)-actual)==F(19,10000) < F(1,500)
    assert F(101,2)<1000*(actual+F(149,100000))<F(103,2)
    assert naive>0 and actual<RULE and correction(misleading)==0
    # A better actual observation does not shrink a fixed algorithmic deadband.
    perfect=F(54,1000)
    perfect_error=abs(F(correction(54),1000)-GAIN*perfect)
    invalid_reduced_bound=GAIN*RULE+ROUND
    fixed_guard_bound=GAIN*(RULE+ETA)+ROUND
    assert perfect_error==F(427,5000)>invalid_reduced_bound
    assert perfect_error<=fixed_guard_bound
    return {'packet_values_checked':8001,'good_radius_endpoint_cases':domain_cases,
            'maximum_observed_rounding_error':qstr(maximum_round),
            'proved_conservative_command_error':qstr(COMMAND_ERROR),
            'maximum_observed_effect_error':qstr(maximum_effect_error),
            'fixed_guard_counterexample':{'perfect_state_and_estimate':qstr(perfect),
                'selected_guard':qstr(ETA),'actual_issue_and_effect_error':'0/1',
                'command_milliunits':correction(54),'actual_bias':qstr(perfect_error),
                'invalid_actual_error_substitution_bound':qstr(invalid_reduced_bound),
                'correct_fixed_guard_bound':qstr(fixed_guard_bound)},
            'unguarded_permission_counterexample':{'true_state':qstr(actual),
                'estimate_milliunits':misleading,'naive_positive_command_milliunits':naive,
                'guarded_command_milliunits':correction(misleading)}}


def branch_certificate(name,weights):
    assert len(weights)==N and sum(weights)==1 and min(weights)>0
    beta=sum(sorted(weights,reverse=True)[:BAD],F(0)); g=1-beta
    lam=GAIN*g-2*AHI
    additive=g*COMMAND_ERROR+2*beta+EXTERNAL
    margin=lam*RADIUS-additive
    assert lam>0 and margin>0
    assert 1+DELTA*ALO-DELTA*GAIN>=0
    cap_service=g*F(1,2)
    actual_service=g*F(4,5)
    assert actual_service>SERVICE and cap_service>SERVICE
    count=0; maximum=F(0); minimum_service=F(100)
    # The represented update is multi-affine in every rectangular variable.
    # Its infinity norm is convex in each coordinate, so corners suffice for
    # this OVERAPPROXIMATION; they are not all realizable soft-feedback cases.
    for beta_t in (F(0),beta):
        mass=1-beta_t
        for a,c in product((ALO,AHI),repeat=2):
            for x,err,badflow,dist in product(product((-RADIUS,RADIUS),repeat=2),
                    product((-COMMAND_ERROR,COMMAND_ERROR),repeat=2),
                    product((F(0),F(4)),repeat=2),product((-EXTERNAL,EXTERNAL),repeat=2)):
                flow=tuple(mass*(2+GAIN*x[k]+err[k])+beta_t*badflow[k] for k in range(2))
                nxt=(x[0]+DELTA*(a*x[0]+c*x[1]+2-flow[0]+dist[0]),
                     x[1]+DELTA*(c*x[0]+a*x[1]+2-flow[1]+dist[1]))
                assert max(map(abs,nxt))<=RADIUS
                assert min(flow)>=SERVICE
                maximum=max(maximum,*map(abs,nxt)); minimum_service=min(minimum_service,*flow)
                count+=1
    return {'name':name,'weights':list(map(qstr,weights)),'bad_weight_bound':qstr(beta),
            'lambda_lower':qstr(lam),'additive_bound':qstr(additive),
            'radius_margin':qstr(margin),'cap_only_actual_service':qstr(cap_service),
            'soft_policy_actual_service':qstr(actual_service),'affine_envelope_corners':count,
            'maximum_envelope_successor_radius':qstr(maximum),
            'minimum_envelope_corner_service':qstr(minimum_service)}


def clip_a(a):
    return min(F(1),max(F(0),a))


def access_startup_checks():
    cases=0
    for a0 in (F(i,16) for i in range(17)):
        for opposition in product((F(0),F(3,4)),repeat=4):
            a=a0
            for o in opposition:
                a=clip_a(a+1-o)
            assert a==1; cases+=1
    a=F(0)
    for _ in range(10):
        a=clip_a(a-F(3,4)); assert a==0
    # Source order: current a determines flow, then held g updates a.
    ordinary,missing=F(1),F(0)
    ordinary_history=[]; missing_history=[]
    for tick in range(25):
        ordinary_history.append(ordinary);missing_history.append(missing)
        held_g=F(0) if tick==0 else F(1)
        ordinary=clip_a(ordinary+held_g-F(3,4))
        missing=clip_a(missing+held_g-F(3,4))
    assert ordinary_history[1]==F(1,4) and ordinary_history[4]==1
    assert missing_history[1]==0 and missing_history[5]==1
    minima={}
    for name,beta,wmax in [('equal',F(5,34),F(1,34)),('weighted',F(3,17),F(3,85))]:
        values=[]
        for tick in range(25):
            # u0 throughout early drain. Thereafter a cap-only bound covers
            # either baseline or actually received legitimate feedback.
            per_engaged=F(2) if tick<16 else F(1,2)
            guaranteed=(1-beta-wmax)*ordinary_history[tick]*per_engaged
            guaranteed+=wmax*missing_history[tick]*per_engaged
            assert guaranteed>SERVICE
            values.append(guaranteed)
        expected=F(7,17) if name=='equal' else F(67,170)
        assert min(values)==expected
        minima[name]={'actual_service_lower':qstr(min(values)),
                      'minimum_tick':values.index(min(values))}
    startup_radius=F(1,2)+24*DELTA*DRIFT
    assert startup_radius<RADIUS
    return {'four_step_access_corner_cases':cases,'no_effort_same_opposition_stays_zero':True,
            'ordinary_engagement_prefix':list(map(qstr,ordinary_history[:6])),
            'initially_missing_engagement_prefix':list(map(qstr,missing_history[:6])),
            'startup_service':minima,'startup_ticks':24,'startup_radius_bound':qstr(startup_radius)}


def held_issue(issues,delays,t):
    delivered=[(s+d,s) for s,d in zip(issues,delays) if s+d<=t]
    if not delivered: return None
    latest=max(a for a,_ in delivered)
    # Tied arrival events may be processed so the older command remains last.
    return min(s for a,s in delivered if a==latest)


def timing_checks():
    count=0
    lag=2;issues=list(range(7))
    for delays in product(range(lag+1),repeat=len(issues)):
        for t in range(lag,len(issues)):
            s=held_issue(issues,delays,t)
            assert s is not None and t-2*lag<=s<=t
            count+=1
    # All delays here are at least one tick, so the negative witness does not
    # depend on a same-tick command-realization interpretation.
    issues=list(range(9)); delays=[1,1,1,4,1,4,4,4,4]
    assert held_issue(issues,delays,8)==3
    assert 8==4+4  # first fresh issuance4 + one claimed latency4
    quiet_cases=0
    issues=[0,16,17,18]
    for delays in product(range(1,5),repeat=4):
        for t in range(20,25):
            s=held_issue(issues,delays,t)
            assert s is not None and s>=16
            quiet_cases+=1
    effect_error=F(1,500)+22*DELTA*DRIFT
    assert effect_error<ETA
    return {'held_age_exhaustive_checks':count,'positive_envelope_lag':lag,
            'generic_held_age_bound_factor':2,
            'one_lag_flush_counterexample':{'issue_times':list(range(9)),
                 'delays':[1,1,1,4,1,4,4,4,4],'first_feedback_issue':4,
                 'checked_time':8,'still_held_issue':3},
            'quiet_drain_checks':quiet_cases,'quiet_drain_first_feedback':16,
            'quiet_drain_valid_hold_by':20,'conservative_generic_valid_hold_by':24,
            'sample_to_effect_age_bound':22,'source_effect_error_bound':qstr(effect_error),
            'design_error':qstr(ETA)}


def resource_checks():
    n,b,normal_senders=N,BAD,4
    costs={'transmission':F(normal_senders*n+b*64),
           'samples':F(2*(normal_senders+2*b)),
           'cpu':F(n,5),'independent_io':F(n*4096,1000000),'maintenance_fields':F(2*n),
           'deployment':F(n),'flow':F(8*n),'selector_drive_hold':F(n),
           'acquisition_onset':F(2)}
    total=sum(costs.values(),F(0)); assert total==F(14077176,15625)<901<=1000
    initial_sample_liability=F(2*2*n)
    assert 1000-initial_sample_liability==864>0
    p_count=2*n+2*n+n+n+1; assert p_count==205
    assert F(p_count,100000)==PBAR
    # These exact stock updates cover both capacity saturation and low stock;
    # the general pointwise proof is algebraic and encoded in Lean.
    count=0
    for stock,supply,cost in product((F(0),F(1000),F(1500),F(2000)),
            (total,F(901),F(1000)),(F(0),total)):
        nxt=min(F(2000),stock+supply-cost)
        assert nxt>=stock>=0 and nxt<=2000
        count+=1
    initial_checks=0
    for stock,supply,ordinary,extra in product((F(1000),F(1500)),
            (total,F(901),F(1000)),(F(0),total),(F(0),initial_sample_liability)):
        nxt=min(F(2000),stock+supply-ordinary-extra)
        assert nxt>=864 and nxt<=2000
        initial_checks+=1
    necessary_equal=F(3,5)/F(1,34)
    necessary_weighted=F(3,5)/F(3,85)
    assert necessary_equal==F(102,5) and necessary_weighted==17
    assert 89*necessary_weighted>1500
    return {'pointwise_cost_terms':{k:qstr(v) for k,v in costs.items()},
            'total_actual_cost_upper':qstr(total),'sufficient_supply':901,
            'separate_io_word_bound_per_body':4096,
            'initial_sample_liability':qstr(initial_sample_liability),
            'initial_stock_floor':864,'initial_stock_checks':initial_checks,
            'side_effect_operation_cap':p_count,'pbar':qstr(PBAR),
            'stock_corner_checks':count,'necessary_service_only_rate_equal':qstr(necessary_equal),
            'necessary_service_only_rate_weighted':qstr(necessary_weighted),
            'zero_supply_no_89_full_service_ticks_from_max_initial_stock':True,
            'scope':'upper sufficient demand and lower necessary actual flow cost are different bounds'}


def result():
    records={'policy':policy_checks(),
             'equal':branch_certificate('equal',[F(1,N)]*N),
             'weighted':branch_certificate('weighted',[F(2,85)]*17+[F(3,85)]*17),
             'access_startup':access_startup_checks(),'timing':timing_checks(),
             'resources':resource_checks()}
    names=('CONTROL.md','Control.lean','control_model.py','INSTANCE.md')
    hashes={n:hashlib.sha256((HERE/n).read_bytes().replace(b'\r\n',b'\n')).hexdigest() for n in names}
    return {'schema':'byzantine-recurring-control-v1','status':'passed',
            'scope':'conditional source interfaces, exact policy/envelope/phase/resource checks; not full RN/IA completion',
            'sources_sha256_lf':hashes,'parameters':{'roles':N,'conditional_impaired_bound':BAD,
                'gain':qstr(GAIN),'rule_threshold':qstr(RULE),'error_design':qstr(ETA),
                'rounding_allowance':qstr(ROUND),'radius':qstr(RADIUS),'delta':qstr(DELTA),
                'all_input_rate_bound':qstr(DRIFT)},'checks':records}


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    mode=ap.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write',action='store_true');mode.add_argument('--check',action='store_true')
    args=ap.parse_args(); actual=result();out=HERE/'control_results.json'
    encoded=json.dumps(actual,indent=2,sort_keys=True)+'\n'
    if args.write:
        out.write_text(encoded,encoding='utf-8',newline='\n')
        print('WROTE exact recurring control record')
    else:
        expected=out.read_text(encoding='utf-8')
        if expected!=encoded: raise RuntimeError('stored recurring control record differs')
        print('PASS exact recurring control/access/resource record')


if __name__=='__main__': main()

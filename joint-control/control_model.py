from fractions import Fraction as F
from itertools import product, combinations
import argparse, json
from pathlib import Path

HERE = Path(__file__).resolve().parent
N, FAULT = 13, 4
K, R, ETA = F(8,5), F(4,5), F(3,50)
DELTA, ALO, AHI = F(1,1000), F(9,200), F(11,200)
OMEGA, SERVICE = F(1,50), F(3,10)


def textq(q):
    q=F(q)
    return f'{q.numerator}/{q.denominator}'


def corner_check():
    # Each rectangular variable enters the one-step relation multi-affinely.
    # Good-estimate averages and hostile-output averages range in these boxes.
    # Exhausting corners therefore bounds EVERY point in this overapproximation.
    count=0; maximum=F(0); min_service=F(10); argmax=None
    for bad in range(FAULT+1):
        good=N-bad
        for a,c in product((ALO,AHI),repeat=2):
            for x in product((-R,R),repeat=2):
                for error in product((-ETA,ETA),repeat=2):
                    for hostile in product((F(-2),F(2)),repeat=2):
                        for disturbance in product((-OMEGA,OMEGA),repeat=2):
                            effects=tuple(F(good,N)*K*(x[j]+error[j])+F(bad,N)*hostile[j] for j in range(2))
                            nxt=(x[0]+DELTA*(a*x[0]+c*x[1]-effects[0]+disturbance[0]), x[1]+DELTA*(c*x[0]+a*x[1]-effects[1]+disturbance[1]))
                            throughput=tuple(2+effects[j] for j in range(2))
                            assert all(abs(z)<=R for z in nxt)
                            assert all(y>=SERVICE for y in throughput)
                            assert all(abs(K*(x[j]+error[j]))<=2 for j in range(2))
                            count+=1
                            peak=max(map(abs,nxt)); low=min(throughput)
                            if peak>maximum: maximum=peak; argmax=dict(bad=bad,a=textq(a),c=textq(c),x=list(map(textq,x)),error=list(map(textq,error)),hostile=list(map(textq,hostile)),disturbance=list(map(textq,disturbance)))
                            min_service=min(min_service,low)
    lam=K*F(N-FAULT,N)-2*AHI
    additive=K*ETA+F(2*FAULT,N)+OMEGA
    margin=lam*R-additive
    assert margin>0
    service=F(N-FAULT,N)*(2-K*(R+ETA))
    assert service>SERVICE
    # Delay/quantization consumes actual elapsed time and bounded input growth.
    speed=2*AHI+2+OMEGA
    info_error=F(1,500)+DELTA*20*speed
    effect_error=info_error+DELTA*4*speed+F(1,1000)/K
    assert effect_error<=ETA
    startup=F(1,2)+24*DELTA*speed
    assert startup<=R
    return dict(corner_count=count,maximum_next_norm=textq(maximum),minimum_corner_throughput=textq(min_service),worst_corner=argmax,lambda_bound=textq(lam),additive_bound=textq(additive),strict_radius_margin=textq(margin),uniform_service_floor=textq(service),info_error=textq(info_error),effect_error_including_command_quantization=textq(effect_error),startup_radius_24ticks=textq(startup),source_query_preserved=True)


def no_repair_witness():
    # After eight sequential acquisitions/releases, each poisoned executable
    # emits -2 persistently. Only one active acquisition at a time is needed.
    # Intact paths are given MAXIMUM inward influence, stronger than any policy.
    bad=8
    outward=-F(2*(N-2*bad),N)
    min_growth=DELTA*(outward-F(1,10))
    assert min_growth>0
    bound=(F(2)/min_growth).numerator//(F(2)/min_growth).denominator+1
    linear_escape=F(-1)+bound*min_growth
    assert linear_escape>1
    return dict(persistent_poisoned_targets=bad,current_access_needed=1,acquisition_spacing=490,events=8,minimum_growth_while_safe=textq(min_growth),uniform_escape_bound_ticks=bound,certified_mean_lower_bound_at_escape=textq(linear_escape),scope='Architecture ablation disables all halt/write/boot or substitute restorative effects on poisoned paths; unrestricted remaining policies cannot overcome their persistent output.')


def energy_checks():
    # I proves25L+500 per recipient, including actual pre-admission/CPU costs
    # and amplified requests. Source power caps separately charge1300/tick
    # for ten whole compromised footprints,104 actuation and4 maintenance.
    baseline=104+1300+4; rate=baseline+325; burst=6500
    supply=1734; cap=7500
    assert rate<supply
    e=burst; minimum=e; ticks=10000
    for t in range(ticks):
        cost=rate+(burst if t==0 else 0)
        e=min(cap,e+supply-cost)
        assert e>=0
        minimum=min(minimum,e)
    aligned=burst; aligned_min=aligned
    for t in range(ticks):
        cost=baseline+13+(2730 if t%10==0 else 0)
        aligned=min(cap,aligned+supply-cost)
        assert aligned>=0
        aligned_min=min(aligned_min,aligned)
    # Actual 16-bit requests and64-bit replies, with thirteen requester
    # phases covering all ten ticks. Each provider takes ONE shared sample
    # per tick, not one sample per recipient. Replies occupy three lanes.
    phases=list(range(10))+[0,1,2]
    def starts(t):
        return 0 if t<0 else sum(t%10==p for p in phases)
    def physical_query_cost(t):
        requests=42*starts(t)
        samples=42 if starts(t-1)>0 else 0
        replies=14*sum(starts(t-j) for j in (3,4,5))
        return F(requests*16,64)+2*samples+replies
    def query_cpu_upper(t):
        # Eight bounded ops per formatted/parsed bit,924 sorting ops per
        # publication, and<=30000 aggregate housekeeping ops per tick.
        request_ops=42*(starts(t)+starts(t-1))*16*8
        replies=14*sum(starts(t-j) for j in (3,4,5))
        reply_ops=2*replies*64*8
        sort_ops=924*starts(t-8)
        return F(request_ops+reply_ops+sort_ops+30000,10000)
    physical_period=sum(physical_query_cost(t) for t in range(30,40))
    cpu_period=sum(query_cpu_upper(t) for t in range(30,40))
    assert physical_period==F(3045,2)  #1522.5 per10, not2478/2730
    assert physical_period+52*10>200*10
    assert physical_period+cpu_period<200*10
    # Every interval has at most two partial10-tick periods.
    query_burst=2*(physical_period+cpu_period)
    assert query_burst<burst
    assert 42*16<=1024 and 14*64<=1024 and 2*64<=1024
    assert max(42*16*8,14*64*8,924)+500<10000
    assert 2*16*8+2*64*8+500<10000
    query_only=F(burst); min_query=query_only
    upper_stock=F(burst); t=0
    while upper_stock>=0:
        # Ignoring ALL actual CPU energy is favorable to the combined
        # system. Its upper stock still becomes negative, so actual payment
        # must fail no later than this certified deadline.
        upper_stock=min(F(cap),upper_stock+200-(physical_query_cost(t)+52))
        query_only=min(F(cap),query_only+200-(physical_query_cost(t)+query_cpu_upper(t)))
        assert query_only>=0
        min_query=min(min_query,query_only)
        t+=1
    return dict(background_rate=baseline,inquiry_interval_rate=325,inquiry_interval_burst=burst,combined_interval_rate=rate,supply=supply,capacity=cap,initial_interval=[burst,cap],maximal_envelope_ticks=ticks,maximal_envelope_min_stock=minimum,periodic_aligned_min_stock=aligned_min,shared_failure_supply=200,shared_failure_by_tick=t,combined_stock_upper_bound_at_deadline=textq(upper_stock),actual_query_physical_cost_per10=textq(physical_period),query_cpu_upper_per10=textq(cpu_period),query_only_rate_upper=textq((physical_period+cpu_period)/10),query_only_burst_upper=textq(query_burst),query_only_min_stock=textq(min_query),requester_phases=phases,request_bits=16,reply_lane_rows=14,operation_count_bound=810,operation_effect_bound=textq(F(810,100000)),scope='Positive proof uses upper envelopes. Negative composition witness bills actual shared samples/transmitted bits; CPU omitted from failure lower charge and bounded for separate feasibility.')


def phase_check():
    r0=F(6889,12500)
    lam=K*F(8,13)-2*AHI
    additive=K*ETA+F(10,13)+OMEGA
    increment=DELTA*(additive-lam*r0)
    assert increment>0
    for t in range(490):
        bound=r0+t*increment
        assert bound<=R
        assert (1-DELTA*lam)*bound+DELTA*additive<=bound+increment
    service=F(8,13)*(2-K*(R+ETA))
    assert service>SERVICE
    return dict(temporary_bad_bound=5,additional_phase_ticks=489,initial_radius=textq(r0),radius_bound_at_phase_end=textq(r0+489*increment),temporary_actual_service=textq(service),note='Optional conservative initial-contamination reserve; not an indefinite F5 invariant.')


def weighted_check():
    weights=[F(101,1300)]*6+[F(99,1300)]*6+[F(100,1300)]
    assert sum(weights)==1
    masses=[sum((weights[i] for i in indices),F(0)) for size in range(5) for indices in combinations(range(N),size)]
    beta=max(masses)
    assert beta==F(101,325)
    lam=K*(1-beta)-2*AHI
    additive=K*ETA+2*beta+OMEGA
    assert additive<lam*R
    service=(1-beta)*(2-K*(R+ETA))
    assert service>SERVICE
    count=0
    for bad_mass in (F(0),beta):
        good_mass=1-bad_mass
        for a,c in product((ALO,AHI),repeat=2):
            for x,error,hostile,disturbance in product(product((-R,R),repeat=2),product((-ETA,ETA),repeat=2),product((F(-2),F(2)),repeat=2),product((-OMEGA,OMEGA),repeat=2)):
                effect=tuple(good_mass*K*(x[j]+error[j])+bad_mass*hostile[j] for j in range(2))
                nxt=(x[0]+DELTA*(a*x[0]+c*x[1]-effect[0]+disturbance[0]),x[1]+DELTA*(c*x[0]+a*x[1]-effect[1]+disturbance[1]))
                assert max(map(abs,nxt))<=R
                assert min(2+effect[j] for j in range(2))>=SERVICE
                count+=1
    heavy_weights=[F(2,3)]+[F(1,36)]*12
    assert sum(heavy_weights)==1
    heavy_growth=DELTA*(F(2,3)-F(1,10))
    assert heavy_growth>0 and -1+3530*heavy_growth>1
    return dict(single_current_hostile_weight='2/3',single_hostile_minimum_mean_growth=textq(heavy_growth),single_hostile_escape_bound=3530,weights=list(map(textq,weights)),fault_subsets_checked=len(masses),worst_four_path_mass=textq(beta),lambda_bound=textq(lam),additive_bound=textq(additive),radius_margin=textq(lam*R-additive),actual_service_floor=textq(service),multi_affine_corners=count)


def overintervention_witness():
    # False high-state evidence, accepted without robust inquiry/decoding,
    # induces every physical path to act at+1.6 while the true state is-.5.
    x=F(-1,2); steps=0
    while x>=-1:
        x=x+DELTA*(F(1,10)*x-K)
        steps+=1
    return dict(initial=textq(F(-1,2)),false_estimate='1/1',actual_command=textq(K),unsafe_tick=steps,unsafe_value_upper_bound=textq(F(-((-x.numerator*10**9)//x.denominator),10**9)),scope='Ablated evidence protection; excessive otherwise physically legal intervention violates the lower protected bound.')


def result():
    return {'schema':'byzantine-joint-control-v1','verification':'exact rational multi-affine vertex certificate plus analytic-proof regression witnesses; not independent audit', 'parameters':{'n':N,'effective_bad_bound':FAULT,'gain':textq(K),'invariant_radius':textq(R),'effect_error_bound':textq(ETA),'delta':textq(DELTA),'drift_interval':[textq(ALO),textq(AHI)],'disturbance_and_operation_bound':textq(OMEGA),'service_requirement':textq(SERVICE)},'control':corner_check(),'no_repair':no_repair_witness(),'energy':energy_checks(),'initial_contamination_phase':phase_check(),'heterogeneous_influence':weighted_check(),'overintervention':overintervention_witness()}

if __name__=='__main__':
    ap=argparse.ArgumentParser(); ap.add_argument('--check',action='store_true'); args=ap.parse_args()
    out=HERE/'control_results.json'; actual=result(); encoded=json.dumps(actual,indent=2,sort_keys=True)+'\n'
    if args.check:
        assert out.read_text(encoding='utf-8')==encoded, 'stored results differ'
        print('PASS exact rational control certificate and reproduced witnesses')
    else:
        out.write_text(encoded,encoding='utf-8'); print('WROTE control_results.json')

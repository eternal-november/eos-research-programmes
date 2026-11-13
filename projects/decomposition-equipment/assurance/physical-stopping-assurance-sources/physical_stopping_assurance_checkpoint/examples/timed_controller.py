"""Exact synthetic physical-interface bridge; no hardware validation claimed."""
import json, itertools, math, hashlib
from pathlib import Path
from fractions import Fraction
HERE=Path(__file__).resolve().parent
BASE=HERE/'inputs'
CAND=json.loads((BASE/'executable_candidate.json').read_text())
GROUP=next(g for g in CAND['joint_innovation_interfaces'] if g['members']==[0,5,10])
PORTS=[0,5,10]
# micrometres, mm/s, 10ms ticks; trained prediction step is one trial.
DT_MS=10; COMPUTE_MS=10; SAMPLE_CHECKPOINT_MS=100; WATCHDOG_MS=310; ACTUATION_MS=10
ACCEL=1000; SPEEDS=(0,700,800,900,1000,1100,1200)
N=sum(GROUP['counts']); EPS=Fraction(13247,1000000); ALPHA=Fraction(1,10)
assert EPS*EPS>=Fraction(46,2*N)

def mean(actions,runs):
    x=list(actions)
    for h in range(1,5):x += [int(r>=h) for r in runs]
    return [int(m['intercept']+sum(w*x[c] for c,w in m['linear'])+sum(w*x[a]*x[b] for a,b,w in m['interactions'])) for m in CAND['mean']]

def clamp(x,l,u):return max(l,min(u,x))
def physical(y):
    # Stipulated calibration map, not inferred physics. Future trial telemetry only.
    sensing=clamp(150+50*y[0],0,1000)
    network=clamp(150+50*y[1],0,1000)
    brake=clamp(2500+500*y[2],500,5000)
    return sensing,network,brake

def simulate(speed, y, clearance_um, packet_loss=False, watchdog=True, omit_compute=False):
    sensing,network,brake=physical(y)
    t=0;x=0;v=0; trace=[]
    # Known drive upper envelope, saturated acceleration until requested speed.
    while v<speed:
        nv=min(speed,v+ACCEL//100);x+=5*(v+nv);v=nv;t+=10
        trace.append((t,x,v,'accelerate'))
    cruise_start=t
    stop_request=SAMPLE_CHECKPOINT_MS+sensing+(0 if omit_compute else COMPUTE_MS)
    arrival=10**9 if packet_loss else stop_request+network
    brake_at=(min(arrival,WATCHDOG_MS) if watchdog else arrival)+ACTUATION_MS
    # Model contract discretizes delays to 10 ms; watchdog physical deadline includes path delay.
    if brake_at>10000:return {'collision':True,'unbounded_no_brake':True,'stop_um':None,'trace':trace}
    while t-cruise_start<brake_at:
        x+=10*v;t+=10;trace.append((t,x,v,'cruise-or-command-wait'))
    while v:
        nv=max(0,v-brake//100);x+=5*(v+nv);v=nv;t+=10
        trace.append((t,x,v,'brake'))
    return {'collision':x>=clearance_um,'stop_um':x,'stop_ms':t,'brake_onset_ms':cruise_start+brake_at,'trace':trace}

def outcomes(actions,runs):
    m=mean(actions,runs)
    return [(tuple(m[p]+z for p,z in zip(PORTS,row)),Fraction(c,N)) for row,c in zip(GROUP['rows'],GROUP['counts'])]

def bound_table(actions,runs,clearance_um,alpha=ALPHA):
    out=[]
    for v in SPEEDS:
        if not v:out.append({'speed':0,'model_risk':0.,'risk_upper':0.,'worst_stop_um':0,'accepted':True});continue
        oo=outcomes(actions,runs)
        rr=[(simulate(v,y,clearance_um),p) for y,p in oo]
        risk=sum((p for r,p in rr if r['collision']),Fraction())
        support_safe=not any(r['collision'] for r,p in rr)
        upper=Fraction(0) if support_safe else min(Fraction(1),risk+EPS)
        out.append({'speed':v,'model_risk':float(risk),'risk_fraction':str(risk),'all_structural_outcomes_safe':support_safe,'risk_upper':float(upper),'risk_upper_fraction':str(upper),'worst_stop_um':max(r['stop_um'] for r,p in rr),'accepted':upper<=alpha})
    return out

def admission(actions,runs,packet,now_ms,history_known=True):
    # At rest. Packet authority/timestamp/calibration explicit; no hidden mode access.
    if not history_known or packet['source']!='clearance_sensor_1' or packet['timestamp_ms']>now_ms or now_ms-packet['timestamp_ms']>100 or packet['error_um']<0 or not packet.get('rest_since_capture',False):return 0,[]
    # Static boundary and stationary initial condition: age doesn't consume distance;
    # age restriction guards validity, NOT a claim timestamps imply calibration.
    lower=packet['distance_um']-packet['error_um']-packet['reserve_um']
    if lower<=0:return 0,[]
    table=bound_table(actions,runs,lower)
    return max(r['speed'] for r in table if r['accepted']),table

def main():
    actions=[-1]*12;runs=[0]*12;clearance=1260000
    packet={'source':'clearance_sensor_1','timestamp_ms':0,'distance_um':1280000,'error_um':10000,'reserve_um':10000,'rest_since_capture':True}
    chosen,table=admission(actions,runs,packet,0)
    worst=max(r['speed'] for r in table if r['worst_stop_um']<clearance)
    assert chosen==1000 and worst==900,(chosen,worst,table)
    traces=[]
    for y,p in outcomes(actions,runs):
        r=simulate(chosen,y,clearance);traces.append({'future_telemetry':y,'probability':str(p),**{k:v for k,v in r.items() if k!='trace'}})
    # Replacing the genuine joint event by independent marginal draws loses advantage.
    marginals=[sum(Fraction(c,N) for z,c in zip(GROUP['rows'],GROUP['counts']) if z[j]==1) for j in range(3)]
    independent_risk=sum((math.prod(marginals[j] if row[j]==1 else 1-marginals[j] for j in range(3)) for (y,p),row in zip(outcomes(actions,runs),GROUP['rows']) if simulate(chosen,y,clearance)['collision']),Fraction())
    # Missing histories must fail closed before motion; watchdog packet loss need not be safe.
    assert admission(actions,runs,packet,101)[0]==0
    assert admission(actions,runs,packet,0,False)[0]==0
    missing=[{'telemetry':y,'stop_um':simulate(chosen,y,clearance,packet_loss=True)['stop_um'],'collision':simulate(chosen,y,clearance,packet_loss=True)['collision']} for y,p in outcomes(actions,runs)]
    assert any(x['collision'] for x in missing)
    warm_runs=[0]*12;warm_runs[10]=2
    warm_lost_ack=[simulate(1100,y,clearance,packet_loss=True) for y,p in outcomes(actions,warm_runs)]
    assert all(not r['collision'] for r in warm_lost_ack)
    assert max(r['stop_um'] for r in warm_lost_ack)==1259500
    uncalibrated_brake=simulate(1100,(-3,-3,-4),clearance,packet_loss=True)
    assert uncalibrated_brake['collision']
    # Omitted compute time gives false geometric assurance at tighter clearance.
    timing=[]
    for y,p in outcomes(actions,runs):
        a=simulate(chosen,y,1315000,omit_compute=True);b=simulate(chosen,y,1315000)
        if not a['collision'] and b['collision']:timing.append({'y':y,'incorrect_stop_um':a['stop_um'],'actual_stop_um':b['stop_um']})
    assert timing
    # Find same current action and last one action, different older history requiring different decision.
    history=[]
    for channel in range(12):
        for r in range(1,4):
            r1=[0]*12;r2=[0]*12;r1[channel]=r;r2[channel]=r+1
            p2=dict(packet,distance_um=557000); v1,t1=admission(actions,r1,p2,0);v2,t2=admission(actions,r2,p2,0)
            if v1!=v2:history.append({'channel':channel,'runs':[r,r+1],'speeds':[v1,v2],'shared_recent_actions':r,'clearance_after_error_and_reserve_um':537000})
    assert history
    frontier=[]
    for r10 in range(5):
        rr=[0]*12;rr[10]=r10
        for aa in [Fraction(1,10),Fraction(1,1000),Fraction(1,10000),Fraction(0)]:
            tt=bound_table(actions,rr,clearance,aa)
            frontier.append({'channel10_runlength':r10,'risk_budget':str(aa),'selected_speed':max(x['speed'] for x in tt if x['accepted'])})
    # Replay memory from observed actions, not a hidden state label.
    replay=[]
    for npositive in [3,4]:
        rr=[0]*12
        for j in range(4):
            aa=[-1]*12;aa[10]=1 if j>=4-npositive else -1
            rr=[min(v+1,4) if a==1 else 0 for v,a in zip(rr,aa)]
        replay.append({'last4_action10':[-1]*(4-npositive)+[1]*npositive,'retained_run10':rr[10],'risk700_at530mm':next(x for x in bound_table(actions,rr,537000) if x['speed']==700)})
    result={'status':'synthetic executable bridge, not physical validation','existing_candidate_sha256':hashlib.sha256((BASE/'executable_candidate.json').read_bytes()).hexdigest(),'prediction_steps_per_trial':1,'physical_tick_ms':10,'tv_budget_H1_outward':str(EPS),'statistical_confidence_failure_upper':.0065+12/2**64,'alpha':float(ALPHA),'selected_speed_mm_s':chosen,'worst_case_speed_mm_s':worst,'speed_gain_fraction':str(Fraction(chosen-worst,worst)),'admission_table':table,'exact_outcomes':traces,'independent_marginal_model_risk':str(independent_risk),'packet_loss_fallback':missing,'warm_support_branch_lost_ack_all_safe':True,'warm_lost_ack_worst_stop_um':max(r['stop_um'] for r in warm_lost_ack),'uncalibrated_brake_counterexample_stop_um':uncalibrated_brake['stop_um'],'omitted_compute_failure':timing,'memory_decision_witnesses':history,'risk_speed_frontier':frontier,'causal_memory_replay':replay,'direct_full_joint_table_gives_same_risk':True,'physical_interface_assumption':'stipulated synthetic outcome telemetry->delay/braking calibration, static protected boundary, known acceleration envelope, local braking authority with included deadline'}
    (HERE/'timed_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ['admission_table','exact_outcomes','packet_loss_fallback','memory_decision_witnesses']},indent=2))
if __name__=='__main__':main()

"""Exact initial-entry, fixed-point WORLD and causal-return compatibility checks.

The mathematical prefix proof is in INITIAL-RETURN.md. This is not a simulation
of the whole indefinite source or a substitute for its physical boundary maps.
"""
from __future__ import annotations
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
import argparse
import ast
import json
import math
import sys
import geometry_model as gm
import program_model as pm

if sys.flags.optimize:
    raise RuntimeError('Unoptimized Python is required')
HERE=Path(__file__).resolve().parent


def require(ok,message):
    if not ok:raise AssertionError(message)


def serial(x):
    if isinstance(x,F):return str(x)
    if isinstance(x,dict):return {k:serial(v) for k,v in x.items()}
    if isinstance(x,(tuple,list)):return [serial(v) for v in x]
    return x


def digest(name):
    return sha256((HERE/name).read_text(encoding='utf-8-sig').replace('\r\n','\n').encode('utf-8')).hexdigest()


def inputs():
    record=json.loads((HERE/'geometry_results.json').read_text(encoding='utf-8-sig'))
    require(all(digest(n)==v for n,v in record['sources'].items()),'Geometry source record is stale')
    c,b,p,actual=gm.construct()
    require(record['timing']==serial(actual['timing']),'Current geometry arithmetic differs')
    return c,b,p,actual


def entry_and_deadline(c,b,p,g):
    k=c.constants;rate=F(p['instruction_service_max_per_quantum']);minimum=F(p['frame_min']);maximum=F(p['frame_max'])
    N=1<<26;allowed_drain_elapsed=N
    remaining_min=F(k['BOOT_DRAIN_STEPS']-allowed_drain_elapsed,1)/rate
    old_prefix_tail=F(p['boot_causal_tail'])
    require(remaining_min>old_prefix_tail,'Initial partial drain can publish old input')
    boot=F(b['boot_padded_upper']+16,1)/F(p['instruction_service_min_per_quantum'])
    plant_gate=(k['PLANT_ENTRY_FRAMES']-1)*minimum
    maintenance_gate=(k['ENTRY_FRAMES']-1)*minimum
    require(plant_gate>boot+p['arbitrary_counter_caps'][2]+4,'Initial plant gate omits old debt')
    require(maintenance_gate>boot+max(p['arbitrary_counter_caps'])+4,'Initial maintenance gate omits old debt')
    source_first_plant=boot+F(p['plant_period'])+2
    source_first_maintenance=boot+F(p['maintenance_period'])+2
    require(plant_gate>source_first_plant and maintenance_gate>source_first_maintenance,'Initial gate lacks genuine availability')
    ready=F(p['new_bank_entry_before_driver_geometry'])+10000
    commission=g['timing']['commissioning'];vmax=g['force']['speed'][1]
    first_new_power=F(k['POWER_AT'])/vmax
    first_old_loss=F(k['WARM_AT'])/vmax
    require(ready<commission<first_new_power,'Commissioning depends on an already renewed bank')
    require(first_old_loss-commission>g['timing']['work'],'Initial bank lacks a complete first work interval')
    t=g['timing'];H=t['conditional_return_H']
    sequence=t['partial']+t['abort']+2*t['half_cycle']+t['old_suffix']
    slack=F(H)-commission-sequence
    require(slack>0,'Return deadline has no strict prefix slack')
    # Uniform max(r,Tc)+sequence < r+H, including a release before Tc.
    for r in (F(0),commission/2,commission,commission+1,F(H),F(3*H)):
        require(max(r,commission)+sequence<r+H,'Return arithmetic uses future first-failure state')
    return dict(initial_drain_elapsed_max_instructions=allowed_drain_elapsed,remaining_drain_min=remaining_min,
        last_old_prefix_effect=old_prefix_tail,boot_upper=boot,plant_gate_min=plant_gate,maintenance_gate_min=maintenance_gate,
        first_genuine_plant_upper=source_first_plant,first_genuine_maintenance_upper=source_first_maintenance,
        ready_including_tracker_upper=ready,commissioning=commission,first_new_power_lower=first_new_power,
        first_old_effect_loss_lower=first_old_loss,initial_ready_window_lower=first_old_loss-commission,
        repair_sequence_without_commissioning=sequence,return_H=H,strict_return_slack=slack,
        proof_scope='initial canonical mechanical corridor and characterized formation prefixes; not arbitrary global state or near-expired debt gates')


def world_bridge(c,p,g):
    tau=F(1,10**7);xdot=F(5099,3000);rowrate=2*xdot;age=F(p['world_observation_to_last_effect'])
    raw=F(1,200);radius=F(c.constants['ROW_VERIFY_RADIUS'],1000)
    changing=raw+rowrate*tau*age
    validated=radius+changing
    require(2*changing<radius,'Good changing rows may fail final range validation')
    require(validated<=F(1,50),'Validation-only row envelope does not support aligned collar proof')
    inverse_floor=F(1,2000);output_floor=F(1,100)
    command_error=2*(changing+inverse_floor)+output_floor
    gamma_min=F(1,100);gamma_max=F(1,50)
    block=F(1000);blocks=10;initial_error=F(2)
    decay=initial_error/(1+gamma_min*block)**blocks
    lag=2*xdot*tau/gamma_min
    tracking_error=command_error+lag+decay
    require(tracking_error<F(1,25),'WORLD tracker error defeats the actual .84/.36 collar')
    m=72;bad=6;persistent=1;cap=4;adverse=bad+(cap-1)*persistent
    upper_flow=(F(m-bad)*F(84,100)-adverse)/m
    lower_flow=(F(m-bad)*F(36,100)+adverse)/m
    service=(F(m-bad)*F(3,10)-adverse)/m
    upper_margin=upper_flow-(F(61,100)+F(1,100)+F(2,100)+3*F(2,100)*F(1,100))
    lower_margin=(F(59,100)-F(1,100)-F(2,100)-3*F(2,100)*F(1,100))-lower_flow
    require(upper_margin==F(11,2500) and lower_margin==F(261,2500) and service==F(3,20),'Weighted collider calculation changed')
    true_upper=F(88,100)-tracking_error;true_lower=F(32,100)+tracking_error
    require(true_upper>F(84,100) and true_lower<F(36,100),'Actual tracker does not refine collar envelopes')
    startup_drift=xdot*tau*g['timing']['commissioning']
    require(startup_drift<F(1,20),'Initial unknown world can escape before maintained feedback')
    # Exact grid lemma: each recovered coordinate numerator is an integer.
    # Row errors<=20 and x>=640 imply n>=1240; x<=360 implies n<=760.
    control=lambda n:max(30,min(90,60+(2*((n//2)-500))//10))
    upper=[control(n) for n in range(1240,3001)]
    lower=[control(n) for n in range(-1000,761)]
    require(min(upper)==84 and max(lower)==36,'Integer inverse/control collar law failed')
    # Global exact equality to continuous feedback is false at ordinary cells.
    exact_inverse=F(1001,2);integer_inverse=1001//2
    continuous=F(60)+2*(exact_inverse-500)/10
    actual=60+(2*(integer_inverse-500))//10
    require(continuous!=actual,'Quantization contrast disappeared')
    return dict(tau=tau,absolute_state_rate=xdot,rank_one_rate=rowrate,effect_age=age,
        raw_head_error=raw,verification_radius=radius,available_generator_row_error=changing,
        validation_only_row_error=validated,inverse_floor_error=inverse_floor,command_floor_error_upper=output_floor,
        commanded_feedback_error=command_error,tracker_rate=[gamma_min,gamma_max],tracker_settle=block*blocks,
        contraction_block=block,contraction_blocks=blocks,residual_initial_error=decay,tracking_lag_error=lag,
        actual_tracking_error=tracking_error,actual_upper_collar_output_lower=true_upper,actual_lower_collar_output_upper=true_lower,
        retained_upper_collar_flow=upper_flow,retained_lower_collar_flow=lower_flow,
        inward_upper_margin=upper_margin,inward_lower_margin=lower_margin,service=service,startup_displacement_upper=startup_drift,
        integer_collar_cases=len(upper)+len(lower),quantization_contrast=dict(numerator=1001,continuous_hundredths=continuous,actual_hundredths=actual),
        rc=dict(capacitance=100,resistance=[F(1,2),F(1)],state_interval=[-1,1],stored_energy_each=50,
                source_power_each_upper=4,resistor_heat_each_upper=8,host_world_trackers=4,
                additional_host_storage=200,additional_source_power=16,instantaneous_resistor_heat_upper=32,
                interval_heat_envelope='200 + 16 L, by storage/input conservation; do not add capacitor release twice'),
        scope='raw projection error includes quantization; maintained availability proves candidate interval and excludes permanent .6 fallback; RC actual-output tracking is an explicit source construction')


def actual_world_instruction_checks(c):
    k=c.constants;cases=[]
    # Complete intended C; actual frame executes provider work then both row
    # searches and integer WORLD calculation. Stop at its actual first WORLD.
    samples=[(1135,1135,0),(865,865,2000),(1145,1145,0),(855,855,2000),(1001,1000,0)]
    for s,d,attack in samples:
        m=pm.Machine(c);m.W=[0]*len(m.W);p=pm.RawPorts(c)
        for origin in range(k['ORIGINS']):
            for bank in range(2):
                p.fast[(origin,bank,0)]=s if origin>=6 else attack
                p.fast[(origin,bank,1)]=d if origin>=6 else 2000-attack
        for key in range(3):p.fast[('head',key)]=1000
        m.enter('frame')
        while not any(e[0]=='world' for e in p.events) and m.steps<2000000:
            require(m.step(p),'Stored frame stopped before WORLD')
        require(any(e[0]=='world' for e in p.events),'Full-size WORLD instruction not reached')
        x=(s+d-1000)//2;y=(s-d+1000)//2
        expected=tuple(max(30,min(90,60+(2*(z-500))//10)) for z in (x,y))
        require(p.world_latch==expected and m.C==c.image,'Actual WORLD differs from integer derivation')
        cases.append(dict(sum_record=s,difference_record=d,six_bad_records=attack,actual_world=p.world_latch,executed_instructions=m.steps))
    # Missing all good row data is outside maintained availability and produces
    # actual fallback. Clipping alone cannot establish the invariant forever.
    m=pm.Machine(c);m.W=[0]*len(m.W);p=pm.RawPorts(c);m.enter('frame')
    while not any(e[0]=='world' for e in p.events) and m.steps<2000000:require(m.step(p),'Fallback frame blocked')
    require(p.world_latch==(60,60),'Missing-row fallback changed')
    return dict(cases=cases,missing_good_rows_actual_fallback=p.world_latch,
        scope='actual full-size frame prefix and WORLD instructions; observer/transport/world-plant physics supplied by the written source proof')


def recurrent_schedule(c,g):
    H=g['timing']['conditional_return_H'];period=41*H;rate=F(1,10*H);N=432
    starts=[];episodes=[]
    for cluster in range(N//3):
        origin=cluster*period
        for j,offset in enumerate((0,250,600)):
            domain=3*cluster+j;t=origin+offset
            starts.append(t);episodes.append((t,t+500,domain))
    count=0
    for i,left in enumerate(starts):
        for j in range(i,len(starts)):
            length=starts[j]-left
            require(j-i+1<=math.floor(3+rate*length),'Closed-endpoint burst envelope failed')
            count+=1
    events=sorted([(a,1,h) for a,b,h in episodes]+[(b,0,h) for a,b,h in episodes])
    active=set();peak=0
    for t,kind,h in events:
        if kind:active.add(h)
        else:active.remove(h)
        peak=max(peak,len(active));require(len(active)<=2,'Direct concurrency exceeded two')
    require(peak==2 and len({h for a,b,h in episodes})==N,'Schedule does not exercise concurrency and roster')
    earliest_new_power=F(c.constants['POWER_AT'])/g['force']['speed'][1]
    require(500<600<earliest_new_power,'Third acquisition need not precede old useful return')
    # The general construction permits adaptive phase waits while starts of
    # successive clusters stay >=40H apart. Each of the three offset sequences
    # has at most1+L/(40H) events, hence total<=3+3L/(40H)<=3+lambda L.
    require(F(3,40*H)<rate,'Causal phase waits would consume the arrival margin')
    bad_actions=[]
    for sign in (-1,1):
        m=pm.Machine(c);p=pm.RawPorts(c)
        m.C[:4]=[pm.encode(pm.LI,3,immediate=100*sign),pm.encode(pm.LI,4,immediate=-100*sign),
                     pm.encode(pm.IO,5,3,2,pm.PRIM['world']),pm.encode(pm.JMP,immediate=0)]
        for _ in range(80):require(m.step(p),'Admitted changed program did not execute')
        require(p.world_latch==(100*sign,-100*sign),'Independent coordinate deviations were duplicate labels')
        # Release changes nothing in this machine; ordinary wrong code continues.
        for _ in range(80):require(m.step(p),'Released altered code silently stopped')
        require(p.world_latch==(100*sign,-100*sign),'Raw release cleaned retained code/output')
        bad_actions.append(dict(actual_world_after_release=p.world_latch,ordinary_instructions_after_release=80))
    return dict(schematic_cluster_offsets=[0,250,600],direct_episode_duration=500,peak_direct_access=peak,
        closed_event_interval_checks=count,one_roster_domains=N,minimum_adaptive_cluster_spacing=40*H,
        arrival_rate=rate,general_count_bound='three sequences with spacing>=40H: count<=3+3L/(40H)<=3+lambda L',
        first_release=500,third_acquisition=600,phase0_new_power_lower=earliest_new_power,
        changed_actual_programs=bad_actions,
        scope='causal recurrent schedule construction plus actual malicious instructions; not a simulated global hybrid trajectory. A fresh phase0 supplies the strict nonreturn lower bound; waits preserve the envelope.')


class TripLatch:
    """Raw voltage/actual-contact latch; no code, permission or health input."""
    def __init__(self):
        self.enabled=True;self.armed=False;self.pending=False;self.resets=0;self.receipt_ttl=17
    def event(self,energy,zero=False,power_cross=False,old_instruction_done=True):
        require(not(zero and power_cross),'All-zero and positive power crossing are different actual events')
        self.receipt_ttl=max(0,self.receipt_ttl-1)
        self.pending=not old_instruction_done
        if energy<2:self.enabled=False
        if zero:self.armed=True;self.enabled=False
        if power_cross and self.armed and energy>=3 and not self.pending:
            self.enabled=True;self.armed=False;self.resets+=1
        return dict(cpu_fetch=self.enabled,source_sampler=self.enabled,force_replenishment=self.enabled,
            receipt_ttl=self.receipt_ttl,armed=self.armed,ordinary_pc_entry_count=self.resets)


def power_entry_checks(c,g):
    # Actual full-size helper is paused AFTER its physical guard but BEFORE
    # emitting the selected cut. Soft resumption preserves C yet uses the old
    # branch after the actual raw load has changed. This tests the interface
    # defect, not a complete nominal brownout trajectory at the chosen stocks.
    k=c.constants;base=k['TARGET_BASE'];m=pm.Machine(c);m.W=[0]*len(m.W);p=pm.RawPorts(c)
    view=pm.populated_view(c,0,0);p.set_view(0,view)
    m.W[base+k['STAGE_ID']]=1
    functional=3+k['VIEW_WORDS']
    for origin in range(k['ORIGINS']):
        for bank in range(2):
            p.fast[(origin,bank,functional+1)]=200
            p.fast[(origin,bank,functional+3)]=0
    expression=next(n for n in ast.walk(c.functions['helper']) if isinstance(n,ast.Expr)
        and isinstance(n.value,ast.Call) and getattr(n.value.func,'id',None)=='emit'
        and len(n.value.args)==5 and getattr(n.value.args[1],'id',None)=='CUT_PORT'
        and getattr(n.value.args[4],'id',None)=='FORCE')
    capture=c.line_spans['helper:'+str(expression.lineno)][0]
    m.enter('helper',(0,))
    while m.pc!=capture and m.steps<10000000:require(m.step(p),'Cannot reach the actual guarded cut branch')
    require(m.pc==capture,'Actual positive-cut branch not reached')
    before=m.steps;m.powered=False
    require(not m.launch(),'Power-off did not stop new instruction launch')
    for origin in range(k['ORIGINS']):
        for bank in range(2):p.fast[(origin,bank,functional+1)]=1200
    p.elapse(20000);m.powered=True
    while not any(e[0]=='command' for e in p.events) and m.steps-before<10000:require(m.step(p),'Soft resume stopped')
    require(p.fields.get((0,k['CUT_PORT'],1,0))==20,'Soft-resume stale-guard obstruction disappeared')
    probe=pm.Machine(c);probe.W=[0]*len(probe.W);probe.enter('permission',(base,1))
    require(probe.run(p,until_yield=False)=='halt' and probe.result()==0,'Current guard would not reject the changed actual load')
    latch=TripLatch();trace=[latch.event(1)]
    for _ in range(20):trace.append(latch.event(4))
    require(not latch.enabled and latch.resets==0 and latch.receipt_ttl==0,'Energy rise silently resumed old execution or froze receipts')
    trace.append(latch.event(4,power_cross=True))
    require(not latch.enabled,'A power crossing without actual retraction rearmed')
    trace.append(latch.event(4,zero=True,old_instruction_done=False))
    trace.append(latch.event(4,power_cross=True,old_instruction_done=False))
    require(not latch.enabled,'Rearm overlapped a funded old instruction')
    trace.append(latch.event(4,power_cross=True,old_instruction_done=True))
    require(latch.enabled and latch.resets==1 and not latch.armed,'Fresh geometric rearm did not start ordinary PC entry')
    reset_min=F(c.constants['RESET_LIMIT'])/g['force']['speed'][1]
    last_force=F(3+6)+F(1,1<<26)+F(1,64)
    require(reset_min>g['timing']['settle']+last_force,'Fresh reset corridor does not clear ALL old emitting banks')
    return dict(soft_resume=dict(captured_actual_pc=capture,executed_before_pause=before,
                actual_cut_after_resume=20,current_guard_result=0,
                scope='actual compiled control continuation under an insufficient soft-restart interface; no claim that the selected nominal stock trajectory realizes this pause'),
        trip_trace=trace,receipt_expiry_continues_while_off=True,
        reset_corridor_min=reset_min,all_bank_clear_and_field_tail_upper=g['timing']['settle']+last_force,
        rearm='actual all-activation-zero arms catch; later fresh power crossing with E>=Eon and completed old IR starts PC entry; current C/W/I are not declared clean',
        source_scope='latch failure belongs to its explicit physical component reach; no intact decision is relabeled due to false input')


def generate():
    c,b,p,g=inputs()
    result=dict(status='derived source-conditioned initial/return closure; independent review and physical-source admission remain separate',
        initial=entry_and_deadline(c,b,p,g),world=world_bridge(c,p,g),actual_world=actual_world_instruction_checks(c),
        recurrence_witness=recurrent_schedule(c,g),power_entry=power_entry_checks(c,g))
    result['sources']={n:digest(n) for n in ('INITIAL-RETURN.md','initial_return_model.py','GEOMETRY.md','geometry_model.py','geometry_results.json','PROGRAM.md','program_model.py','program_source.py','RETURN.md','CONTINUITY.md','ACQUISITION.md','STREAMING.md')}
    return serial(result)


def main():
    parser=argparse.ArgumentParser(description=__doc__);group=parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--write',action='store_true');group.add_argument('--check',action='store_true');args=parser.parse_args()
    result=generate();path=HERE/'initial_return_results.json'
    if args.write:path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n',encoding='utf-8',newline='\n')
    else:require(json.loads(path.read_text(encoding='utf-8-sig'))==result,'Initial-return record differs; inspect before rewriting')
    print('initial-return record '+('written' if args.write else 'matches'))

if __name__=='__main__':main()

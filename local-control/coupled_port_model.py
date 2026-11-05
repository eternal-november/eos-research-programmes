"""Exact checks for the common retained-state port certificate.

The finite assignment verifies nonempty generic feasibility; it is not the
full-program PORT-SOURCE inventory or its completion certificate.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
import json
from pathlib import Path
import sys
import subprocess

HERE=Path(__file__).resolve().parent
PORT_SOURCE_COMMIT='e6d10f4aa2027a29399bd4fd06535a797edd874b'
PREFIX='theories-and-designs/byzantine-control/local-control/'

def require(ok,message):
    if not ok: raise AssertionError(message)

def digest(name):
    return sha256((HERE/name).read_text(encoding='utf-8-sig').replace('\r\n','\n').encode()).hexdigest()

def encode(value):
    if isinstance(value,F): return str(value)
    if isinstance(value,dict): return {k:encode(v) for k,v in value.items()}
    if isinstance(value,(list,tuple)): return [encode(v) for v in value]
    return value

def coupled_storage_checks():
    # An incidence-level algebra/encoding test, not the program source point.
    B=((1,1,0),(0,-1,1))
    D=((1,0,0),(0,0,1))
    w=(F(1),)*3; a=(F(1),)*2
    lmin=(F(1),)*3; lmax=(F(3,2),)*3
    cmin=(F(1),)*2; cmax=(F(2),)*2
    rmin=(F(12),)*3; gmin=(F(16),)*2; k=F(2)
    pslack=[];qslack=[]
    for e in range(3):
        pslack.append(w[e]*rmin[e]/lmax[e]
            -sum(a[n]*abs(B[n][e])/lmin[e] for n in range(2))-k*w[e])
    for n in range(2):
        qslack.append(a[n]*gmin[n]/cmax[n]
            -sum(w[e]*abs(B[n][e])/cmin[n] for e in range(3))-k*a[n])
    require(min(pslack+qslack)>=0,'Shared-node storage compatibility fails')
    Finput=F(4)
    cases=0
    coefficient_cases=((tuple(lmin),tuple(cmin),F(12),F(16)),
        (tuple(lmax),tuple(cmax),F(13),F(17)),
        ((F(1),F(3,2),F(1)),(F(2),F(1)),F(12),F(17)))
    for phi in product((F(-3),F(0),F(3)),repeat=3):
      for q in product((F(-2),F(0),F(2)),repeat=2):
       for u in product((F(-1),F(1)),repeat=2):
        for j in product((F(-1),F(1)),repeat=2):
         for L,C,R,G in coefficient_cases:
            i=tuple(phi[e]/L[e] for e in range(3))
            v=tuple(q[n]/C[n] for n in range(2))
            y=tuple(sum(F(D[p][e])*i[e] for e in range(3)) for p in range(2))
            dp=tuple(sum(F(B[n][e])*v[n] for n in range(2))
                -sum(F(D[p][e])*u[p] for p in range(2))-R*i[e] for e in range(3))
            dq=tuple(j[n]-sum(F(B[n][e])*i[e] for e in range(3))-G*v[n]
                for n in range(2))
            def abs_rate(x,dx):
                return abs(dx) if x==0 else (dx if x>0 else -dx)
            W=sum(w[e]*abs(phi[e]) for e in range(3))+sum(a[n]*abs(q[n]) for n in range(2))
            dW=sum(w[e]*abs_rate(phi[e],dp[e]) for e in range(3))
            dW+=sum(a[n]*abs_rate(q[n],dq[n]) for n in range(2))
            require(dW<=Finput-k*W,'Absolute storage derivative loses a coupling')
            dE=sum(i[e]*dp[e] for e in range(3))+sum(v[n]*dq[n] for n in range(2))
            ports=sum(v[n]*j[n]-G*v[n]**2 for n in range(2))
            ports-=sum(u[p]*y[p] for p in range(2))+sum(R*x*x for x in i)
            require(dE==ports,'Incidence energy does not cancel internally')
            energy=sum(phi[e]**2/(2*L[e]) for e in range(3))
            energy+=sum(q[n]**2/(2*C[n]) for n in range(2))
            comparison=sum(w[e]**2*lmax[e] for e in range(3))
            comparison+=sum(a[n]**2*cmax[n] for n in range(2))
            inverse=max([1/(w[e]**2*lmin[e]) for e in range(3)]
                +[1/(a[n]**2*cmin[n]) for n in range(2)])
            require(W*W<=2*energy*comparison and energy<=W*W*inverse/2,
                'Physical energy and clearance-potential comparison fails')
            for n in range(2):
                require(abs(v[n])<=W/(a[n]*cmin[n]),'Effort decoder lost stored deformation')
            for p in range(2):
                require(abs(y[p])<=sum(abs(D[p][e])*abs(phi[e])/lmin[e]
                    for e in range(3)),'Physical current decoder fails')
            cases+=1
    # Clearing uses the same state, with a strict forced-radius margin.
    W0=F(64);target=F(8);steps=0
    require(Finput/k<=target/2,'Target lies below the forced storage radius')
    while 2**steps<2*W0/target:steps+=1
    require(W0/F(2**steps)+Finput/k<=target,'Finite clearance misses target')
    # One nonempty joint delivery/clearance assignment, on the SAME q,phi
    # rectangle. This verifies parameter feasibility, not the full program.
    qmax=F(32);pmax=F(50);ready=F(1);vready=F(5)
    qready=F(10);pready=F(3,2);spill=F(11);over=F(24)
    jmax=F(64);jmin=F(52);eta=F(1);delta=F(1,2)
    on_shunt=F(0);charger_conductance=F(1)
    require(pmax>=F(3,2)*(qmax+1),'Delivery flux face not inward')
    require(over*(qmax/2-spill)>jmax+pmax,'Delivery charge face not inward')
    require(qready<=spill and qmax/2>spill,'Spill-free delivery region is empty')
    require(jmin>pmax+eta and vready>1+2*F(3,2)*ready+delta,
        'Useful delivery lower faces lack strict headroom')
    require(min(F(63)-qready,jmax)>=jmin,'Current-limited charger lacks lower supply')
    delivery_cases=0
    for phi,q,L,C,R,body,source in product((-pmax,pmax),(-qmax,qmax),
            (F(1),F(3,2)),(F(1),F(2)),(F(1),F(2)),
            (F(-1),F(1)),(F(63),F(128))):
        current=phi/L;voltage=q/C
        charger=min(jmax,max(F(0),charger_conductance*(source-voltage)))
        overflow=over*max(F(0),abs(voltage)-spill)*(1 if voltage>=0 else -1)
        dp=voltage-body-R*current;dq=charger-on_shunt*voltage-overflow-current
        require(phi*dp<=0 and q*dq<=0,'Shared delivery rectangle is not invariant')
        input_power=source*charger;node_power=voltage*charger
        heat=(source-voltage)*charger
        require(heat>=0 and input_power==node_power+heat,
            'Actual charger transfer is not paid in the same energy balance')
        delivery_cases+=1
    aw=F(1,128);rate=F(400);forcing=1+aw*jmax;level=F(1,100)
    require(F(1200)/F(3,2)-aw>=rate,'Brake flux compatibility fails')
    require(aw*2048/2-1>=rate*aw,'Brake charge compatibility fails')
    require(forcing/rate<=level/2,'Safe-current level is unreachable at forced radius')
    Winit=pmax+aw*qmax;nclear=0
    while 2**nclear<2*Winit/level:nclear+=1
    require(Winit/F(2**nclear)+forcing/rate<=level,'Joint clearance misses actual current')
    joint=dict(storage_rectangle=dict(flux=pmax,charge=qmax),
        capacitor_range=[1,2],inductance_range=['1','3/2'],
        source_voltage_range=[63,128],source_current_cap=jmax,
        delivery_resistance_range=[1,2],delivery_shunt=on_shunt,
        charger_conductance=charger_conductance,overflow_slope=over,overflow_onset=spill,
        ready_current=ready,delivery_prefix=(qmax+qready)/eta+(pmax+pready)/delta,
        brake_resistance=1200,brake_shunt=2048,brake_weight=aw,brake_rate=rate,
        brake_forcing=forcing,safe_neck_current=level,
        clearance_bound=F(nclear)/rate,body_voltage_bound=1,
        residual_body_power=level,force_upper_from_clearance=level/aw,
        force_need_not_equal_current_bound=True,checked_delivery_faces=delivery_cases,
        states_retained_between_modes=True,
        physical_state_energy_upper=pmax*pmax/2+qmax*qmax/2,
        initial_clearance_potential=Winit,maximum_charger_input_power=128*jmax,
        full_program_instantiation=False)
    # Opposite currents cannot be identified just because one node sees zero.
    circulation=(F(1),F(-1))
    require(sum(circulation)==0 and sum(abs(x) for x in circulation)>0,
        'Hidden circulating state counterexample vanished')
    # A parallel diode capacitor does not absorb positive source input at zero.
    initial_strand_derivative=F(1,2)
    require(initial_strand_derivative>0,'False exact-zero brake counterexample lost')
    return dict(status='derived generic certificate; not a program source instantiation',
        incidence=B,boundary_incidence=D,channel_weights=w,node_weights=a,
        channel_compatibility_slack=pslack,node_compatibility_slack=qslack,
        checked_derivative_and_energy_cases=cases,common_rate=k,input_bound=Finput,
        clearance_potential_is_not_spendable_energy=True,
        clearance_example=dict(initial_potential=W0,target=target,halving_steps=steps,
            time_bound=F(steps)/k,retained_state_not_reset=True),
        joint_delivery_clearance_assignment=joint,
        current_cancellation_is_not_a_state_quotient=True,
        capacitor_diode_initial_current_derivative=initial_strand_derivative)


def force_and_time_checks():
    cases=0
    for q0,cs,ct,drift,dt,jump in product((F(-2),F(0),F(2)),
        (F(1),F(2)),(F(1),F(2)),(F(-3),F(0),F(3)),
        (F(0),F(1,4),F(2)),(F(-1,2),F(0),F(1,2))):
        q1=q0+drift*dt+jump
        upper=2*abs(q0)/cs+3*dt+abs(jump)
        require(abs(q1)/ct<=upper,'Force continuation lost compliance or a state jump')
        cases+=1
    q0=F(1);before=q0/2;after=q0
    work=q0*q0/2-q0*q0/4
    require(after>before and after==2*before and work>0,
        'Paid compliance-change force counterexample missing')
    time_cases=0
    for sigma in (F(1,16),F(1),F(16)):
        k=F(3,5);h=F(7,2);rate=F(2,11);power=F(123,7)
        require((sigma*k)*(h/sigma)==k*h,'Decay changes under units alone')
        require((sigma*rate)*(h/sigma)==rate*h,'Fault-rate product changes under units alone')
        require((sigma*power)*(h/sigma)==power*h,'Delivered energy changed under units alone')
        time_cases+=1
    return dict(force_endpoint_cases=cases,
        compliance_countercase=dict(retained_deformation=q0,force_before=before,
            force_after=after,actual_parameter_work=work),
        common_time_scale_cases=time_cases,
        state_jump_budget_remains_separate=True,
        physical_speedup_is_not_a_unit_conversion=True)


def transit_work_checks():
    # Coefficient identities in arbitrary positive d and nonnegative b.
    # No independent bank demand or resource baseline is selected here.
    a=F(4);k=F(1,10);eta_min=F(1,2)
    tcap=2/a;pin=(a+k)*tcap;upstream=pin/eta_min
    require(pin==F(41,20) and upstream==F(41,10),
        'Transit bleed or conversion loss was omitted')
    require(a-(a+k)==-k,'Retained E+T does not share the claimed drain')
    eon=(F(4),F(4),F(4))
    eoff=tuple(F(2,3)*x for x in eon)
    emax=(F(8),F(4),F(4));transit=(tcap,F(0),F(0))
    hysteresis=tuple(eon[i]-eoff[i]-transit[i] for i in range(3))
    total_off=tuple(4*eoff[i]-emax[i]-transit[i] for i in range(3))
    require(min(hysteresis)>0 and min(total_off)>0,
        'The retained transit defeats hysteresis or two-halving retirement')
    exp_lower=1+F(41,10)+F(41,10)**2/2+F(41,10)**3/6
    require(exp_lower>20,'Transit cold formation cannot deliver1.9d after1q')
    cold_margin=(F(1,2),F(-5),F(-4))
    require(cold_margin[0]*10+cold_margin[1]==0
        and cold_margin[0]*8+cold_margin[2]==0,
        'Six-quantum prefix demand/burst condition is misstated')
    return dict(parameter_order=['d_b','b_b','constant'],
        transit_rate=a,transit_bleed=k,minimum_converter_efficiency=eta_min,
        transit_capacity_per_d=tcap,transit_input_per_d=pin,upstream_input_per_d=upstream,
        hysteresis_margin_coefficients=hysteresis,
        four_Eoff_minus_Emax_and_transit_coefficients=total_off,
        cold_exponential_lower=exp_lower,cold_prefix_margin_coefficients=cold_margin,
        six_quantum_condition='d_b >= 10*b_b+8',
        initial_transit_charge_not_assumed=True,
        parameterized_in_authoritative_bank_demand=True)


def source_snapshot():
    names=('PORT-SOURCE.md','port_source_model.py','port_source_results.json')
    texts={name:subprocess.run(['git','show',PORT_SOURCE_COMMIT+':'+PREFIX+name],
        cwd=HERE,capture_output=True,encoding='utf-8',check=True).stdout.replace('\r\n','\n')
        for name in names}
    source=json.loads(texts['port_source_results.json'])
    require(all(sha256(texts[name].encode()).hexdigest()==expected
                for name,expected in source['sources'].items()),
            'Pinned source manifest differs from its source files')
    return source,{
        name:sha256(text.encode()).hexdigest() for name,text in texts.items()}


def primary_source_mechanical_checks(source):
    p=source['parameters'];m=p['mechanical'];given=source['mechanical']
    n=m['modules_per_host'];side=m['modules_per_braking_side']
    require(n==p['sides']*side and side==p['contacts_per_side'],
        'Actual bank/contact state partition changed')
    lm,lp,cm,cp=(F(m[key]) for key in ('L_min','L_max','C_min','C_max'))
    r,g=F(m['R_min']),F(m['G_min'])
    brow,bcol,drow=(F(m[key]) for key in ('hard_B_row_l1','hard_B_column_l1','hard_D_row_l1'))
    jhard,uhard=F(m['hard_j_l1']),F(m['hard_u_l1'])
    kh=F(given['k_hard']);kg=F(given['k_good'])
    hard_slacks=[r/lp-bcol/lm-kh,g/cp-brow/cm-kh]
    require(min(hard_slacks)>=0,'Primary raw remapping violates the common potential law')
    forcing=jhard+drow*uhard;W=forcing/kh
    require(W==F(given['W_hard']),'Raw state envelope is not source-derived')
    nominal_slacks=[r/lp-1/lm-kg,g/cp-1/cm-kg]
    require(min(nominal_slacks)>=0,'Intact bank-local modes lack common decay')
    Fside=side*F(m['nominal_u_abs_per_module'])+F(m['brake_j_l1_per_side'])
    target=F(given['W_clear_per_braking_side']);clear=F(given['clearance_time'])
    require(Fside/kg<=target/2,'Useful forced-radius margin is absent')
    halves=0
    while 2**halves<2*W/target:halves+=1
    require(clear>=F(halves)/kg,'Actual source wait does not buy clearance')
    rating=F(m['force_rating']);rho=cp/cm
    load_clear=target/(cm*rating)
    input_growth=jhard+brow*W/lm
    growth=input_growth/(cm*rating)
    age=F(source['base_binding']['functional_guard_horizon'])
    error=F(m['force_head_low_reading_error'])
    # The pinned main-P witness is the actual LOAD500 one-head/max interface.
    require(source['primary_force_witness']['actual_guard_verdicts']==[1,0],
        'Source lost its intact-execution primary-input witness')
    guard=rho*(F(1,2)+error)+growth*age
    require(guard<1 and load_clear+error<F(1,2),
        'Actual finite-head guard and useful clearance do not compose')
    on_i=tuple(F(x) for x in given['on_i_interval'])
    on_v=tuple(F(x) for x in given['on_v_interval'])
    keeper_potential=side*(lp*on_i[1]+cp*on_v[1])
    require(keeper_potential>target and keeper_potential<W,
        'A whole-host brake was silently substituted for bank-local clearance')
    H=W*W*max(1/lm,1/cm)/2
    max_jump=W*W*max(1/lm-1/lp,1/cm-1/cp)/2
    coeff_power=W*W*F(m['inverse_coefficient_rate_max'])/2
    require(H==F(given['mechanical_hard_storage']), 'Physical H bound differs')
    require(max_jump<=F(given['parameter_work_store_capacity']),
        'One admissible coefficient change lacks actual stored work capacity')
    require(coeff_power==F(given['continuous_parameter_work_rate']),
        'Coefficient work and recharge envelope differ')
    driver=(W/cm)*jhard
    received=(W/lm)*drow*uhard
    require(driver+received==F(given['hard_mechanical_absolute_port_power']),
        'Mechanical effort/flow input ceiling lost a port')
    dissipation=W*W*max(F(m['R_max'])/(lm*lm),F(m['G_max'])/(cm*cm))
    schedule=source['return_schedule']
    hold=F(schedule['previous_return_H']);hnew=F(schedule['conditional_return_H'])
    rate=F(schedule['original_raw_acquisition_rate'])
    require(hnew==hold+5*clear and rate==1/(10*hold),
        'Clearance changed the original time/rate comparison silently')
    cover=1+2+(F(3)+2*rate*hnew).__floor__()
    require(cover==6 and hnew>hold,'The fixed raw fault rate loses the common cover')
    require(F(schedule['phase_bounds']['0_prepared_isolate_shunt_cut_drain'])
        <F(schedule['unchanged_earliest_timeout']), 'Whole clearance stage can time out')
    require(F(schedule['unchanged_timer_job'])<=F(schedule['unchanged_nontransferable_ready_window']),
        'A nonexistent keeper interval was used')
    return dict(source_commit=PORT_SOURCE_COMMIT,actual_modules=n,modules_per_braking_side=side,
        hard_compatibility_slacks=hard_slacks,nominal_side_slacks=nominal_slacks,
        hard_forcing=forcing,hard_potential=W,physical_mechanical_energy_upper=H,
        braked_side_forcing=Fside,clearance_potential_level=target,
        concurrent_keeper_potential_upper=keeper_potential,
        whole_host_low_potential_not_required=True,
        conservative_halvings=halves,actual_clearance_time=clear,
        force_clearance_load=load_clear,force_continuation_multiplier=rho,
        force_continuation_growth=growth,actual_guard_horizon=age,
        actual_head_error=error,actual_force_guard_upper=guard,
        maximum_funded_parameter_jump=max_jump,continuous_parameter_work=coeff_power,
        driver_delivered_positive_power=driver,recipient_positive_backwork=received,
        mechanical_dissipation_peak=dissipation,
        original_raw_compromise_rate=rate,updated_return_H=hnew,effective_cover=cover,
        mechanical_scale_is_not_clock_rescaling=True,
        driver_conversion_and_complete_work_inventory_still_required=True,
        no_operating_bank_rate_selected=True,source_admitted=False)


def main():
    require(not sys.flags.optimize,'Unoptimized checks required')
    parser=argparse.ArgumentParser()
    mode=parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write',action='store_true')
    mode.add_argument('--check',action='store_true')
    args=parser.parse_args()
    names=('COUPLED-PORTS.md','coupled_port_model.py')
    hashes={name:digest(name) for name in names}
    source,source_hashes=source_snapshot()
    output=encode(dict(status='derived common port certificate; full source work inventory pending',
        authoritative_source=dict(commit=PORT_SOURCE_COMMIT,sources=source_hashes),
        primary_source_mechanics=primary_source_mechanical_checks(source),
        sources=hashes,certificate=coupled_storage_checks(),
        force_and_time=force_and_time_checks(),transit_work=transit_work_checks()))
    require(hashes=={name:digest(name) for name in names},'Suppliers changed during check')
    rendered=json.dumps(output,indent=2,sort_keys=True)+'\n'
    target=HERE/'coupled_port_results.json'
    if args.write:
        target.write_text(rendered,encoding='utf-8');print('coupled-port record written')
    else:
        require(target.read_text(encoding='utf-8')==rendered,'Coupled-port record differs')
        print('coupled-port record matches')

if __name__=='__main__':main()

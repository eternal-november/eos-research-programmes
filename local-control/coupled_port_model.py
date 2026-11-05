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

HERE=Path(__file__).resolve().parent

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


def main():
    require(not sys.flags.optimize,'Unoptimized checks required')
    parser=argparse.ArgumentParser()
    mode=parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write',action='store_true')
    mode.add_argument('--check',action='store_true')
    args=parser.parse_args()
    names=('COUPLED-PORTS.md','coupled_port_model.py')
    hashes={name:digest(name) for name in names}
    output=encode(dict(status='derived common port certificate; full source instantiation pending',
        sources=hashes,certificate=coupled_storage_checks()))
    require(hashes=={name:digest(name) for name in names},'Suppliers changed during check')
    rendered=json.dumps(output,indent=2,sort_keys=True)+'\n'
    target=HERE/'coupled_port_results.json'
    if args.write:
        target.write_text(rendered,encoding='utf-8');print('coupled-port record written')
    else:
        require(target.read_text(encoding='utf-8')==rendered,'Coupled-port record differs')
        print('coupled-port record matches')

if __name__=='__main__':main()

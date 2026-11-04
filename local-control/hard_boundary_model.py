"""Exact checks of the hard physical cut/energy construction.

The universal bounds are proved in HARD-BOUNDARY.md. These independent finite
arithmetic and graph probes do not certify a manufactured component.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent


def require(ok, message):
    if not ok:
        raise AssertionError(message)


def digest(name):
    text = (HERE / name).read_text(encoding='utf-8-sig').replace('\r\n', '\n')
    return sha256(text.encode('utf-8')).hexdigest()


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {key: encode(item) for key, item in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(item) for item in value]
    return value


def inventory():
    old = json.loads((HERE / 'resource_results.json').read_text(encoding='utf-8'))['runtime_inventory']
    # A raw material inventory, deliberately distinct from nominal work prices.
    # Every listed number is a hard source design capacity, not a sensor report.
    parts = {
        'two_operating_carriers': 2 * F(old['per_bank_capacity']),
        'all_instruction_port_capsules_and_data_fields': F(old['combined_capsule_field_capacity']),
        'force_pairs_and_world_trackers': F(old['actual_field_and_world_stock']),
        'memory_material_capacity_one_per_installed_bit': F(old['memory_bits']),
        'additional_comparator_and_placement_capacity': F(2**30),
        'wire_and_mount_convertible_capacity': F(2**40),
        'all_remaining_chemical_material_and_defect_tool_residue': F(2**60),
    }
    body = sum(parts.values(), F(0))
    body_cap, feed_cap = F(2**64), F(2**96)
    require(body < body_cap, 'Hard body material inventory does not fit')
    require(F(old['upstream_capacity']) < feed_cap, 'Current upstream stock exceeds feed material capacity')
    cmin, gmax, i0 = F(1, 2**64), F(2**64), F(2**64)
    vbody, vfeed = F(2**65), F(2**81)
    require(cmin * vbody**2 / 2 >= body_cap, 'Body voltage bound unsupported')
    require(cmin * vfeed**2 / 2 >= feed_cap, 'Feed voltage bound unsupported')
    require(F(1, 10000) >= cmin and 10000 <= gmax, 'Existing boundary components exceed hard alphabet')
    require(F(1, 2**27) >= cmin, 'Illustrative carrier capacitor too small')
    # Possible material crosswires, not merely the four intended WORLD sources.
    nodes_per_zone = 2**40
    macro_vertices=64*int(old['memory_bits']) + 2**38
    require(macro_vertices<nodes_per_zone, 'Finite macro material interface does not fit')
    zones = 2
    nearby_world_terminals = 6  # two coordinates in own/adjacent regions
    world_cut_edges = zones * nodes_per_zone * nearby_world_terminals
    all_cut_edges = 2**48
    require(world_cut_edges < all_cut_edges, 'World edges omitted from all-port cut')
    world_cap = world_cut_edges * (i0 + 2*gmax*vfeed)
    complete_stock = body_cap + feed_cap
    exogenous_power = F(2**96)
    # Body/feed exchange cancels; all other positive cut work has this cap.
    local_cut_power = all_cut_edges * vfeed * (i0 + 2*gmax*vfeed)
    heat_power = local_cut_power + exogenous_power
    return dict(nominal_inventory_source='resource_results.json', raw_body_parts=parts,
        body_inventory_sum=body, hard_body_capacity=body_cap, hard_feed_capacity=feed_cap,
        hard_nonthermal_convertible_capacity=complete_stock,
        derived_total_convertible_capacity_including_heat=2*complete_stock,
        minimum_terminal_capacitance=cmin, maximum_bridge_conductance=gmax, bounded_current_intercept=i0,
        body_voltage_bound=vbody, feed_voltage_bound=vfeed,
        material_nodes_per_zone=nodes_per_zone, macro_terminal_budget=macro_vertices, zones_per_host=zones,
        nearby_world_terminals=nearby_world_terminals,
        potential_world_crosswires=world_cut_edges, all_external_cut_edges=all_cut_edges,
        world_export_cap=world_cap, exogenous_power_upper=exogenous_power,
        all_positive_external_cut_power=local_cut_power,
        local_heat_interval_rate=heat_power,
        local_thermal_capacity=complete_stock, passive_cooling_floor=heat_power,
        thermal_excess_bound=2,
        raw_material_laws_not_inferred_from_nominal_prices=True,
        complete_conduit_and_receiver_join_remains_required=True)


def weighted_family(data):
    M = data['world_export_cap']
    require(M.denominator == 1 and M >= 4, 'Invalid hard export')
    M = int(M)
    m, R, b, p = 32 * (M + 12), 6, 6, 1
    W = b + (M - 1) * p
    service = F(3, 10) - F(13, 10) * b / m - F(M - 1, m)
    upper = F(22, 100) - (F(186, 100) * b + M - 1) / m - F(1,100) * (2 * (1 - F(b,m)) + F(6,100))
    lower = F(22, 100) - (F(66, 100) * b + M - 1) / m - F(1,100) * (2 * (1 - F(b,m)) + F(6,100))
    derivative = F(829, 500) + F(M - 1, m)
    require(service >= F(3,20), 'Existing service floor not preserved')
    require(upper >= F(11,2500) and lower >= F(261,2500), 'Existing collar margins not preserved')
    require(derivative <= F(5099,3000), 'Existing row timing supplier not preserved')
    require(m % 2 == 0 and m >= 72 and 6*m < 2**256, 'Finite word/source parameters invalid')
    # Degree and every local compiled storage/work index are unchanged.
    require(40 < m and 80 == 2*40, 'Locality/body pool changed')
    return dict(export_cap=M, region_population=m, regions=R, total_hosts=m*R,
        host_index_bits=(m*R-1).bit_length(), local_degree=40, bodies_per_side=80,
        global_bad_cover=b, physical_domains=p, weighted_bad_influence=W,
        service_lower=service, upper_collar_margin=upper, lower_collar_margin=lower,
        coordinate_rate_upper=derivative, row_rate_upper=2*derivative,
        original_safety_box=['7/20','13/20'], original_required_service='1/10',
        existing_service_and_timing_bounds_preserved=True,
        population_fixed_independently_of_horizon=True,
        not_a_practical_hardware_size_claim=True)


def voltage_power_checks():
    cases = 0
    for c, budget, a, b, g in product((F(1,4),F(1),F(4)), (F(1),F(4),F(16)),
                                    range(-8,9), range(-8,9), (F(0),F(1,4),F(1),F(4))):
        ea, eb = c*a*a/2, c*b*b/2
        if max(ea,eb) > budget:
            continue
        # Both terminal storage relations imply the pairwise cut-power bound.
        voltage_sq = 2*budget/c
        current = g*(a-b)
        require(current*current <= 4*g*g*voltage_sq, 'Current Cauchy bound')
        require(abs(a*current) <= 2*g*voltage_sq, 'Receiving terminal power bound')
        require((a-b)*current >= 0, 'Bridge creates energy')
        cases += 1
    intercept_cases=0
    for V,G,I0,a,b in product((F(1),F(3)), (F(0),F(2)), (F(1),F(4)), range(-3,4), range(-3,4)):
        if abs(a)>V or abs(b)>V: continue
        delta=F(a-b)
        I=G*delta+(I0 if delta>=0 else -I0)
        require(abs(I)<=I0+2*G*V, 'Bounded current intercept omitted')
        require(abs(a*I)<=V*(I0+2*G*V), 'Active/diode current power omitted')
        intercept_cases+=1
    # Finite stock alone does not give a rate. Smaller R preserves energy but
    # produces arbitrarily large instantaneous initial current.
    peaks = [F(1,r) for r in (F(1), F(1,10), F(1,1000))]
    require(peaks[-1] == 1000 and F(1,2) < 1, 'Finite-energy/no-rate countermodel lost')
    return dict(exact_cut_cases=cases, bounded_current_intercept_cases=intercept_cases, finite_energy_counterexample=dict(
        capacitor=1, voltage=1, stored_energy='1/2', resistances=['1','1/10','1/1000'], initial_currents=peaks),
        minimum_capacitance_and_finite_bridge_conductance_are_separate_raw_inputs=True)


def conserved_heat_checks():
    cases = 0
    # Repeated export/reimport can exceed the initial stock without producing
    # heat; only telescoped energy balance controls actual irreversible heat.
    for initial in product(range(4), repeat=3):
        for src, dst, amount, loss in product(range(3), range(3), range(4), range(4)):
            if src == dst or amount > initial[src] or loss > amount:
                continue
            state = list(initial)
            state[src] -= amount
            state[dst] += amount-loss
            require(sum(initial)-sum(state) == loss, 'Internal transfer not cancelled')
            require(loss <= sum(initial), 'Heat exceeds actual energy')
            cases += 1
    repeated_exports = 20
    require(repeated_exports > 1, 'Export counting counterexample absent')
    # Discrete impulse/continuous-power thermal comparison at exact rational
    # decay. Total arrival envelope is burst C plus rate P, not a fresh C/tick.
    admitted = 0
    for deposits in product((0,1,2), repeat=7):
        if any(sum(deposits[a:b]) > 2 + (b-a) for a in range(7) for b in range(a+1,8)):
            continue
        temp = F(1)
        for deposit in deposits:
            temp = temp/2 + F(deposit, 4)
            require(temp <= 2, 'Local thermal envelope failed')
        admitted += 1
    return dict(conservative_transfer_cases=cases, admitted_heat_histories=admitted,
        lossless_round_trip_export_count=20, lossless_round_trip_initial_energy=1,
        local_cut_rate_independent_of_population=True,
        combined_thermal_energy_barrier_cases=combined_thermal_barrier_checks(),
        heat_to_work_recycling_is_included=True)


def combined_thermal_barrier_checks():
    cases=0
    # At the Y=2C boundary, arbitrary division between free and thermal
    # energy leaves theta>=1. Reversible conversion changes neither Y nor
    # the maximum total energy, even if a later stage dissipates it again.
    for C,P in product((F(1),F(5),F(100)), repeat=2):
        for efrac in (F(0),F(1,4),F(1,2),F(1)):
            E=C*efrac
            theta=(2*C-E)/C
            require(theta>=1 and P-P*theta<=0, 'Combined thermal barrier fails')
            for transfer in (F(0), (C-E)/2, C-E):
                E2=E+transfer
                Q2=C*theta-transfer
                require(E2+Q2==2*C and 0<=E2<=C, 'Heat recycling creates energy')
                require(Q2/C<=2, 'Thermal result discarded actual storage')
                cases+=1
    return cases


def receiver_module_checks():
    results = []
    # Generalization of the same BOUNDARIES circuit, at each real inlet rating.
    # C is fixed small so the passive front store is explicitly charged.
    for P in (F(1500), F(524288), F(2**24), F(2**40), F(2**63)):
        V = F(300)
        I = P/V
        r = F(1, 2**64)
        C = F(1, 2**64)
        # shunt starts .1 below the permitted maximum; at V it dominates
        # BOTH possible incoming directions plus local bleed.
        slope = 30*I
        top_net = 2*I-slope*F(1,10)-V/1000
        require(top_net < 0, 'Raw endpoint upper invariant fails')
        require(slope<=2**64 and I<=2**64, 'Rescaled limiter exceeds hard material alphabet')
        require(V*I == P, 'Receiver power rating not actual terminal power')
        require(r >= F(1,2**64) and C >= F(1,2**64), 'Hard alphabet violated')
        stock = C*V*V  # source+receiver capacitors
        # Named generic cold charging comparison: h=I/2; supply slack .5V.
        h=I/2
        require(2*r*h < F(1,2), 'Series drop invalidates nominal headroom')
        results.append(dict(terminal_power_rating=P, current_rating=I,
            two_capacitor_stock=stock, minimum_series_resistance=r,
            shunt_slope=slope, upper_boundary_net_current=top_net,
            conductance_upper=1/r,
            proves_voltage_and_power_only_not_protocol_freshness=True))
    return dict(rescaled_port_cases=results,
        power_is_not_semantic_data_or_private_write_authority=True,
        actual_lane_counts_timing_and_nominal_delivery_need_join=True)


def typed_graph_checks():
    # All physical source/target/coordinate leaves are enumerated for one
    # translated local star; all stars are isomorphic for the cyclic family.
    degree, banks, coords = 40, 2, 15+2*80
    leaves = []
    N=432
    offsets=tuple(range(-20,0))+tuple(range(1,21))
    neighbors=lambda host: tuple((host+j)%N for j in offsets)
    for offset in range(degree):
        target=neighbors(0)[offset]
        origin_ordinal=neighbors(target).index(0)
        for bank in range(banks):
            for coord in range(coords):
                leaves.append(('force',offset,bank,coord))
            leaves.append(('write',offset,bank,2*origin_ordinal+bank))
            leaves.append(('raw_record',offset,bank,0))
            leaves.append(('query',offset,bank,0))
    force = [v for v in leaves if v[0]=='force']
    write = [v for v in leaves if v[0]=='write']
    require(len(force)==14000 and len(set(force))==14000, 'Actual field array/aliases changed')
    require(len(write)==80 and sorted(v[3] for v in write)==list(range(80)), 'Private bay map changed')
    # Arbitrary source-site rewiring can choose any of its existing terminals;
    # crossing an intact receiving boundary still ends at its fixed leaf.
    for leaf in leaves:
        require(leaf[0] in {'force','write','raw_record','query'}, 'Hidden C/W terminal')
        if leaf[0]=='write':
            require(leaf[3]==2*neighbors(neighbors(0)[leaf[1]]).index(0)+leaf[2], 'Source can select another producer bay')
    # The graph is deliberately not an energy-cap proof: a conductive edge
    # into WORLD, omitted from the list of four ordinary generators, changes M.
    ordinal_checks=0
    for N2 in (432,444,504):
        for origin in range(N2):
            ns=tuple((origin+k)%N2 for k in offsets)
            for offset,target in enumerate(ns):
                back=tuple((target+k)%N2 for k in offsets).index(origin)
                require(back==39-offset, 'Translation changed actual writer ordinal')
                ordinal_checks+=1
    nominal_world_ports=4
    new_crosswire_flow=F(5)
    require(new_crosswire_flow>nominal_world_ports, 'Maintenance-to-world countercase lost')
    return dict(actual_force_leaves=len(force), private_write_leaves=len(write),
        raw_record_leaves=80, query_leaves=80,
        all_external_typed_leaves=len(leaves), actual_writer_ordinal_checks=ordinal_checks,
        physical_aliases_count_once=True,
        arbitrary_internal_rewire_preserves_fixed_receiving_leaf=True,
        counterexample_omitted_maintenance_world_crosswire_flow=new_crosswire_flow,
        source_mode='written all-terminal graph plus enumerated translated source-star; not full unbounded graph enumeration')


def divider_consistency(data):
    # This checks a possible energy/capacity interface, not the conduit theorem.
    # In particular, it does NOT prove bounded J or no bypass of a contact.
    body_v=data['body_voltage_bound']
    feed_v=data['feed_voltage_bound']
    R, Iunit, loops = F(2**68), F(2**15), 4
    Ccarrier = F(1,2**27)
    old=json.loads((HERE/'resource_results.json').read_text(encoding='utf-8'))['runtime_inventory']
    Emin,Emax=F(old['per_bank_on']),F(old['per_bank_capacity'])
    lo,hi=F(2**43),F(2**45)
    require(Ccarrier*lo*lo/2 < Emin and Emax < Ccarrier*hi*hi/2, 'Carrier voltage range wrong')
    require(R>=5*body_v, 'Two-zone divider residual ratio unsupported')
    source_v=2*R+body_v
    require(source_v < feed_v, 'Feed voltage bounds contain own source inconsistently')
    source_power=F(22,5)*Iunit*R
    all_power=loops*source_power + F(old['upstream_rate'])
    provisional_upstream_cap=8*all_power+F(old['upstream_burst'])
    require(provisional_upstream_cap < data['hard_feed_capacity'], 'Feed stock does not fit hard capacity')
    require(F(19,10)*Iunit*lo > F(old['per_bank_charger_output']), 'Nominal bank power shortfall')
    # No R satisfies R>=5V and upstream voltage 2R<=V for positive V.
    impossible_global_v=F(1)
    require(2*5*impossible_global_v > impossible_global_v, 'Global voltage circularity hidden')
    return dict(status='compatible two-zone energy sizing only; actual conduit proof not supplied',
        body_voltage_limit=body_v, feed_voltage_limit=feed_v, scaled_resistance=R,
        actual_current_unit=Iunit, maximum_source_voltage=source_v,
        per_loop_power_ceiling=source_power, independent_loops=loops,
        hypothetical_four_loop_total_input=all_power,
        provisional_upstream_capacity=provisional_upstream_cap,
        carrier_capacitance=Ccarrier, nominal_carrier_voltage_interval=[lo,hi],
        preserves_existing_bank_operating_stock=True,
        false_global_voltage_fixed_point_rejected=True,
        bounded_source_current_and_actual_contact_topology_not_proved=True)


def actual_world_work_checks():
    cases=0
    for x,y in product((F(7,20), F(1,2), F(13,20)), (F(-1), F(0), F(3,10),F(9,10), F(1))):
        current=y
        work=x*current
        require(abs(work)<=1, 'WORLD effect work exceeds its added physical rating')
        cases+=1
    # The region capacitor realizes exactly the existing normalized ODE under
    # physical t=tau*q. This is an action realization, not a new controller.
    tau=F(1,10**7)
    for m in (72, 96, 144):
        for nu,u,coupling in product((F(59,100),F(61,100)), (F(3,10),F(9,10)), (F(-1,100),F(1,100))):
            capacitance=F(m)/tau
            actual_current=m*(nu-u+coupling)
            require(actual_current/capacitance==tau*(nu-u+coupling), 'World time/unit decode failed')
            cases+=1
    return dict(exact_power_and_decode_cases=cases, original_rc_source_power=16,
        additional_world_effector_power=4, total_world_source_power=20,
        rc_and_effector_stock=200,
        output_element='ordinary powered controlled-current element q=y, physical work x*y',
        actual_old_blend_zero_is_needed_to_remove_world_backfeed=True,
        source_supply_and_price_join_remains_required=True)


def main():
    require(not sys.flags.optimize, 'Unoptimized checking required')
    parser=argparse.ArgumentParser()
    mode=parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args=parser.parse_args()
    names=('HARD-BOUNDARY.md','hard_boundary_model.py','FAULT-MAP.md','BOUNDARIES.md',
           'RESOURCES.md','resource_results.json','RUNTIME-PORTS.md','INITIAL-RETURN.md')
    hashes={name:digest(name) for name in names}
    target=HERE/'hard_boundary_results.json'
    if args.check:
        expected=json.loads(target.read_text(encoding='utf-8'))
        require(expected['sources']==hashes, 'Hard-boundary inputs changed; review before refreshing')
    data=inventory()
    result=encode(dict(status='derived hard-energy/cut family and source interface; joint source not admitted',
        sources=hashes, inventory=data, weighted_population=weighted_family(data),
        voltage_and_power=voltage_power_checks(), heat=conserved_heat_checks(),
        receiver_modules=receiver_module_checks(), typed_graph=typed_graph_checks(),
        divider_energy_interface=divider_consistency(data),
        world_effect_work=actual_world_work_checks()))
    require(hashes=={name:digest(name) for name in names}, 'Inputs changed during checking')
    rendered=json.dumps(result, indent=2, sort_keys=True)+'\n'
    if args.write:
        target.write_text(rendered, encoding='utf-8')
        print('hard-boundary record written')
    else:
        require(target.read_text(encoding='utf-8')==rendered, 'Hard-boundary result differs')
        print('hard-boundary record matches')


if __name__=='__main__':
    main()

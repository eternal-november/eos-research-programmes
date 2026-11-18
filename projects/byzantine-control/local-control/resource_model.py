"""Exact resource checks; interval proofs and source bindings are in RESOURCES.md.

No controller succeeds by being named good. The enumerations concern actual
chronological stock, all-symbol work, reservations and deposited energy.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def chronological_stock(demand, supply, capacity, clip_first):
    stock = capacity
    trace = [stock]
    for debit, offered in zip(demand, supply):
        if clip_first:
            available = min(capacity, stock + offered)
            if debit > available:
                return False, trace
            stock = available - debit
        else:
            if debit > stock + offered:
                return False, trace
            stock = min(capacity, stock + offered - debit)
        trace.append(stock)
    return True, trace


def interval_requirement(demand, supply, clip_first):
    # Independent expansion; no stock recurrence is used here.
    return max([0] + [sum(demand[a:b]) - sum(supply[a + int(clip_first):b])
                     for a in range(len(demand)) for b in range(a + 1, len(demand) + 1)])


def storage_checks():
    checked = 0
    for length in range(1, 6):
        for demand in product((0, 1, 3), repeat=length):
            for supply in product((0, 2), repeat=length):
                for clip_first in (False, True):
                    needed = interval_requirement(demand, supply, clip_first)
                    for capacity in sorted({0, max(0, needed - 1), needed, needed + 1}):
                        actual, _ = chronological_stock(demand, supply, capacity, clip_first)
                        require(actual == (capacity >= needed), "Chronological/interval disagreement")
                        checked += 1
    demand = [3] * 18
    supply = [0, 0, 9] * 6
    require(chronological_stock(demand, supply, 6, False)[0], "Direct-use witness failed")
    require(not chronological_stock(demand, supply, 6, True)[0], "Charging-order counterexample lost")
    require(chronological_stock(demand, supply, 9, True)[0], "Corrected clip-first capacity failed")
    return dict(exact_history_capacity_comparisons=checked,
                charging_order=dict(direct_capacity=6, clip_first_capacity=9,
                                    direct_trace=chronological_stock(demand, supply, 6, False)[1],
                                    wrong_clip_trace=chronological_stock(demand, supply, 6, True)[1]))


def reservation_checks():
    # One physical reservoir. Reserving is not removal from that reservoir.
    capacity, total, reserved, offered = 10, 10, 8, 8
    free = total - reserved
    false_free = min(capacity, free + offered)
    total_after = min(capacity, total + offered)
    actual_free = total_after - reserved
    require((false_free, actual_free) == (10, 2), "Shared-reserve overflow witness disappeared")
    require(false_free >= 5 > actual_free, "False certificate no longer changes a launch")
    # Physical transfer, rather than an accounting declaration, funds the tail.
    upstream, tail, bank_power = 12, 0, True
    price = 5
    require(upstream >= price, "No launch funding")
    upstream -= price
    tail += price
    bank_power = False
    performed = False
    if tail >= price:
        tail -= price
        performed = True
    require(performed and not bank_power and upstream == 7 and tail == 0,
            "Power loss cancelled or duplicated funded work")
    require(tail < price, "A second launch spent the same reserve")
    # A globally adequate total cannot fund a disconnected local consumer.
    stores = [10, 0]
    require(sum(stores) >= 5 and stores[1] < 5, "Local-delivery counterexample lost")
    return dict(overflow=dict(physical_total=total_after, reserved=reserved,
                              claimed_free=false_free, actual_free=actual_free),
                isolated_tail=dict(upstream_after=upstream, completed_after_power_off=performed,
                                   tail_after=tail, second_launch_funded=False),
                disconnected_stores=stores)


def recurrent_supply_checks():
    period = [0, 0, 5, 5, 5, 5]
    supply = period * 20
    demand = [3] * len(supply)
    count = 0
    for a in range(len(supply)):
        for b in range(a + 1, len(supply) + 1):
            require(sum(supply[a:b]) >= 3 * max(0, b - a - 2), "Supply lacks claimed interval envelope")
            count += 1
    ok, trace = chronological_stock(demand, supply, 12, False)
    require(ok, "Recurring deficits exhausted provisioned reserve")
    for start in range(0, len(supply), len(period)):
        require(trace[start] == 12 and trace[start + 2] == 6 and trace[start + 5] == 12,
                "No actual recurrent decline/recharge")
    # Average supply is not a bounded-outage certificate.
    bad_supply = [0] * 5 + [10] * 5
    require(sum(bad_supply) > 3 * len(bad_supply), "Countercase has insufficient average")
    require(not chronological_stock([3] * 10, bad_supply, 12, False)[0],
            "Average-only countercase unexpectedly survived")
    return dict(period=period, demand_per_quantum=3, capacity=12,
                cycles=20, interval_checks=count, one_cycle=trace[:7],
                average_supply_without_latency_bound_fails=True)


def branch_checks():
    # Continuous charge between instantaneous debits. The all-interval burst
    # law includes both endpoints, so one instantaneous debit is at most3.
    burst, rate, charge = 3, 2, 4
    on, off, capacity = F(16), F(32, 3), F(30)
    admitted = 0
    lowest = on
    for debits in product(range(4), repeat=7):
        if any(sum(debits[a:b+1]) > burst + rate*(b-a)
               for a in range(7) for b in range(a, 7)):
            continue
        energy = on
        for index, debit in enumerate(debits):
            if index:
                energy = min(capacity, energy + charge)
            energy -= debit
            require(energy >= on-burst > off, "Connected bank lost its operating margin")
            lowest = min(lowest, energy)
        admitted += 1
    # One local branch does not inherit half of a host-wide envelope.
    host_burst, branch_a, branch_b = 8, 8, 0
    require(branch_a + branch_b <= host_burst and branch_a > host_burst/2,
            "Per-bank concentration counterexample lost")
    # If a bleed is left connected, it must enter the charge headroom.
    source_charge, intended_load, hidden_bleed = F(4), F(2), F(3)
    require(source_charge-intended_load > 0 and source_charge-intended_load-hidden_bleed < 0,
            "Always-on discharge counterexample lost")
    return dict(continuous_charge_with_event_debit_histories=admitted,
                minimum_energy=lowest, operating_cutoff=off,
                host_envelope_is_not_branch_envelope=True,
                uncharged_connected_bleed_reverses_headroom=True)


def finite_inventory(degree=40, bays=80, image_cells=8192, private_words=32768):
    """Conservative finite source-price witness; not a frozen PROGRAM bill.

    Unit energy is the declared price of one native operation. Other positive
    prices below define a comparison instance, not empirical CPU specifications.
    Per-cartridge duplicated records and all generator fields are overcounts.
    """
    processors = 2 * bays
    state_heads = 38 + 8 * bays
    fast_keys = 3 + degree * (state_heads + 4)
    records_per_processor = 2 * degree * (fast_keys + degree)
    lanes = processors * 2 * degree
    mu_max = F(1 << 27)  # raw launch ceiling, distinct from nominal1.01*2^26
    # Includes wide execution plus one maximal bounded launch/decoder action.
    wide_price = 16384 + 4096
    records = processors * records_per_processor
    # row = name, count, event price, event burst, event rate
    bank_rows = [
        ("processor and bounded I/O launch", bays, F(wide_price), F(1), mu_max),
        ("every incoming data/control/reset symbol", bays * 2 * degree, F(8), F(264), F(1040)),
        ("receipt/timer transition", bays * records_per_processor, F(1), F(2), F(101, 100)),
        # Every neighbor's BOTH banks may direct all their processor attempts
        # at this one bank. Do not divide that host-origin envelope by two.
        ("target-side passive operation", processors * degree, F(4096), F(1), mu_max),
    ]
    rows = [(name, 2*n, cost, sigma, rho) for name, n, cost, sigma, rho in bank_rows]
    burst = sum(n * cost * sigma for _, n, cost, sigma, _ in rows)
    event_rate = sum(n * cost * rate for _, n, cost, _, rate in rows)
    field_count = 64 + 8 * bays
    generator_power = processors * degree * field_count * 12
    # Finite conservative code/private/record inventory. This does not certify
    # a complete actual W layout; binding that layout is a separate check.
    record_bits = 2048
    data_branch_bits = 128 * 384 + 512 * 128 + 384 + 512 + 128
    request_receiver_bits = 2 * degree * degree * 1024
    request_sender_bits = 26 * degree * 512
    source_scratch_bits = 4096
    # Both directions, padded per-cartridge inventories, every held field and
    # a separate metadata/source-I allowance. Counter semantic widths are not
    # increased by this physical padding.
    memory_bits = (processors * (192 * image_cells + 256 * (private_words + 64 + degree * field_count)
                                + record_bits * records_per_processor + request_receiver_bits
                                + request_sender_bits + source_scratch_bits)
                   + 2 * lanes * data_branch_bits)
    passive_power = F(memory_bits, 1024)
    continuous = generator_power + passive_power
    functional_rate = event_rate + continuous
    # Do not identify downstream consumption with upstream charging demand.
    # Two units of output per functional-rate unit, efficiency >=1/2, and
    # separately provisioned external work give gross upstream rate5*d0.
    rate = 5 * functional_rate
    margin = burst + rate
    capacity = burst + 2 * rate + margin
    # Real finite one-shot slots: one instruction tail per processor plus one
    # target operation per dedicated branch; their worst prices are prepaid.
    tail_capacity = processors * wide_price + processors * degree * 4096
    bank_branches = 2
    local_burst = burst / bank_branches
    local_rate = functional_rate / bank_branches
    on_threshold = 4 * (local_burst + 1)
    off_threshold = 2 * on_threshold / 3
    local_capacity_each = on_threshold + 2 * functional_rate
    local_bank_capacity = bank_branches * local_capacity_each
    charge_to_on = (on_threshold + local_burst) / local_rate
    require(on_threshold - local_burst > off_threshold, "Burst rearms low-energy cutoff")
    halvings = 0
    threshold = off_threshold
    while threshold < local_capacity_each:
        threshold *= 2
        halvings += 1
    discharge_coefficient = F(1, 10)
    backfeed = discharge_coefficient * off_threshold / 2
    drain_bound = 2 * halvings / discharge_coefficient
    energy_head_unit = F(1)
    while local_capacity_each / energy_head_unit > (1 << 20):
        energy_head_unit *= 2
    require(local_capacity_each / energy_head_unit <= 1 << 20, "Energy word range overflow")
    # Separate from operating/tail stores: every installed transducer may have
    # passive kinetic, magnetic or electrical storage. Eight is an explicit
    # illustrative rating, requiring source binding; positions alone do not
    # prove this bound or discharge their retained effects.
    transducer_count = processors * degree * field_count
    stored_energy_per_transducer = F(8)
    other_stored_capacity = transducer_count * stored_energy_per_transducer
    energy_cap = capacity + tail_capacity + local_bank_capacity + other_stored_capacity
    # Include finite independent external/backfeed mechanical input as well as
    # upstream offered power. This is a declared source envelope, not zero heat.
    offered_supply_power_cap = 2 * rate
    other_input_power_cap = generator_power + 2 * backfeed
    incoming_power = offered_supply_power_cap + other_input_power_cap
    thermal_capacity, cooling = energy_cap, incoming_power
    initial_thermal_excess_upper = F(1)
    theta_bound = max(initial_thermal_excess_upper, incoming_power/cooling) + energy_cap/thermal_capacity
    thermal_coupling, mechanical_side_effect = F(1, 200), F(1, 200)
    plant_side_effect = thermal_coupling * theta_bound + mechanical_side_effect
    require(plant_side_effect == F(3, 200) < F(1, 50), "Thermal/plant margin failed")
    require(capacity - (burst + 2 * rate) == margin > 0, "Stock margin inconsistent")
    return dict(design=dict(degree=degree, bays=bays, image_cells=image_cells, private_words=private_words),
                scope="finite conservative inventory witness, awaiting actual PROGRAM/port binding",
                processors=processors, state_heads=state_heads, fast_keys=fast_keys,
                raw_processor_launch_ceiling=mu_max,
                records=records, raw_symbol_lanes=lanes, memory_bits=memory_bits,
                physical_bits_per_record=record_bits, physical_bits_per_data_branch=data_branch_bits,
                per_processor_padded_request_receiver_bits=request_receiver_bits,
                per_processor_padded_request_sender_bits=request_sender_bits,
                per_processor_source_scratch_bits=source_scratch_bits,
                event_classes=[dict(name=name, count=n, price=c, burst=s, rate=r)
                               for name, n, c, s, r in rows],
                per_bank_event_classes=[dict(name=name, count=n, price=c, burst=s, rate=r)
                                        for name, n, c, s, r in bank_rows],
                continuous_power=continuous, burst=burst, functional_rate=functional_rate,
                upstream_rate=rate, charger_efficiency_lower=F(1, 2),
                total_charger_output=2 * functional_rate,
                total_charger_input_upper=4 * functional_rate,
                local_branch_burst=local_burst, local_branch_rate=local_rate,
                bank_branches=bank_branches,
                on_threshold=on_threshold, off_threshold=off_threshold,
                charge_to_on_bound=charge_to_on, local_capacity_each=local_capacity_each,
                discharge_coefficient=discharge_coefficient, residual_backfeed_bound=backfeed,
                halving_intervals=halvings, post_cut_no_launch_bound=drain_bound,
                energy_head_unit=energy_head_unit, energy_head_range=local_capacity_each/energy_head_unit,
                outage_latency=2, reserve_margin=margin, capacity=capacity,
                tail_capacity=tail_capacity, local_bank_capacity=local_bank_capacity,
                transducer_count=transducer_count,
                stored_energy_per_transducer=stored_energy_per_transducer,
                other_stored_capacity=other_stored_capacity,
                total_stored_capacity=energy_cap, incoming_power=incoming_power,
                offered_supply_power_cap=offered_supply_power_cap,
                other_input_power_cap=other_input_power_cap,
                initial_thermal_excess_upper=initial_thermal_excess_upper,
                thermal_capacity=thermal_capacity, cooling=cooling,
                thermal_bound=theta_bound, plant_side_effect=plant_side_effect)




def world_resource_checks():
    """Resource rederivation of RC tracking plus actual controlled-current work.

    The controller/source bridge is INITIAL-RETURN's separate proof. Optional
    parent source hashes below make its later arrival a record change.
    """
    checks=0
    c=F(100)
    for r,command,state in product((F(1,2),F(1)),(-F(1),F(0),F(1)),(-F(1),F(0),F(1))):
        current=(command-state)/r
        source=command*current
        heat=r*current*current
        energy_rate=state*current
        require(energy_rate==source-heat,'WORLD RC energy balance mismatch')
        require(c*state*state/2<=50 and source<=4 and heat<=8,'WORLD RC resource envelope failed')
        checks+=1
    parent_files=tuple(name for name in ('INITIAL-RETURN.md','initial_return_model.py','initial_return_results.json') if (HERE/name).exists())
    if (HERE/'initial_return_results.json').exists():
        actual=json.loads((HERE/'initial_return_results.json').read_text(encoding='utf-8-sig'))['world']['rc']
        require(actual['host_world_trackers']==4 and actual['capacitance']==100,
                'Actual WORLD tracker count/capacitance changed')
        require([F(v) for v in actual['resistance']]==[F(1,2),F(1)],
                'Actual WORLD resistance interval changed')
        require((actual['additional_host_storage'],actual['additional_source_power'],actual['instantaneous_resistor_heat_upper'])==(200,16,32),
                'Actual WORLD physical budget changed')
    import hard_boundary_model as hard
    effect = hard.actual_world_work_checks()
    require(effect['additional_world_effector_power'] == 4 and effect['total_world_source_power'] == 20,
            'Actual controlled-current WORLD interface changed')
    return dict(scope='four RC trackers plus their actual controlled-current outputs on the protected plant prefix',
        source_interface_snapshot='6d23357',channels=4,capacitance=c,resistance_interval=[F(1,2),F(1)],
        state_and_command_interval=[-F(1),F(1)],host_storage=F(200),
        host_tracker_source_power=F(16),host_effector_source_power=F(4),
        host_source_power=F(20),host_peak_heat=F(32),exact_power_cases=checks,
        effector_work=effect,
        parent_source_files_bound=list(parent_files),
        controller_world_bridge_not_proved_by_this_resource_check=True)


def shared_foreign_heat_family(bound, hosts):
    """Conserved-network thermal supplier with explicit hard-source inputs.

    Choosing these ratings defines a mathematical source class. Their truth
    for a physically damaged body is not inferred from nominal field records.
    """
    require(hosts>=1,'Empty physical source')
    hard_stock=bound['total_stored_capacity']
    hard_external=bound['incoming_power_upper']
    total_stock=hosts*hard_stock
    total_external=hosts*hard_external
    h,k=total_stock,total_external
    excess=max(F(1),total_external/k)+total_stock/h
    require(excess==2,'Shared conservation/thermal comparison changed')
    require(F(1,200)*excess+F(1,200)<F(1,50),'Shared thermal/plant allowance fails')
    # A foreign source can add heat at a good node without causing another
    # intrusion there. Only the common energy account licenses this budget.
    stored=[F(10)]*hosts
    total_before=sum(stored)
    transfers=[]
    if hosts>1:
        delivered=min(F(5),stored[0])
        stored[0]-=delivered
        heat_at_one=delivered
        require(sum(stored)+heat_at_one==total_before,'Foreign heat created energy')
        transfers=[dict(source=0,receiver=1,heat=heat_at_one)]
    return dict(hosts=hosts,scope='conditional whole-network heat rating; raw fault-body inputs require source admission',
        hard_convertible_stock_cap_per_fixture=hard_stock,
        hard_external_supply_and_environment_power_per_fixture=hard_external,
        all_convertible_stock=total_stock,all_external_power=total_external,
        thermal_capacity_per_fixture=h,passive_cooling_floor_per_fixture=k,
        initial_thermal_excess_upper=F(1),thermal_excess_bound=excess,
        plant_effect_upper=F(3,200),conserved_foreign_transfer=transfers,
        no_new_fault_label_for_heat_receiver=True,
        raw_hard_cap_is_independent_source_parameter=True,
        nominal_field_price_does_not_prove_faulty_export_cap=True)

def runtime_inventory():
    """Bind actual runtime arrays and transfers, keeping raw ratings explicit.

    Finite storage does not imply a power bound. Background-clock price/rate,
    passive dissipation, generator storage and coupling below are declared
    source ratings. Their all-history physical realization remains an input.
    """
    import port_model as ports
    import program_model as program
    import boundary_model as boundary

    field = boundary.parameter_checks()
    field_record = json.loads((HERE/'boundary_results.json').read_text(encoding='utf-8'))
    for name, value in field_record['sources'].items():
        require(boundary.digest(name) == value, 'Stale field-boundary evidence: '+name)
    require(boundary.normalize(field) == field_record['parameters'], 'Field-boundary point differs')
    world = world_resource_checks()
    bound = ports.bounds()
    port_record = json.loads((HERE/'port_results.json').read_text(encoding='utf-8'))
    program_record = json.loads((HERE/'program_results.json').read_text(encoding='utf-8'))
    for record in (port_record, program_record):
        for name, value in record['sources'].items():
            require(ports.digest(HERE/name) == value, 'Stale upstream evidence: '+name)
    require(ports.normalize(bound) == port_record['bounds'], 'Port inventory differs from frozen record')
    d, b, cells = bound['design']['d'], bound['design']['B'], bound['design']['L']
    n = 2*b
    shape = program.Design(degree=d, bays=b, origins=13, image_cells=cells,
                           fast_batch=16, query_batch=4, maintenance_batch=4,
                           connectors_a=11, connectors_b=11)
    compiled = program.Compiler(shape).compile()
    private_words = compiled.next_register+compiled.constants['DATA_WORDS']+32
    require(private_words == program_record['full_layout_bounds']['private_words_with_metadata'],
            'Actual full-program private layout changed')
    require(len(compiled.nodes) == program_record['full_layout_bounds']['code_cells'],
            'Actual code layout changed')
    padded_private_words = 32768
    require(private_words <= padded_private_words, 'Private memory allocation is too small')
    keys = compiled.constants['FAST_KEYS']
    # INCIDENCE's selected sparse layout, not its dense alternative.
    records_per_bank = 26*(keys+d)
    require((keys, records_per_bank) == (27283, 710398), 'Selected input layout changed')
    field_count = 64+8*b
    generator_count = n*d*field_count  # Preserved allocation units, not actual generator count.
    actual_pairs = field['installed_pairs']
    require(actual_pairs == 2*d*(15+2*b), 'Physical endpoint-pair count changed')
    actual_field_stock = actual_pairs*field['raw_field_storage_per_pair']+world['host_storage']
    actual_field_power = actual_pairs*field['healthy_source_power_per_pair']+world['host_source_power']
    memory = dict(code_and_private=n*(192*cells+256*padded_private_words),
                  selected_input_records=2*records_per_bank*2048,
                  source_scratch=n*4096,
                  request_receivers=2*(2*d*d)*1024,
                  port_descriptors=bound['descriptor_bits'],
                  instruction_latches=n*2048,
                  command_mailboxes=bound['command_mailbox_bits'],
                  request_mailboxes=bound['request_mailbox_bits'],
                  data_and_propagation=bound['data_storage_with_propagation_bits'],
                  passive_target_endpoints=bound['passive_target_endpoint_bits'],
                  held_fields=2*d*field_count*256,
                  local_route_metadata=2*(records_per_bank+2*d*d+2*b*d)*128)
    require(all(value % 2 == 0 for value in memory.values()), 'Installed symmetric bank count is not even')
    memory_bits = sum(memory.values())
    autonomous_bits = memory_bits-memory['code_and_private']
    # A declared clocked-control circuit rating, not inferred from bit count.
    # It includes reset, expiry, rejection, arbitration and inactive-CPU work.
    background_rate = F(1 << 31)
    background_price_per_bit = F(1)
    raw_rates = [F(2048*101, 100), F(128*101, 100), F(64*101, 100),
                 F(1040), F(1)/ports.DELTA, F(ports.MU_HARD)]
    require(all(rate < background_rate for rate in raw_rates), 'Auxiliary rate exceeds chosen circuit rating')
    background_power = autonomous_bits*background_price_per_bit*background_rate
    leakage_power = F(memory_bits, 1024)
    generator_power = generator_count*12
    require(actual_field_power <= generator_power, 'Existing generator delivery budget is too small')
    # These independent target/receiver circuits are available from U even
    # while the ordinary bank supply is cut. Source capsules are not reused.
    external_bank_rows = [
        ('incoming raw symbols', 2*d, F(8), F(264), F(1040)),
        ('local passive endpoint work', 2*b*d, F(4096), F(1), F(ports.MU_HARD)),
    ]
    external_burst_bank = sum(count*price*sigma for _,count,price,sigma,_ in external_bank_rows)
    external_rate_bank = sum(count*price*rate for _,count,price,_,rate in external_bank_rows)
    # Never infer a bank demand envelope by splitting a concentrated host
    # offer count. Only physically duplicated arrays/chargers are halved.
    require(external_bank_rows[1][1] == bound['target_slots_per_kind_per_bank'],
            'One target bank lost neighboring processors')
    recharge_peak = bound['maximum_local_recharge_power']
    bank_recharge_peak = recharge_peak/2
    capsule_bank = F(bound['capsule_energy_capacity'], 2)
    bank_burst = capsule_bank
    bank_rate = bank_recharge_peak+F(generator_power, 2)+leakage_power/2
    # Charge every repeated dump/recharge at continuous installed peak. The
    # operation-count lower bill does not pay an idle charged slot reset.
    external_burst = 2*external_burst_bank
    external_rate = 2*external_rate_bank+background_power+leakage_power
    bank_charger_output = 2*bank_rate
    bank_charger_efficiency = F(1,2)
    total_charger_input = 2*bank_charger_output/bank_charger_efficiency
    upstream_rate = total_charger_input+external_rate
    upstream_burst = external_burst
    latency = F(2)
    margin = upstream_burst+upstream_rate
    upstream_capacity = upstream_burst+latency*upstream_rate+margin
    on = 4*(bank_burst+bank_rate+1)
    off = 2*on/3
    bank_capacity = on+4*bank_rate
    startup = (on+bank_burst)/bank_rate
    require(on-bank_burst > off, 'Operating threshold cannot pay the initial capsule burst')
    require(bank_charger_output > bank_rate, 'No positive local charging headroom')
    # Raw foreign power, in both selected target banks. Every actual portal
    # has a minimum pulse duration and a finite count; it is not priced from
    # the number of accepted records alone.
    target_pulse_power = 2*3*(2*b*d)*bound['per_endpoint_pulse_power']
    incoming_data_power = 2*(2*d)*(1 << 20)
    incoming_command_power = 2*(d+1)*128*bound['per_endpoint_pulse_power']
    incoming_request_power = 2*(2*d*d)*16*bound['per_endpoint_pulse_power']
    base_portal_power = target_pulse_power+incoming_data_power+incoming_command_power+incoming_request_power
    # Conservatively retain all protected field/WORLD return power before the
    # actual carrier cut; after that cut its isolated state cannot rearm U.
    ordinary_field_backfeed = actual_field_power
    portal_power = base_portal_power+ordinary_field_backfeed
    leakage_ratio = F(1)  # Admit the complete rated portal power as backfeed.
    rho = leakage_ratio*F(portal_power, 2)
    discharge_k = F(1,10)
    require(rho <= discharge_k*off/4, 'Actual aggregate portal leakage prevents robust half-cutoff drainage')
    halvings, threshold = 0, off
    while threshold < bank_capacity:
        halvings += 1
        threshold *= 2
    drain = 2*halvings/discharge_k
    robust_drain = 2*(halvings+1)/discharge_k
    energy_unit = F(1)
    while bank_capacity/energy_unit > 1 << 20:
        energy_unit *= 2
    require(bank_capacity/energy_unit <= 1 << 20, 'Finite energy sensor overflows')
    sensed_off_threshold = off//energy_unit-2
    require(off/(2*energy_unit)+1 <= sensed_off_threshold, 'No nonempty robust energy-head interval')
    require((sensed_off_threshold+1)*energy_unit < off, 'Energy-head rounding can certify above cutoff')
    # All capsule, field, reservoir and provisionally rated mechanical stock.
    transducer_store_rating = F(8)
    transducer_capacity = generator_count*transducer_store_rating
    require(actual_field_stock <= transducer_capacity, 'Existing physical storage allocation is too small')
    total_stored = (upstream_capacity+2*bank_capacity+
                    bound['isolated_energy_capacity']+transducer_capacity)
    supply_upper = 2*upstream_rate
    incoming_other = portal_power+generator_power
    incoming_power = supply_upper+incoming_other
    thermal_capacity, cooling_floor = total_stored, incoming_power
    theta = max(F(1), incoming_power/cooling_floor)+total_stored/thermal_capacity
    coupling, mechanical_effect = F(1,200), F(1,200)
    require(theta == 2 and coupling*theta+mechanical_effect < F(1,50), 'Coupled thermal margin failed')
    require(upstream_capacity-(upstream_burst+upstream_rate*latency) == margin,
            'Upstream storage envelope changed')
    command_rate = bound['autonomous_command_rate']
    request_rate = bound['autonomous_request_rate']
    autonomous_capsule_rate = ports.PORT_ENERGY*(command_rate+request_rate)
    require(autonomous_capsule_rate < recharge_peak, 'Sampler funding escaped peak-transfer bill')
    return dict(scope='runtime-bound conservative resource supplier; physical ratings and joint source remain conditional',
        design=dict(degree=d,bays=b,image_cells=cells), code_cells=len(compiled.nodes),
        actual_private_words=private_words, padded_private_words=padded_private_words,
        fast_keys=keys, selected_records_per_bank=records_per_bank,
        runtime_slots=bound['installed_slots'], runtime_port_capsules=bound['total_port_slots'],
        capsule_capacity=bound['capsule_energy_capacity'], data_field_capacity=bound['data_field_energy_capacity'],
        combined_capsule_field_capacity=bound['isolated_energy_capacity'], memory_categories=memory,
        memory_bits=memory_bits, autonomous_bits=autonomous_bits,
        background_clock_rate=background_rate, background_price_per_bit=background_price_per_bit,
        required_auxiliary_rate_checks=raw_rates, background_power=background_power,
        leakage_power=leakage_power, generator_allocation_units=generator_count,generator_power=generator_power,
        actual_signed_pairs=actual_pairs,actual_force_pair_stock=field['raw_field_storage_per_pair'],
        actual_force_pair_power=field['healthy_source_power_per_pair'],
        actual_world_resource_interface=world,actual_field_and_world_stock=actual_field_stock,
        actual_field_and_world_power=actual_field_power,
        unused_generator_power_headroom=generator_power-actual_field_power,
        unused_physical_storage_headroom=transducer_capacity-actual_field_stock,
        per_bank_external_rows=[dict(name=name,count=count,price=price,burst=sigma,rate=rate)
                                for name,count,price,sigma,rate in external_bank_rows],
        all_capsule_recharge_peak=recharge_peak, per_bank_recharge_peak=bank_recharge_peak,
        per_bank_burst=bank_burst,per_bank_rate=bank_rate,
        autonomous_command_rate=command_rate,autonomous_request_rate=request_rate,
        autonomous_capsule_rate=autonomous_capsule_rate,
        external_burst=external_burst,external_rate=external_rate,
        per_bank_charger_output=bank_charger_output,charger_efficiency_lower=bank_charger_efficiency,
        total_upstream_charger_input=total_charger_input,
        upstream_burst=upstream_burst,upstream_rate=upstream_rate,
        outage_latency=latency,reserve_margin=margin,upstream_capacity=upstream_capacity,
        per_bank_on=on,per_bank_off=off,per_bank_capacity=bank_capacity,
        per_bank_startup_bound=startup,portal_power=portal_power,
        base_raw_portal_power=base_portal_power,ordinary_field_backfeed_upper=ordinary_field_backfeed,
        target_pulse_power=target_pulse_power,incoming_data_power=incoming_data_power,
        incoming_command_power=incoming_command_power,incoming_request_power=incoming_request_power,
        backfeed_fraction=leakage_ratio,per_bank_residual_backfeed=rho,discharge_coefficient=discharge_k,
        post_cut_halvings=halvings,post_cut_no_launch_bound=drain,
        post_cut_half_off_bound=robust_drain,sensed_off_threshold=sensed_off_threshold,
        raw_energy_head_error_units=F(1),
        energy_head_unit=energy_unit,energy_head_range=bank_capacity/energy_unit,
        transducer_store_rating=transducer_store_rating,transducer_capacity=transducer_capacity,
        total_stored_capacity=total_stored,offered_supply_power_upper=supply_upper,
        other_incoming_power_upper=incoming_other,incoming_power_upper=incoming_power,
        initial_thermal_excess_upper=F(1),thermal_capacity=thermal_capacity,
        passive_cooling_floor=cooling_floor,thermal_excess_bound=theta,
        nonzero_thermal_coupling=coupling,mechanical_effect_upper=mechanical_effect,
        plant_side_effect_upper=coupling*theta+mechanical_effect,
        selected_standing_load=leakage_power,
        actual_outage_drawdown_lower=latency*leakage_power,
        physical_storage_allocation_covers_constructed_field_and_world=True,
        hard_damaged_body_storage_not_inferred_from_nominal_coil_caps=True,
        local_thermal_point_requires_its_original_actual_incoming_envelope=True,
        whole_source_conduct_and_return_not_established=True)


def reset_recharge_checks():
    """An idle-reset witness defeats accepted-operation-only energy bills."""
    from port_model import DELTA, PORT_ENERGY
    common, slot, dissipated = F(10*PORT_ENERGY), F(0), F(0)
    initial = common
    launches = 0
    for _ in range(10):
        common -= PORT_ENERGY
        slot += PORT_ENERGY
        dissipated += slot
        slot = F(0)
        require(common+slot+dissipated == initial, 'Idle reset created energy')
    require(launches == 0 and dissipated == initial, 'Repeated idle-charge witness lost')
    elapsed = 10*(DELTA+F(1,128))
    require(dissipated <= (PORT_ENERGY/DELTA)*elapsed, 'Physical precharge ceiling did not pay idle dumps')
    return dict(idle_resets=10,accepted_operations=launches,actual_debit=dissipated,
                elapsed=elapsed,precharge_power=PORT_ENERGY/DELTA,
                accepted_operation_only_bill_fails=True)



def runtime_supply_checks(bound):
    """Actual chronological witness with the same selected D and capacity."""
    rate, burst = bound['upstream_rate'], bound['upstream_burst']
    capacity = bound['upstream_capacity']
    supply = [F(0), F(0), 5*rate/3, 5*rate/3, 5*rate/3, 5*rate/3]*20
    demand = [rate]*len(supply)
    demand[0] += burst
    ok, trace = chronological_stock(demand, supply, capacity, False)
    require(ok and min(trace) >= bound['reserve_margin'], 'Runtime stock witness loses its reserve')
    for start in range(6, len(supply), 6):
        require(trace[start] == capacity and trace[start+2] == capacity-2*rate,
                'Runtime supply witness has no recurring actual drawdown/recharge')
    # Primary interval evidence at rational offsets; the written periodic
    # deficit argument establishes the infinite continuous-time statement.
    def delivered(t):
        cycles = t//6
        phase = t-6*cycles
        return F(20,3)*cycles+F(5,3)*max(F(0),phase-2)
    grid = [F(k,4) for k in range(73)]
    checks = 0
    for start in grid:
        for end in grid:
            if end < start:
                continue
            actual = delivered(end)-delivered(start)
            require(actual >= max(F(0),end-start-2), 'Continuous phase violates latency-rate supply')
            checks += 1
    standing = bound['selected_standing_load']
    poor_capacity = 2*standing-1
    require(not chronological_stock([standing,standing],[0,0],poor_capacity,False)[0],
            'Insufficient actual standing-load reserve survives outage')
    return dict(cycles=20,first_cycle_stock=trace[:7],minimum_stock=min(trace),
                recurrent_full_recharge=True,phase_interval_checks=checks,
                supply_period=6,outage_length=2,on_rate=5*rate/3,
                on_rate_below_upper=(5*rate/3 < bound['offered_supply_power_upper']),
                lower_envelope_rate=rate,lower_envelope_latency=2,
                selected_standing_load=standing,positive_outage_drawdown=2*standing,
                insufficient_actual_capacity=poor_capacity,
                witness_scope='raw source/stock witness; useful controller and common fault history remain to assemble')

def heat_checks():
    # Discrete linear comparison with explicit impulses: y_next=r*y+heat/h.
    # For all interval heat <= burst + rate*L, convolution is bounded by
    # max(y0,rate/(h*(1-r))) + burst/h. Enumerate independently of that formula.
    r, h, burst, rate = F(1, 2), F(2), F(3), F(1)
    bound = rate / (h * (1-r)) + burst/h
    accepted = 0
    for heat in product((0, 1, 3), repeat=7):
        if any(sum(heat[a:b]) > burst + rate*(b-a)
               for a in range(len(heat)) for b in range(a+1, len(heat)+1)):
            continue
        y = F(0)
        for deposit in heat:
            y = r*y + F(deposit, h)
            require(y <= bound, "Convolution envelope violated")
        accepted += 1
    # A single pulse violates a temperature constraint despite a low average.
    pulse = [10] + [0]*19
    require(F(sum(pulse), len(pulse)) < 1, "Pulse average is not small")
    require(F(pulse[0], h) > 2, "Pulse does not exceed the temperature limit")
    # With NO passive removal and an uncontrollable residual input, shutdown
    # of the CPU does not bound the remaining affine temperature trajectory.
    residual_power, thermal_storage, initial_y, limit = F(1), F(2), F(0), F(2)
    crossing_time = (limit-initial_y)*thermal_storage/residual_power
    require(initial_y + residual_power*(crossing_time+1)/thermal_storage > limit,
            "Missing-sink boundary was hidden by an affected-host label")
    return dict(admitted_heat_histories=accepted, comparison_bound=bound,
                average_only_temperature_counterexample=True,
                absent_passive_sink=dict(residual_power=residual_power, thermal_capacity=thermal_storage,
                                        cpu_power=0, limit=limit, equality_time=crossing_time,
                                        excess_after_one_more_quantum=True),
                continuous_statement="written integrating-factor/arrival-envelope proof in RESOURCES.md")


def finite_health_check():
    health, epsilon, service = F(30), F(2), F(3)
    horizon = health / (epsilon * service)
    require(horizon == 5, "Endurance arithmetic")
    return dict(initial_health=health, loss_per_service=epsilon, service_rate=service,
                maximum_horizon=horizon, no_replenishment=True,
                scope="stipulated irreversible-loss comparison, not a physical wear calibration")


def encode(x):
    if isinstance(x, F):
        return str(x)
    if isinstance(x, dict):
        return {k: encode(v) for k, v in x.items()}
    if isinstance(x, (list, tuple)):
        return [encode(v) for v in x]
    return x


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    runtime = runtime_inventory()
    result = encode(dict(status="runtime inventory bound; independent source admission and physical realization remain open",
                         sources={name: sha256((HERE/name).read_bytes().replace(b'\r\n', b'\n')).hexdigest()
                                  for name in (("RESOURCES.md", "resource_model.py", "PROGRAM.md", "program_source.py", "program_model.py", "program_results.json", "RUNTIME-PORTS.md", "port_model.py", "port_results.json", "INCIDENCE.md", "ACQUISITION.md", "BOUNDARIES.md", "boundary_model.py", "boundary_results.json", "TRANSDUCER.md", "transducer_model.py", "transducer_results.json", "HARD-BOUNDARY.md", "hard_boundary_model.py")+tuple(name for name in ("INITIAL-RETURN.md", "initial_return_model.py", "initial_return_results.json") if (HERE/name).exists()))},
                         storage=storage_checks(), reservations=reservation_checks(),
                         recurring=recurrent_supply_checks(), branches=branch_checks(),
                         inventories=[finite_inventory(bays=b) for b in (14, 80)],
                         runtime_inventory=runtime, runtime_supply=runtime_supply_checks(runtime), idle_recharge=reset_recharge_checks(),
                         shared_foreign_heat=[shared_foreign_heat_family(runtime,n) for n in (432,444,504)],
                         heat=heat_checks(), finite_health=finite_health_check()))
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    path = HERE / "resource_results.json"
    if args.write:
        path.write_text(rendered, encoding="utf-8")
        print("resource record written")
    elif args.check:
        require(path.read_text(encoding="utf-8") == rendered, "Resource record is stale")
        print("resource record matches")
    else:
        print(rendered)


if __name__ == "__main__":
    main()

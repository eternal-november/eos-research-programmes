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
    result = encode(dict(status="constructed resource adapter; source/PROGRAM binding and independent review pending",
                         sources={name: sha256((HERE/name).read_bytes().replace(b'\r\n', b'\n')).hexdigest()
                                  for name in ("RESOURCES.md", "resource_model.py")},
                         storage=storage_checks(), reservations=reservation_checks(),
                         recurring=recurrent_supply_checks(), branches=branch_checks(),
                         inventories=[finite_inventory(bays=b) for b in (14, 80)],
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

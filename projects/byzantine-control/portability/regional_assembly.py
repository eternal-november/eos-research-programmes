"""Exact port, rating, event and open-region checks for the connected B ladder."""

from collections import Counter, defaultdict
from fractions import Fraction as Q
from hashlib import sha256
import argparse
import json
from pathlib import Path

from regional_coupling import Port, State, flow, mode_request, system
from threshold_incidence_model import region_edges

HERE = Path(__file__).resolve().parent
M = 12 * (6 + 2**98) + 2
TAU = Q(1, 10**7)


def need(condition, message):
    if not condition:
        raise ValueError(message)


def owner(zone):
    first = zone.pairs[0][0]
    return first.row, first.column


def share(requests, cap):
    """Nonstoring fixed branches sharing one rated traversing port."""
    need(cap >= 0 and all(q >= 0 for q in requests), "Negative unsigned trunk rate")
    total = sum(requests)
    scale = cap / total if total > cap else Q(1)
    return tuple(q * scale for q in requests)


def limit_pairs(zone, efforts, main, thermal):
    """Two physical stages, with paired branch currents through both ends."""
    loads = tuple(abs(q) + abs(t) for q, t in zip(main, thermal, strict=True))
    raw_peak = max(loads)
    first = zone.endpoint_cap / raw_peak if raw_peak > zone.endpoint_cap else Q(1)
    gross = sum((abs(efforts[s]) + abs(efforts[d])) * load * first
                for (s, d), load in zip(zone.pairs, loads, strict=True))
    second = zone.world_work_cap / gross if gross > zone.world_work_cap else Q(1)
    return tuple(first * second * q for q in main), tuple(first * second * t for t in thermal)


def zone_branches(zone, state, efforts):
    main, thermal = [], []
    for (s, d), request in zip(zone.pairs, state.requests, strict=True):
        delta = efforts[s] - efforts[d]
        if state.mode == 0:
            q = zone.endpoint_cap * (max(delta, 0) if zone.directed else delta)
        elif state.mode == 1:
            q = min(state.stock, 1) * max(-zone.endpoint_cap, min(zone.endpoint_cap, request))
        else:
            q = Q(0)
        t = zone.m * zone.thermal_coefficient * min(2, state.theta) if state.mode in (0, 1) else Q(0)
        main.append(q)
        thermal.append(t)
    return limit_pairs(zone, efforts, main, thermal)


def network(zones, states, efforts, offers, external_quantity):
    """Evaluate one common cut with signed external quantity into the world."""
    need(set(states) == set(offers) == {z.name for z in zones}, "Incorrect zone incidence")
    ports = {p for z in zones for p in z.ports}
    need(set(efforts) == set(external_quantity) == ports, "Incorrect world incidence")
    outlets = defaultdict(list)
    quantity = dict(external_quantity)
    stored_rate = Q(0)
    cooling = Q(0)
    inlet = Q(0)
    for zone in zones:
        x = {p: efforts[p] for p in zone.ports}
        state = states[zone.name]
        q = flow(zone, state, x, offers[zone.name])
        need(zone_branches(zone, state, x) == (q["main"], q["thermal"]), "Serial limit mismatch")
        for p, flux in q["contributions"].items():
            quantity[p] += flux
        inlet += q["external_inlet"]
        stored_rate += q["Ydot"]
        cooling += q["bath"] + q["thermal_waste"]
        waste_rating = len(zone.pairs) * 2 * zone.m * zone.thermal_coefficient * zone.thermal_loss_effort
        outlets[owner(zone)].append((zone.external_inlet_cap, 2 * zone.bath_coefficient + waste_rating,
                                     q["external_inlet"], q["bath"] + q["thermal_waste"]))
    for rows in outlets.values():
        input_caps, exhaust_caps, inputs, exhausts = zip(*rows)
        need(share(inputs, sum(input_caps)) == inputs, "Source inlet trunk throttled")
        need(share(exhausts, sum(exhaust_caps)) == exhausts, "Source exhaust trunk throttled")
    external_work = sum(efforts[p] * external_quantity[p] for p in ports)
    world_work = sum(efforts[p] * quantity[p] for p in ports)
    need(sum(quantity.values()) == sum(external_quantity.values()), "Global quantity mismatch")
    need(world_work + stored_rate == external_work + inlet - cooling, "Global work mismatch")
    return quantity, outlets


def layout_checks(columns):
    zones = system(columns, M, region_edges)
    edges = region_edges(columns)
    size = 5 * columns - 2 + (columns + 1) // 3
    need(len(zones) == size, "Wrong zone count")
    owned = Counter(owner(z) for z in zones)
    attachments = Counter(p for z in zones for p in z.ports)
    need(len(owned) == 2 * columns and max(owned.values()) <= 5, "Wrong regional ownership")
    need(len(attachments) == 4 * columns and max(attachments.values()) <= 5, "Wrong gross port degree")
    graph = defaultdict(set)
    for a, b in edges:
        graph[a].add(b)
        graph[b].add(a)
    reached, pending = set(), [(0, 0)]
    while pending:
        v = pending.pop()
        if v not in reached:
            reached.add(v)
            pending.extend(graph[v] - reached)
    need(reached == set(owned), "Disconnected protected regions")
    states = {z.name: State(Q(0), Q(0), 0, (Q(0),) * len(z.pairs)) for z in zones}
    effort = {p: (Q(3, 5) if p.row == 0 else Q(2, 5)) for p in attachments}
    offers = {z.name: Q(0) for z in zones}
    external = {p: Q(0) for p in attachments}
    quantity, _ = network(zones, states, effort, offers, external)
    # Diagonals can add inter-row flow. Every ordinary rung carries m/250 on each coordinate.
    upper_out = -sum(rate for p, rate in quantity.items() if p.row == 0)
    need(upper_out >= 2 * columns * Q(M, 250), "Loss of extensive inter-region flow")
    # Simultaneous extreme efforts, independent failures, reverse requests, stock/heat faces.
    effort = {p: Q((-1)**(p.row + p.coordinate) * (5 + p.column)) for p in attachments}
    for j, zone in enumerate(zones):
        states[zone.name] = State((Q(0), Q(1, 2), zone.stock_capacity)[j % 3],
                                  (Q(0), Q(1))[j % 2], j % 4,
                                  tuple((-1)**k * 2 * zone.endpoint_cap for k in range(len(zone.pairs))))
        offers[zone.name] = zone.external_inlet_cap
    first_port = zones[0].ports[0]
    external[first_port] = Q(-3, 7)
    network(zones, states, effort, offers, external)
    # At the all-hot thermal face every former independent outlet still fits simultaneously.
    for zone in zones:
        states[zone.name] = State(Q(0), Q(2), 0, (Q(0),) * len(zone.pairs))
    network(zones, states, effort, offers, external)
    return {"columns": columns, "zones": size, "peak_world_attachments": max(attachments.values()),
            "largest_owner_bag": max(owned.values()), "initial_upper_outflow": str(upper_out)}


def event_and_shortfall():
    zones = system(3, M, region_edges)
    zone = zones[0]
    req = (Q(7),) * len(zone.pairs)
    start = State(Q(1), Q(0), 0, req)
    first, status = mode_request(zone, start, 1, req)
    after, rejected = mode_request(zone, first, 2, req)
    reverse, _ = mode_request(zone, start, 2, req)
    reverse, _ = mode_request(zone, reverse, 1, req)
    need((status, rejected) == ("accepted", "rejected-or-unfunded")
         and after.mode == 1 and reverse.mode == 2, "Lost competing order at one fixture")
    partial, refused = mode_request(zone, State(Q(1, 3), Q(0), 1, req), 2, req)
    need(refused == "rejected-or-unfunded" and partial.stock == 0 and partial.mode == 1
         and partial.theta * zone.thermal_capacity == Q(1, 3), "Lost the paid failed transfer")
    other = next(z for z in zones if z.name != zone.name and owner(z) == owner(zone))
    other_req = (Q(-2),) * len(other.pairs)
    other_start = State(Q(1), Q(0), 0, other_req)
    def two_updates(order):
        live = {zone.name: start, other.name: other_start}
        for target, mode, words in order:
            live[target.name], outcome = mode_request(target, live[target.name], mode, words)
            need(outcome == "accepted", "Separate local stock not delivered")
        return live
    jobs = ((zone, 1, req), (other, 2, other_req))
    pair = two_updates(jobs)
    need(pair == two_updates(reversed(jobs))
         and pair[zone.name].stock == pair[other.name].stock == 0, "Lost separate owned payments")
    power = zone.bath_coefficient
    d = max(Counter(owner(z) for z in zones).values())
    full_in = d * zone.external_inlet_cap
    small_exhaust = d * power / 2
    need(full_in - small_exhaust == d * 7 * power / 16, "Wrong trapped energy slope")
    need(share((power,) * d, small_exhaust) == (power / 2,) * d, "Scarce trunk not shared")
    return {"simultaneous_order_modes": [after.mode, reverse.mode],
            "undersized_trunk_bag": d, "stored_growth_per_q": str(full_in - small_exhaust),
            "zero_entry_two_capacity_crossing_after_q": "32/7"}


def world_chart():
    record = json.loads((HERE / "world_channel_results.json").read_text(encoding="utf-8"))
    sender = record["sender"]
    cut = Q(sender["physical_output"]["positive_weight_time"])
    need(cut < 2 and sender["nominal_captures"] == 96 and sender["ordinary_retirements"] == 1,
         "WORLD chart changed")
    need(Q(sender["physical_output"]["true_E_lower"]) > 1, "No funded chart")
    # One attached output, a 0.6 background inflow and the five coupler terminations.
    displacement = TAU * (Q(3, 5) + Q(1, M) + Q(1, 10)) * 2
    need(displacement < Q(1, 5), "Coupled effort could leave the WORLD work chart")
    quantity = Q(6, 5) * cut
    reference = sender["physical_output"]
    need(reference["protected_quantity"] == {"0": str(quantity)}
         and reference["physical_world_port_work"] == {"0": str(quantity / 2)},
         "Constant-effort WORLD reference changed")
    extra_work = (Q(1, 10) - displacement) * quantity
    need(extra_work > Q(17, 100), "Variable upper-row effort lost its finite work consequence")
    return {"cut_q": str(cut), "effort_displacement_upper": str(displacement),
            "extra_work_lower_over_old_chart": str(extra_work),
            "paid_WORLD_captures": sender["nominal_captures"]}


def report():
    files = ("REGIONAL-ASSEMBLY.md", "regional_assembly.py", "regional_coupling.py",
             "regional_coupling_results.json", "threshold_incidence_model.py", "FLOW-COMPOSITION.md",
             "WORLD-CHANNEL.md", "world_channel_results.json")
    return {"bindings_sha256_lf": {f: sha256((HERE / f).read_text(encoding="utf-8").encode()).hexdigest()
                                   for f in files},
            "layouts": [layout_checks(n) for n in (3, 4, 8, 17, 40)],
            "scarcity": event_and_shortfall(), "world_fixture": world_chart()}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="Write the checked finite fixtures")
    args = parser.parse_args()
    result = report()
    output = HERE / "regional_assembly_results.json"
    if args.write:
        output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    else:
        need(json.loads(output.read_text(encoding="utf-8")) == result, "Stale regional result record")
    print("Passed connected region checks on five ladders, paid ties, thermal scarcity and the B WORLD chart.")

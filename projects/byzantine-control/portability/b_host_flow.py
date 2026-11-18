"""Exact financial and flow cuts for B's common host port completion."""

from fractions import Fraction as Q
from hashlib import sha256
from itertools import product
from pathlib import Path
import argparse
import json
import subprocess

import rx_restoration as marker
import threshold_field_source as field

HERE = Path(__file__).resolve().parent
SOURCE = "theories-and-designs/byzantine-control/portability/"
A80 = "8f53d2983a9b6e3f9ff3a636c716de97f5c90050"
LEASE = "c9f09edc3440bc08f2e875883ee6e1f79e645ef3"


def need(value, reason):
    if not value:
        raise ValueError(reason)


def reduced_marker(w, v, live=False, h=Q(1, 8192)):
    """Actual branch currents and work; the 98–99 V section is the amendment."""
    need(0 <= w <= 300 and 0 <= v <= 300, "Outside the retained voltage range")
    need(not live or v >= 100, "A withdrawn front cannot be LIVE")
    bleed = marker.LEAK * v * v / 300
    taper = min(1, max(0, w - 98))
    rated = marker.IDLE + 300 * marker.LEAK
    forward = min(marker.IDLE + bleed, max(0, 4*w - v) * rated / 50)
    charge = Q(0) if live else taper * forward
    holding = marker.HOLD * min(1, (w / 99)**2)
    ballast = holding - 4*w*charge
    total_sink = 200*marker.C/h if live else bleed
    raw_current = charge - total_sink
    vprime = raw_current / marker.C
    if (v == 0 and vprime < 0) or (v == 300 and vprime > 0):
        vprime = Q(0)
    spill_heat = v * (raw_current - marker.C*vprime)
    heat = ballast + (4*w-v)*charge + v*total_sink + spill_heat
    need(min(ballast, charge, heat, spill_heat) >= 0, "Unfunded or negative dissipation")
    need(holding == marker.C*v*vprime + heat, "Front, transformer and ballast work diverged")
    return charge, holding, vprime, heat


def marker_case():
    samples = (Q(0), Q(50), Q(98), Q(197,2), Q(99), Q(100), Q(200), Q(300))
    tested = 0
    for w, v, live in product(samples, samples, (False, True)):
        if live and v < 100:
            continue
        q, _, dv, _ = reduced_marker(w, v, live)
        if live:
            need(q == 0 and dv == -200/Q(1,8192), "LIVE drain depends on the main supply")
        elif w >= 99 and v < 300:
            need(dv == marker.IDLE/marker.C, "Lost the original working-pressure front")
        elif w <= 98:
            need(q == 0, "A weak disconnected front drew input")
        tested += 1
    near = Q(99) - Q(1, 2**30)
    old_gap = marker.IDLE / marker.C  # v=0, old derivative below 99 is zero
    new_gap = reduced_marker(Q(99), Q(0))[2] - reduced_marker(near, Q(0))[2]
    need(new_gap == old_gap / 2**30, "Joined weakness allowance lost continuity")
    return {"examined_states": tested, "old_front_derivative_jump": str(old_gap),
            "new_front_change_over_two_to_minus_30": str(new_gap),
            "extra_at_98_5": str(reduced_marker(Q(197,2), Q(0))[0])}


def charged_dump(stock, cap, rate, t, floor=Q(1, 2)):
    """Simultaneous constant incoming power and physical dump, including both stops."""
    need(0 <= stock <= cap and rate >= 0 and t >= 0, "Invalid physical dump entry")
    k = cap / 100
    original = stock
    left = t
    if stock < floor and rate:
        dwell = min(left, (floor-stock)/rate)
        stock += dwell*rate
        left -= dwell
    if stock > floor and rate < k:
        dwell = min(left, (stock-floor)/(k-rate))
        stock += dwell*(rate-k)
        left -= dwell
    if stock >= floor:
        stock = min(cap, stock+max(0, rate-k)*left)
    burn = original + rate*t - stock
    need(0 <= stock <= cap and burn >= 0, "Dump lost or created work")
    return stock, burn


def dump_case():
    cap = field.PULSE_ENERGY
    k = cap/100
    a = cap/100000
    floor = field.DUMP_FLOOR
    final, heat = charged_dump(floor, cap, a, Q(100))
    need(final == floor and heat == a*100, "Bypassed inlet disappeared at the floor")
    test_count = 0
    for s, rate, t in product((Q(0), floor, Q(4), cap), (Q(0), a, k, 2*k), (Q(1,7), Q(100), Q(400))):
        z, h = charged_dump(s, cap, rate, t)
        split, q1 = charged_dump(s, cap, rate, t/3)
        result, q2 = charged_dump(split, cap, rate, 2*t/3)
        need((z,h) == (result,q1+q2), "An observer cut altered the physical accounting")
        test_count += 1
    return {"tested_subdivisions": test_count, "positive_dump_at_equal_floor": str(heat),
            "crossing_drift_below": str(a), "crossing_drift_above": str(a-k)}


def mechanical_case():
    pose = Q(11,10)
    speed = field.BIT_SPEED
    rotor = 22*(Q(2**20)+22*(2**16+field.REACTION))/16
    maximum = speed + rotor + pose
    motor = field.FORCE*maximum
    native = field.NATIVE_FORCE*maximum
    need(motor < 8 and native < 512, "Vector or native driver exceeds actual price")
    bit = speed
    v = Q(-1)
    force = field.FORCE
    col = Q(1,2)
    field_to_bit = force*bit
    field_to_pose = -force*col*v
    native_to_bit = field.NATIVE_FORCE*bit
    field_heat = 8 - field_to_bit - field_to_pose
    parent_heat = 512 - native_to_bit
    need(field_heat >= 0 and parent_heat >= 0, "Unfunded concurrent code work")
    need(field_heat + parent_heat + (field_to_bit+native_to_bit) + field_to_pose == 520,
         "Conjugate quantities do not sum on the shared bit")
    normal = 80*Q(11,5) + Q(11,10) + field.REACTION
    failed = 1360*Q(11,5) + 2*68 + Q(11,10) + field.REACTION
    need(failed > normal and failed < 3130, "Incorrect all-route housing rating")
    return {"relative_speed_bound": str(maximum), "one_motor_W_per_q": str(motor),
            "native_W_per_q": str(native), "conforming_pose_hold": str(normal),
            "failed_concentrated_pose_hold": str(failed),
            "free_vs_held_field_work_delta": str(field_to_bit)}


def raw_causal_cut():
    lane = field.PulseSelector(cut=False)
    # The abstract union of source lock and signal is not a locatable remote power grant.
    lane.trigger_energy[0].stock = field.TRIGGER_ENERGY
    good = lane.capture(0, 1, now=Q(0))
    need(good == "latched", "Actual capture unavailable")
    lane.trigger_energy[0].stock -= 1
    bad = lane.deliver(0, now=Q(1,2))
    need(bad == "unfunded-pending" and lane.pending[0] is not None, "Actual distal weak branch lost")
    lane.trigger_energy[0].stock += 1
    delivered = lane.deliver(0, now=Q(1,2))
    need(delivered == "active" and lane.slots[0] is not None, "Complementary funded branch lost")
    return {"one_unit_missing": bad, "restored_by_delivery": delivered,
            "aggregate_trigger_price": str(field.TRIGGER_ENERGY)}



def trigger_route(value, source_stock, receiving_stock, donor_cut, wire_intact=True):
    """One pressed, three-near/three-far strobe job at a fixed physical leaf."""
    need(value in (-1,0,1) and 0 <= receiving_stock <= 1024, "Invalid trigger state")
    if source_stock < 4096:
        return {"status": "unfunded", "source": source_stock, "receiver": receiving_stock}
    # Capture happens before the chosen later cut. The sequestered cell keeps its physical right.
    route_value = value
    near_logic = 3*6 + 32*16 + 8*6
    far_logic = 3*6 + 32*16 + 8*6
    need(near_logic <= 2048 and far_logic <= 1024, "Control price exceeds the actual end")
    if donor_cut == "before-launch":
        return {"status": "inhibited", "source": source_stock, "receiver": receiving_stock}
    need(donor_cut in ("none", "after-launch"), "Unknown cut")
    emitted = 2048
    selected = wire_intact and receiving_stock == 0
    received = 1024 if selected else 0
    far_heat = received
    local_heat = 4096-emitted
    wire_heat = emitted-received
    need(near_logic <= local_heat and (not selected or far_logic <= far_heat), "Unfunded control")
    need(local_heat + wire_heat + far_heat == 4096, "Lost a charge on the two-ended lead")
    return {"status": "delivered" if selected else "refused",
            "value": route_value if selected else None, "source": source_stock-4096,
            "receiver": receiving_stock, "local_heat": local_heat, "lead_and_dump_heat": wire_heat,
            "far_heat": far_heat, "active_cpu_now": donor_cut == "none"}


def trigger_point():
    K = 4*field.DEGREE*field.L
    slots = 3*K
    capacity = slots*1024
    scan = Q(3,8)+Q(1,16)+Q(3,8)
    earliest_timeout = Q(7)/Q(202,25)
    need(scan < earliest_timeout <= 1, "Receiver deadline no longer precedes all eight-edge timeouts")
    record = json.loads((HERE/"world_channel_results.json").read_text())["source"]
    oldcap = Q(record["reduced_U_capacity"])
    oldfloor = Q(record["qualified_voltage_floor_slack"])
    # The new capacitors have no credit as ready inlet or duplicated upstream stock.
    # Standby and two additional metering bits per physical slot receive a conservative bill.
    holding = slots*Q(2,1024)
    # The two bits change only at the aperture/clear. They may also be hit by the pre-existing
    # fixed physical override. Price the installed bit-rate ceiling rather than nominal duty.
    toggles = 2*slots*2**31
    # A global per-bit hard ceiling would exceed the whole raw supply. Do not install that update interface.
    need(toggles > Q(record["remaining_supply_rate"]), "Broad physical update obstruction disappeared")
    # Physical receipt energy and ingress polarity are the capacitor and its passive break-before-make contact.
    # Use the existing per-slot stage-valid bit and six-stage timer; no new writable state row or holding charge.
    draw = 2**14 * slots
    hard = 4*41*(8*2**31*capacity + 4*draw)
    parasitic = 4*41*slots*Q(1,2**60)
    need(Q(record["combined_bath_margin"]) > hard
         and Q(record["remaining_reaction"]) > parasitic, "Added receiving termination exceeds rating")
    need(oldfloor - Q(3,4)*capacity > 1, "Material slot capacity consumed the working chart")
    need(trigger_route(1,4096,0,"after-launch")["value"] == 1
         and trigger_route(-1,4096,1024,"none")["status"] == "refused"
         and trigger_route(1,4095,0,"none")["status"] == "unfunded"
         and trigger_route(-1,4096,0,"before-launch")["status"] == "inhibited"
         and trigger_route(1,4096,0,"none",False)["status"] == "refused", "Wrong trigger branch")
    return {"K": K, "additional_capacity": capacity,
            "amended_C_U": str(2*(oldcap-capacity)/2**128),
            "after_capacity_voltage_floor_slack": str(oldfloor-Q(3,4)*capacity),
            "all_mode_bath_margin_after_slot_terminals": str(Q(record["combined_bath_margin"])-hard),
            "remaining_reaction": str(Q(record["remaining_reaction"])-parasitic),
            "six_stage_deadline": str(scan), "earliest_timeout": str(earliest_timeout),
            "rejected_unpriced_two_bit_slope": str(toggles), "two_bit_holding_alone": str(holding)}


def joined_u():
    driver = json.loads((HERE/"world_channel_results.json").read_text())["source"]
    older = json.loads((HERE/"rx_power_results.json").read_text())["budget"]
    cap = Q(driver["reduced_U_capacity"])
    cu = 2*cap/2**128
    old = Q(older["U_C"])
    headroom = Q(driver["qualified_voltage_floor_slack"])
    need(old > cu and headroom > 0, "The old capacitor is no longer an obstructed comparison")
    for fraction in (Q(0), Q(1,4), Q(1,2), Q(1)):
        v = fraction * 2**64
        need(cu*v*v/2 == cap*fraction*fraction, "Incorrect unique source-energy observer")
    reference_energy_error = (old-cu)*(2**63)**2/2
    return {"rebound_C_U": str(cu), "old_U_error_at_300_V_transformer": str(reference_energy_error),
            "working_quarter_capacity_slack": str(headroom),
            "remaining_zone_margin": driver["combined_bath_margin"]}



def shared_body_cut():
    """A single instantaneous cut, including a scarce RX terminal and a spilling E."""
    power = marker.power
    row = power.catalogue()["rx"]
    L = Q(2**64, 600)
    origin_voltage, vs, vr, w = 300*L, Q(264), Q(250), Q(197, 2)
    u = origin_voltage/L
    terminal_limit = row.inlet()["limit"]
    upstream = power.phi(u-vs, power.SMALL, terminal_limit)
    line = power.phi(vs-vr, power.SMALL, terminal_limit)
    load = min(row.current, max(0, vr-w)/row.resistance)
    bs, br = vs/1000, vr/1000
    # These selected front voltages are below the independently priced shunt threshold.
    Udot = -u*upstream
    front_energy = vs*(upstream-line-bs) + vr*(line-load-br)
    line_heat = (u-vs)*upstream + (vs-vr)*line + vs*bs + vr*br + (vr-w)*load
    h = row.profile
    live = reduced_marker(w, Q(200), True, h)
    idle = reduced_marker(w, Q(0))
    count = 2*power.MARKERS["rx"]
    hold = 2*live[1]+(count-2)*idle[1]
    marker_energy = 2*marker.C*200*live[2]
    marker_heat = 2*live[3]+(count-2)*idle[3]
    # One paid divider (32 work and 512 metering) drives its fixed sink through both live fronts.
    profile = (32+power.METER)/h * w/99
    Wdot = w*load-row.bleed*w*w-hold-profile
    rx_heat = line_heat+row.bleed*w*w+marker_heat+profile
    need(Udot+front_energy+Wdot+marker_energy+rx_heat == 0, "One U/weak RX energy mismatch")
    T = Q(10)
    Tdot = -Q(41,10)*T
    world_to_bank = Q(3,5)*(Q(3,5)+Q(2,5))
    hold_motor = Q(1)
    spill = 4*T+world_to_bank-hold_motor
    need(spill > 0, "Full connected bank no longer spills on this cut")
    T_E_heat = T/10+hold_motor+spill
    need(Tdot-world_to_bank+T_E_heat == 0, "Jam and WORLD share one spilling E")
    signal_source = -Q(32768)
    signal_sink = Q(16384)
    need(signal_source+signal_sink+Q(16384) == 0, "Remote energy impulse at the new field terminal")
    return {"origin_current": str(upstream/L), "weak_main_v": str(w),
            "finite_rx_power": str(profile), "full_bank_spill_rate": str(spill),
            "two_ended_signal_power": str(signal_sink), "local_standing_fronts": count}



def return_boundary():
    rows = marker.power.catalogue()
    summed = sum(row.number * row.inlet()["limit"] for row in rows.values())
    private_other = 2**45
    need(summed > 6*private_other, "Return-incidence discriminator no longer separates the budgets")
    hot = Q(2**40)
    limit = rows["capture"].inlet()["limit"]
    old = marker.power.phi(Q(1), marker.power.SMALL, limit)
    current = min(old, 900*limit/(hot+1), 900*limit/hot)
    need(old == limit and hot*old > 900*limit and (hot+1)*current == 900*limit,
         "Confused absorption at a foldback with gross through-power")
    return {"raw_rail_single_end_current_sum": str(summed),
            "ratio_to_old_nonsupply_row": str(summed/private_other),
            "hot_endpoint": str(hot), "current_on_hot_equal_offset_pair": str(current)}


def git_read(rev, name):
    raw = subprocess.check_output(["git", "show", f"{rev}:{SOURCE}{name}"], cwd=HERE)
    return raw.decode("utf-8-sig").replace("\r\n", "\n")


def bound():
    records = (("A80-G3.md", A80), ("receiver_lease_results.json", LEASE))
    bindings = {}
    for name, rev in records:
        raw = git_read(rev, name)
        if name.endswith(".json"):
            json.loads(raw)
        bindings[name] = {"revision": rev, "sha256_lf": sha256(raw.encode()).hexdigest()}
    files = ("B-HOST-FLOW.md", "b_host_flow.py", "rx_restoration.py", "rx_power.py",
             "threshold_field_source.py", "world_channel_results.json", "REGIONAL-ASSEMBLY.md",
             "THRESHOLD-GATE-SOURCE.md", "FLOW-COMPOSITION.md", "PROJECTED-WORK-FLOW.md")
    return {"immutable": bindings, "local_sha256_lf": {n:sha256((HERE/n).read_text(encoding="utf-8").encode()).hexdigest()
                                                      for n in files}, "front": marker_case(),
            "dump": dump_case(), "mechanics": mechanical_case(), "source_cut": raw_causal_cut(),
            "single_upstream": joined_u(), "paid_trigger": trigger_point(), "same_host_cut": shared_body_cut(), "return_boundary": return_boundary()}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    result = bound()
    path = HERE/"b_host_flow_results.json"
    if args.write:
        path.write_text(json.dumps(result, indent=2, sort_keys=True)+"\n", encoding="utf-8")
    else:
        need(json.loads(path.read_text(encoding="utf-8")) == result, "Changed host flow evidence")
    print("Checked B common host stock, receiving fronts, dump contact, shared bit work and raw trigger cut.")

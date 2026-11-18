"""Source chronology and reached helper branches for the B later phase-ten cut."""

from __future__ import annotations

import argparse
import ast
from fractions import Fraction as Q
from hashlib import sha256
from dataclasses import dataclass
from types import SimpleNamespace
from math import floor
import json
from pathlib import Path

import common_response as prior
import legacy_realization as legacy
import threshold_design as design
import threshold_incidence_model as incidence
import threshold_program_model as program
import threshold_publication_model as publication


HERE = Path(__file__).resolve().parent
BASE = "1be94c7a611bfb4867d2fb4ce5e1b9a8fa6d23e8"
TRIP = "d26dc729f8fd12ec2b751f79f853076c32c8c711"
CUT = "48212f6db91a2038a6641028aaaabe0cdf4c15d2"
LEAD = "2aade1e91bbadb5c29d5d7945c7a460caae54d6e"
MOUNT = "f08190a108fd02eddc6bc377cfaeff644dba20ec"
POP = 12 * (6 + 2**98) + 2
TARGET = 39
need = program.need


def text_at(rev, name):
    return legacy.text_at(rev, "portability/" + name)


def record(rev, name):
    return json.loads(text_at(rev, name + "_results.json"))


def assigned_function(rev, filename, name, env):
    tree = ast.parse(text_at(rev, filename))
    f = next(n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == name)
    exec(compile(ast.Module(body=[f], type_ignores=[]), filename, "exec"), env)
    return env[name]


def binaries():
    old, _ = legacy.module_at(BASE, "portability/abort_protocol_alternative.py", "_history_lease")
    env = dict(
        old=old,
        legacy=legacy,
        program=program,
        design=design,
        checks=need,
        PIN="07f29286fcfd570299c7610bf9f9acd6267f2852",
    )
    compiler = assigned_function(BASE, "return_seat.py", "candidate", env)
    isa = program.load_isa()
    c, b = compiler(isa)
    old_receipt = record(BASE, "normal_response_transport")
    need(
        program.hash_text(json.dumps(c.image)) == old_receipt["source_image"] and len(c.nodes) == 3057,
        "Wrong physical image",
    )
    tick = assigned_function(
        BASE, "normal_response_transport.py", "check_tick", dict(ast=ast, need=need, program=program)
    )
    tick(isa, c)
    return isa, c, b


def bounds(c, b):
    base = record(BASE, "common_response")["exact"]
    lease = record(BASE, "receiver_lease")["interval"]
    normal = record(BASE, "normal_response_transport")
    cut = record(CUT, "b_cut_induction")["inequalities"]
    hand = record(TRIP, "b_handoff")["quantitative"]
    lead = record(MOUNT, "b_lead_installation")
    oldlead = record(LEAD, "b_lead_installation")
    mount = Q(lead["contact"]["known_parallel_force"])
    need(
        mount == Q(oldlead["contact"]["known_parallel_force"])
        and Q(lead["budget"]["force_slack"]) > 0
        and Q(lead["budget"]["pressure_floor_slack"]) > 0,
        "Unmatched mount, pressure or current installation",
    )
    tau = Q(base["tau"])
    rho = Q(81, 250)
    vmax = Q(261)
    imax = Q(21, 5)
    imin = -rho / 64
    F = Q(lease["Fmax"])
    f = Q(lease["Fmin"])
    visit = 11 * F
    prime = Q(lease["first_all_keys_including_fold"])
    delta = Q(101, 100)
    R = Q(base["repaired_settling"])
    band = R + Q(32000) / Q(9, 10) + delta
    job = Q(cut["supplier_window"])
    H = Q(lead["contact"]["effect_age"])
    action = Q(b["instruction_upper_bounds"]["helper"] + 64, 2**26) + Q(1, 64)
    need(
        H == Q(normal["source_receipt"]["new_effect_horizon"])
        and Q(lead["contact"]["old_sign_after_issue"]) == Q(372, 25) < 15
        and action < Q(1, 8),
        "Late visibility or physical command lifetime changed",
    )
    need(
        hand["planned_trip_work_upper"] == 526
        and Q(hand["strict_shutdown_margin_before_shunt"]) > 7000
        and Q(cut["raw_prime"]) == prime
        and Q(lease["per_key"]["maintenance"]["source_to_visible_age"]) + 2 * F < 1000,
        "Unusable raw lease, missed bank handoff or stale fold",
    )
    contact = assigned_function(TRIP, "handoff_contact.py", "retiring_side", dict(Fraction=Q))
    seg = c.constants["SEGMENT"]
    length = c.constants["BLEND_LIMIT"]
    need(
        contact(True, "NORMAL", 9 * seg + seg // 2, length, seg, length) == 0
        and contact(True, "NORMAL", 9 * seg + seg // 2, length - 1, seg, length) is None
        and lead["hardware"]
        and all(e["trip_work"] == 2048 and e["true_old_world_weight"] == 0 for e in lead["hardware"]),
        "No true funded trip on the zero-weight old side",
    )
    stage = 2101 * F + 2 * visit
    first_mature = R + Q(12500) / Q(9, 10) + 517 + stage + visit
    need(
        first_mature * Q(11, 10) < 40000 and prime + visit < 40000 / Q(11, 10),
        "Cannot ensure actual ISO and SHUNT visits before their endpoints",
    )
    hard = Q(record(BASE, "threshold_field_source")["point"]["mechanics"]["W_over_tau"])
    span = Q(hand["available_driver_approach"])
    block = 100 * tau / 32
    v_eq = Q(16644 * 64, 4097)
    i_eq = v_eq / 64
    old_q_error = (hard + Q(3, 2) * v_eq + i_eq) / 11**10 + rho / 32
    serving_error = (hard + v_eq + i_eq) / 11**10 + rho / 63
    serving_low = (v_eq - serving_error) / 128 + Q(1, 5000)
    serving_high = (v_eq + serving_error) / 128 + Q(1, 5000)
    need(
        Q(4061, 2000) < serving_low <= serving_high < Q(4063, 2000),
        "The same calibrated ADC cannot produce the displayed serving-side 2031",
    )

    need(
        block < span
        and v_eq - old_q_error / Q(3, 2) > 255
        and v_eq + old_q_error / Q(3, 2) < 261
        and 0 < i_eq - old_q_error < i_eq + old_q_error < imax,
        "Returning to the operating box would require a guessed initial stress",
    )

    proposal_force = 34 * Q(2) - 6 * Q(22, 5) - Q(11, 10) - rho
    need(
        proposal_force > 29 + 2 and 6 * Q(22, 5) + Q(11, 10) + rho < 28, "Oriented source pressure lost"
    )
    # Extra whole bands, visits and a stage wait are deliberately overcounted.
    pre = 4 * band + 3 * (R + 40000) + 2 * stage + 4 * delta + 1000
    need(pre < 350000, "Pre-shunt work budget")
    derivative = Q(1, 100) + imax + 64 * vmax
    brake_start_low = 255 - derivative * pre / (Q(3, 2) * tau)
    need(
        brake_start_low > 248
        and 16644 - imax - 64 * 255 > 0
        and Q(base["on_time_upper"]) < Q(c.constants["WARM_AT"]) / Q(11, 10),
        "Missing on-to-brake high antecedent",
    )
    lower = (brake_start_low - 88) * Q(3, 2) * tau / derivative
    upper = (261 - 88) * Q(3, 2) * tau / (64 * 88 - Q(1, 100) + imin)
    redraw = Q(normal["source_receipt"]["sequential_pair_upper"])
    need(
        lower > 1000 + prime + stage and upper < 25_000_000 and redraw <= Q(lease["pair_window"]),
        "No observation window before true crossing",
    )
    qtol = derivative * visit / tau
    spread = (2 * hard / 11**10 + 2 * rho / 32) / (Q(3, 2) * 128)
    history_age = Q(2000)
    need(
        history_age
        > Q(lease["per_key"]["maintenance"]["expiry_after_last_scheduled_old_offer"]) + prime + visit,
        "A still-readable sibling or partial fold could predate the actual head tube",
    )
    drift = derivative / (Q(3, 2) * tau * 128)
    low_sample = Q(11, 16) - spread - qtol / 192 + Q(1, 5000)
    high_sample = Q(11, 16) + spread + history_age * drift + Q(1, 5000)
    need(
        Q(1375, 2000) < low_sample <= high_sample < Q(1377, 2000),
        "Clocked spring heads do not all quantize to 688",
    )
    low = Q(11, 16) + spread + drift * H + mount / 128
    high = (132 - qtol - derivative * H / tau) / 128 - mount / 128
    gap = Q(995, 1000)
    need(
        low < 1 < high
        and gap > Q(4, 5)
        and gap < 1
        and Q(lead["contact"]["full_contact_upper"]) < 1
        and Q(lead["contact"]["nominal_clearance_deficit"]) < Q(1, 5),
        "Different admissibility does not hold at the material contacts",
    )
    bill_lo = (132 - qtol) ** 2 * tau / 6
    bill_hi = 2904 * tau
    need(
        0 < bill_lo <= bill_hi < Q(base["actual_J_when_no_positive_requests"]),
        "Unavailable coefficient work",
    )
    after = Q(base["clearance"]) + prime + 2 * visit + 2 * action + 15
    whole = 100000 + pre + upper + after + history_age
    frames = int(whole / f) + 2
    need(
        whole < job
        and frames < c.constants["WATCH_FRAMES"]
        and (Q(1, 8) - action) > 0
        and Q(1, 4) > Q(1, 8),
        "No single incumbent or intact timer through the response",
    )
    return dict(
        first_mature_from_band_entry=first_mature,
        serving_adc_interval=[serving_low, serving_high],
        prior_full_on_window=span,
        operating_box_entry=block,
        head_history=history_age,
        spring_spread=spread,
        pre_shunt_upper=pre,
        minimum_brake_start_v=brake_start_low,
        crossing_elapsed=[lower, upper],
        source_prime=prime,
        probe_pair=redraw,
        whole_incumbent_window=whole,
        watchdog_window=job,
        frame_decrements_upper=frames,
        stage_settlement=stage,
        fold_age=Q(lease["per_key"]["maintenance"]["source_to_visible_age"]) + 2 * F,
        q_over_tau_at_branch=[132 - qtol, Q(132)],
        quantizer_input=[low_sample, high_sample],
        mount_force=mount,
        low_load_upper=low,
        high_load_lower=high,
        working_gap=gap,
        full_effect_horizon=H,
        paid_jump_work=[bill_lo, bill_hi],
        head_change_delay_margin=Q(1, 8) - action,
        positive_action_after_clear=prime + 2 * visit + 2 * action + 15,
    )


def levels(isa, c, phase, position, iso, shunt):
    # An executable representative in a supported observation fibre. The query
    # proof permits all other values (including E_A) admitted on that history.
    p = c.constants
    v = prior.physical_view(isa, c, 623488)
    v[p["CAM"]] = phase * p["SEGMENT"] + p["GUARD"]
    v[p["BLEND"]] = position
    for side in (0, 1):
        v[p["BLEND_AT_A"] + side] = int(position == side * p["BLEND_LIMIT"])
        v[p["ANCHOR_IS_A"] + side] = int(side == (position == p["BLEND_LIMIT"]))
    v[p["ISO_DEF_A"]] = 0 if iso else 1000
    v[p["SHUNT_DEF_A"]] = 0 if shunt else 1000
    v[p["ISO_SEATED_A"]] = int(iso)
    v[p["SHUNT_SEATED_A"]] = int(shunt)
    v[p["SHUNT_OPEN_A"]] = int(not shunt)
    v[p["POWER_OFF_A"]] = 0
    v[p["ENERGY_A"]] = 623488
    return v


def projection(c, ports, v, load, affine):
    k = c.constants
    target, group = incidence.maintenance_group(POP, 0, TARGET)
    need(
        target == 20 and len(group) == 15 and len(set(p for p, _ in group)) == 15,
        "Incorrect actual voter incidence",
    )
    words = list(v) + [load, 2031, 5, 5]
    need(len(words) == k["FAST_TARGET_KEYS"], "Incomplete physical target keys")
    mapped = 0
    for s, (p, local) in enumerate(group):
        svc = affine(s)
        for j, val in enumerate(words):
            key = 3 + local * k["FAST_TARGET_KEYS"] + j
            for reader_bank in (0, 1):
                lane = 2 * incidence.neighbors(POP, p).index(0) + reader_bank
                actual = publication.route(c, POP, p, svc, lane, key, val)
                need(
                    actual is not None
                    and actual.provider == p
                    and actual.receiver == 0
                    and actual.slot == s
                    and actual.destination_key == 3 + TARGET * k["FAST_TARGET_KEYS"] + j
                    and actual.provider_bank == svc
                    and actual.receiver_bank == reader_bank,
                    "Unfunded/aliased socket",
                )
                if reader_bank == 1:
                    publication.install(ports, [actual])
            mapped += 1
    return mapped


def spring_taps(c, provider, member_force):
    # Use the fixed B transducer itself. This local stable-value representative
    # is licensed for every actual member by the proved quantization interval.
    cut_source = text_at(CUT, "b_cut_induction.py")
    defs = ast.Module(
        body=[
            n
            for n in ast.parse(cut_source).body
            if isinstance(n, ast.ClassDef) and n.name in ("SpringContact", "TapSite", "FixedTaps")
        ],
        type_ignores=[],
    )
    space = dict(
        dataclass=dataclass,
        Q=Q,
        incidence=incidence,
        require=need,
        raw=SimpleNamespace(MASK=(1 << 256) - 1),
    )
    exec(compile(defs, "<pinned B target transducer>", "exec"), space)

    def quant(value, error, lo, hi):
        # The bias belongs to the load ADC; on the gap input it still rounds
        # the real 0.995 to 995. A single selected physical read law suffices.
        return max(lo, min(hi, floor(value + Q(1, 5) + Q(1, 2))))

    contact = space["SpringContact"]
    cm = Q(3, 2) * 2**29
    force_b = Q(16644 * 64, 4097) / 128
    old = tuple(contact(member_force * 128 * cm, cm, Q(995, 1000), 0) for _ in range(11))
    new = tuple(contact(force_b * 128 * 2**29, Q(2**29), Q(995, 1000), 0) for _ in range(11))
    bank = SimpleNamespace(origin=provider, receivers=incidence.neighbors(POP, provider))
    site = space["TapSite"](SimpleNamespace(owner=20), (old, new))
    return space["FixedTaps"](bank, c.constants, {20: site}, (lambda: Q(1, 2), lambda: Q(1, 2)), quant)


def fresh_publisher(isa, c, b, s, provider, local, bank, v):
    k = c.constants
    cpu = program.initialized(isa, c)
    ports = program.ports_class(isa)(c)
    fixed = spring_taps(c, provider, Q(11, 16))

    class Heads:
        def get(self, key, missing):
            return fixed.functional(key) if key[0] == local else missing

    ports.functional = Heads()
    for rel, value in enumerate(v):
        ports.fast["head", 3 + local * k["FAST_TARGET_KEYS"] + rel] = value
    # A real cyclic scan takes this aligned visit every sweep. Use the
    # prior receiver-lease result for the paid repeated occurrences and TTL.
    start = local * k["RAW_TARGET_HEADS"]
    idx = start // k["FAST_BATCH"] * k["FAST_BATCH"]
    cpu.W[k["FAST_CURSOR"]] = idx
    calls = 0
    while cpu.W[k["FAST_CURSOR"]] < start + k["RAW_TARGET_HEADS"]:
        program.call(
            isa, c, ports, "publish_fast", (), b["instruction_upper_bounds"]["publish_fast"] + 10, cpu
        )
        calls += 1
    rows = publication.deliveries(c, POP, provider, bank, ports, 0, 1)
    opposite = publication.deliveries(c, POP, provider, bank, ports, 0, 0)
    need(
        {(x.source_key, x.destination_key, x.value) for x in rows}
        == {(x.source_key, x.destination_key, x.value) for x in opposite},
        "The real broadcast did not contain both fixed receiver-bank branches",
    )
    key = 3 + TARGET * k["FAST_TARGET_KEYS"]
    rows = [r for r in rows if key <= r.destination_key < key + k["FAST_TARGET_KEYS"]]
    seen = {r.destination_key - key: r.value for r in rows}
    need(
        len(rows) == len(seen) == k["FAST_TARGET_KEYS"]
        and all(r.provider_bank == bank and r.slot == s for r in rows)
        and [seen[k["VIEW_WORDS"] + j] for j in range(4)] == [688, 2031, 5, 5],
        "Actual fixed functional fold or source bank changed",
    )
    return rows, dict(
        provider=provider,
        local_target=local,
        bank=bank,
        calls=calls,
        captures=ports.samples,
        offers=ports.offers,
        keys=len(rows),
    )


def actual_calls(isa, c, b, limits):
    k = c.constants
    begin = k["TARGET_BASE"] + TARGET * k["TARGET_WORDS"]
    ports = program.ports_class(isa)(c)
    m = program.initialized(isa, c)
    visits = []
    _, roster = incidence.maintenance_group(POP, 0, TARGET)
    pubrows = []
    pubstats = []
    for slot, (origin, local) in enumerate(roster):
        v = levels(isa, c, 10, k["BLEND_LIMIT"], True, True)
        rows, stats = fresh_publisher(isa, c, b, slot, origin, local, slot % 2, v)
        pubrows.extend(rows)
        pubstats.append(stats)

    # The compiled frame tail checked in binaries() implements this exact
    # decrement on every completed frame; RANK renewals are separately bounded.
    def elapse(n):
        for field in ("TIMER", "STAGE_WAIT", "ABORT_WAIT", "EXIT_WAIT"):
            a = begin + k[field]
            m.W[a] = max(0, m.W[a] - n)

    def step(tag, phase, blend, iso, shunt, load, dt, expected):
        elapse(dt)
        n = projection(c, ports, levels(isa, c, phase, blend, iso, shunt), load, lambda s: s % 2)
        if tag == "later 688 read":
            # Current addressed offers overwrite their own records; other
            # banks, receipt ages and prior claims are not erased by a compare.
            publication.install(ports, pubrows)
        before = m.steps
        program.call(isa, c, ports, "helper", (TARGET,), b["instruction_upper_bounds"]["helper"] + 10, m)
        packet = next(t for t in reversed(ports.events) if t[0] == "command")
        stage, wait, last, timer, high, abort = (
            m.W[begin + k[x]] for x in ("STAGE_ID", "STAGE_WAIT", "LAST_PHASE", "TIMER", "HIGH", "ABORT")
        )
        need(
            packet[1] == TARGET and packet[4] == 20 and packet[6] == expected and abort == 0,
            "Unexpected local action at " + tag,
        )
        if expected:
            need(packet[8] == 20, "Wrong physical sign")
        visits.append(
            dict(
                cut=tag,
                command=list(packet[1:]),
                stage=stage,
                remaining_wait=wait,
                last=last,
                timer=timer,
                high=high,
                retired=m.steps - before,
                mapped_keys=n,
            )
        )

    full = k["BLEND_LIMIT"]
    for tag, phase, blend, iso, shunt, load, n, expected in (
        ("old phase 8", 8, 0, False, False, 2031, 0, 0),
        ("old phase 8 mature", 8, 0, False, False, 2031, 2100, k["ACT_PORT"]),
        ("phase 9 entry", 9, 0, False, False, 2031, 1, 0),
        ("phase 9 mature", 9, 0, False, False, 2031, 2100, k["BLEND_PORT"]),
        ("phase 9 opposite endpoint", 9, full, False, False, 2031, 60000, k["BLEND_PORT"]),
        ("phase 10 entry", 10, full, False, False, 2000, 20000, 0),
        ("phase 10 still waiting", 10, full, False, False, 2000, 2090, 0),
        ("phase 10 mature, both retracted", 10, full, False, False, 2000, 10, k["ISO_PORT"]),
        ("isolation seated", 10, full, True, False, 1990, 41000, k["SHUNT_PORT"]),
        ("shunt seated, load still high", 10, full, True, True, 1950, 41000, 0),
        ("later 688 read", 10, full, True, True, 688, 25_000_000, 0),
        (
            "still eligible after complete clearance",
            10,
            full,
            True,
            True,
            125,
            254_000_000,
            k["CUT_PORT"],
        ),
    ):
        step(tag, phase, blend, iso, shunt, load, n, expected)
    need(
        visits[3]["command"][2] == 1
        and all(x["command"][2] == 0 for x in (visits[7], visits[8], visits[-1])),
        "The helper applied to another bank",
    )
    need(
        visits[6]["remaining_wait"] == 10
        and visits[7]["remaining_wait"] == 0
        and visits[7]["timer"] == k["WATCH_FRAMES"]
        and visits[-1]["timer"] > 0,
        "Unformed phase-ten watchdog",
    )
    return dict(
        steps=visits,
        substitution_receipts=pubstats,
        stage_test_scope="Representative private branch/counter values and elapsed envelopes. No exact joint clock trace is inferred from the batched frame counts.",
    )


def report():
    for name in (
        "common_response.py",
        "legacy_realization.py",
        "threshold_program_model.py",
        "threshold_design.py",
        "threshold_program_source.py",
        "threshold_incidence_model.py",
        "threshold_publication_model.py",
    ):
        need(
            (HERE / name).read_text(encoding="utf-8-sig") == text_at(BASE, name),
            "Live source differs: " + name,
        )
    isa, c, b = binaries()
    cost = bounds(c, b)
    return prior.normalize(
        dict(
            bindings=dict(programme=BASE, trip=TRIP, cut=CUT, lead=LEAD, flexure=MOUNT),
            scope="Reached mathematical member with a later visit; reduced executable branch checks are not full clock orbits",
            cost=cost,
            visits=actual_calls(isa, c, b, cost),
            implementation_sha256=sha256(
                Path(__file__).read_bytes().replace(b"\r\n", b"\n")
            ).hexdigest(),
        )
    )


if __name__ == "__main__":
    opt = argparse.ArgumentParser()
    opt.add_argument("--write", action="store_true")
    args = opt.parse_args()
    result = json.dumps(report(), sort_keys=True, indent=2) + "\n"
    file = HERE / "b_phase_ten_history_results.json"
    if args.write:
        file.write_text(result, encoding="utf-8", newline="\n")
    else:
        need(file.read_text(encoding="utf-8") == result, "Stale phase-ten history")
    print(
        "Checked later B phase-ten branch, physical timing, candidate actions and paired contact bounds."
    )

"""Finite arithmetic, source-local commands, and raw witness scheduling for A80."""

from fractions import Fraction as Q
from math import ceil, floor
import ast
from collections import defaultdict, deque
from dataclasses import dataclass
import json

import a80_return_seat as seat


def need(test, message):
    if not test:
        raise AssertionError(message)


def bound_record(revision, path):
    return json.loads(seat.source.at(revision, path).decode("utf-8-sig"))


def proof_arithmetic(cert, t, source, initial):
    h = Q(t["H"])
    w = Q(cert["local_nontransferable_work"])
    rate = Q(t["unchanged_rate"])
    horizon = 2 * h + 2 * w
    need(
        1 + 2 + floor(3 + horizon * rate) == 6 and horizon * rate < 1,
        "Expanded common planning cover failed",
    )
    q = Q(t["quiet_epoch"])
    spacing = Q(t["true_same_bank_spacing"])
    all_rights = 40 * 2 * (80 + 128)
    stripe = ceil(q * (1 + all_rights + 80) / (1 - 80 * q / spacing)) + 1
    completion = Q(t["total"]) - Q(t["stripe"]) + stripe
    need(
        all_rights == 16640 and stripe == 57557690137 and h - completion > 3640881037,
        "Conservative per-socket renewal lacks a strict H margin",
    )
    need(
        Q(t["changed_functional_horizon"]) == Q(cert["functional_guard_horizon"])
        and Q(t["upper_load"]) < 1
        and Q(t["upper_clearance_deficit"]) < Q(1, 5),
        "Factual horizon changed",
    )
    a = source["parameters"]["world"]
    m = a["fixed_regional_population"]
    M = a["raw_world_flow_bound"]
    tau = Q(a["plant_time_per_hardware_quantum"])
    need(m == 12 * (6 + 2**98) + 2 and M == 2**98, "Unmatched external work and regional capacity")
    alpha = Q(initial["world"]["effect_age"])
    e = 2 * (Q(1, 200) + 4 * tau * alpha + Q(1, 2000)) + Q(1, 100)
    residue = Q(2, 11**10)
    error = e + Q(4) * tau / Q(1, 100) + residue
    upper = Q(84, 100) * (1 - Q(6, m)) - Q(6 + M, m) - Q(6406, 10000)
    lower = Q(5594, 10000) - Q(36, 100) - Q(6 + M, m)
    service = (Q(3, 10) - residue) * (1 - Q(6, m)) - Q(6 + M, m)
    need(
        error < Q(1, 25) and min(upper, lower) > Q(116, 1000) and service > Q(1, 5),
        "Positive-weight tracking, collar or regional service failed",
    )
    need(2 * tau * 50000 == Q(1, 100) and 2 * tau * 50000 < Q(1, 20), "No initialized collar room")
    need(
        Q(3, 40 * h) <= rate and 600 < spacing and Q(500) * Q(11, 10) / 40000 < Q(1, 50),
        "Adaptive overlap witness lacks timing separation",
    )
    return dict(
        H=h,
        W=w,
        planning=horizon * rate,
        stripe=stripe,
        return_slack=h - completion,
        load=Q(t["upper_load"]),
        clearance_deficit=Q(t["upper_clearance_deficit"]),
        upper=upper,
        lower=lower,
        service=service,
        tracking_error=error,
    )


def factual(isa, c):
    k = c.constants
    key = 3 + k["VIEW_WORDS"]
    answers = []
    for first in (491, 509):
        p = isa.RawPorts(c)
        m = isa.Machine(c, poison=0)
        for origin, val in enumerate((first, *([491] * 6), *([509] * 6))):
            p.fast[origin, 0, key] = val
            p.fast[origin, 0, key + 2] = 0
        m.enter("permission", (k["TARGET_BASE"], 0))
        need(
            m.run(p, until_yield=False) == "halt" and m.C == c.image,
            "Unformed policy or shared C mutation",
        )
        answers.append(m.result())
    need(answers == [1, 0], "An actual A80 private comparison ceased consuming the primary")
    return answers


def audited_bounds(t, source):
    delta = Q(1, 2**30)
    capture = source["capture_work"]
    old = Q(capture["raw_old_control_settle"])
    cold = Q(capture["raw_good_capture_upper"])
    first = Q(capture["receiver_private_strobe_lower"])
    last = Q(capture["receiver_private_strobe_deadline"])
    need(
        max(old, delta) + delta + delta == cold == Q(301, 100) * delta
        and first - cold == Q(49, 100) * delta
        and last == Q(404, 100) * delta,
        "Pending settlement/cold charge/indexed capture do not fit the true private aperture",
    )
    funding = bound_record(seat.gate.FROZEN, "local-control/port_resource_results.json")["supply"]
    design_rate = Q(t["host_U_rate"])
    need(
        funding["period"] == 6
        and funding["outage_duration"] == 2
        and Q(funding["on_power"]) == 2 * design_rate
        and Q(funding["on_period_available_work"]) == 8 * design_rate
        and Q(funding["outage_drawdown_lower"]) > 0,
        "Unmatched recurring source or empty outage",
    )
    quiet = Q(t["quiet_epoch"])
    spacing = Q(t["true_same_bank_spacing"])
    stripe = ceil(quiet * (1 + 16800 + 80) / (1 - 80 * quiet / spacing)) + 1
    worked = Q(t["total"]) - Q(t["stripe"]) + stripe + 50000
    launch = Q(101, 100)
    margin = Q(t["H"]) - (launch + worked)
    need(
        stripe == 58108448490 and margin > 3_090_070_000,
        "Strict time from the physical release to its full useful/retired terminal was lost",
    )
    half = Q(t["fresh_half"])
    h = Q(t["H"])
    need(
        2 * half + 50000 + Q(5347794885226509, 1048576) < h
        and Q(20000) / Q(11, 10) > 18000
        and 40 * h + 1100 + 3 * h + 2 * half < 45 * h + 1100,
        "A received role can fall outside its actual keeper audit flank or opportunity",
    )
    return margin, first - cold


def unchanged_routines(isa, amended):
    import parent_realization as parent

    revision = "c6972d943fe977a0cdc22d52ff45d41587efdb32"
    raw = seat.source.at(revision, "portability/image_transport.py").decode("utf-8-sig")
    # The transport checks every paired instruction and actual useful operand of
    # each unchanged routine. This primary family reads its image in cell_result.
    src = seat.replace_once(
        raw, 'need(code_readers=={"refresh_fields"}', 'need(code_readers=={"cell_result"}'
    )
    funcs = [
        n
        for n in ast.parse(src).body
        if isinstance(n, ast.FunctionDef) and n.name in ("segments", "compare_code")
    ]
    env = dict(ast=ast, need=need, defaultdict=defaultdict, parent=parent)
    exec(
        compile(ast.Module(body=funcs, type_ignores=[]), "<shared instruction comparison>", "exec"), env
    )
    isa.SOURCE = seat.Text(seat.gate.frozen("program_source.py"))
    baseline = isa.Compiler(amended.design).compile()
    result, _ = env["compare_code"](isa, baseline, amended)
    need(
        {"boot", "permission", "publish_queries", "publish_fast", "publish_plant", "estimate"}.issubset(
            result["closed"]
        )
        and "helper" in result["changed"]
        and "cell_result" in result["self_readers"],
        "Incomplete A80 policy comparison",
    )
    return result["compared_cells"], result["mapped_registers"]


def selected_body_witness(isa, c):
    # A charged abstract digital update. The actual chosen cartridge is the
    # already weighted, powered body, not an arbitrary unused spare of the host.
    # The same ordinary finite ISA and bank sampler serve the new and old words.
    for sign in (-1, 1):
        body = isa.Machine(c, poison=0)
        ports = isa.RawPorts(c)
        body.C[:4] = [
            isa.encode(isa.LI, 3, immediate=100 * sign),
            isa.encode(isa.LI, 4, immediate=-100 * sign),
            isa.encode(isa.IO, 5, 3, 2, isa.PRIM["world"]),
            isa.encode(isa.HALT),
        ]
        need(
            body.run(ports, budget=8, until_yield=False) == "halt"
            and ports.world_latch == (100 * sign, -100 * sign),
            "Charged selected body produced no actual latched action",
        )
        need(body.C != c.image and body.halted, "Release would have no retained adverse state")
    issue = Q(1, 64) + Q(1, 2**26) + Q(4, 2**26) + 2 + Q(1, 64)
    weight = Q(1, 2) - Q(11, 10) * 500 / 40000
    upper = weight * (-1 + Q(2, 1 + 4)) + (1 - weight)
    need(
        issue < 3 and weight > Q(48, 100) and upper < Q(23, 100),
        "No physical local service discriminator",
    )
    return issue, weight, upper


def world_actions(isa, c):
    receipts = ((1135, 1135, 0), (865, 865, 2000), (1001, 1000, 0))
    results = []
    for sumword, diffword, falseword in receipts:
        p = isa.RawPorts(c)
        m = isa.Machine(c, poison=0)
        for o in range(13):
            for b in range(2):
                p.fast[o, b, 0] = sumword if o >= 6 else falseword
                p.fast[o, b, 1] = diffword if o >= 6 else 2000 - falseword
        for key in range(3):
            p.fast["head", key] = 1000
        m.enter("frame")
        while not any(row[0] == "world" for row in p.events) and m.steps < 2_000_000:
            need(m.step(p), "Actual frame did not produce the prescribed local output")
        need(any(row[0] == "world" for row in p.events), "No actual WORLD")
        px = (sumword + diffword - 1000) // 2
        py = (sumword - diffword + 1000) // 2
        expected = tuple(max(30, min(90, 60 + (2 * (x - 500)) // 10)) for x in (px, py))
        need(tuple(p.world_latch) == expected and m.C == c.image, "A80 actual quantized world value")
        results.append(expected)
    return results


def footprint():
    # Execute the frozen incidence construction, not a fresh set of desired projected rows.
    incidence = seat.source.old_module("incidence_model.py")
    original = seat.source.at(seat.gate.FROZEN, "local-control/receiver_model.py").decode("utf-8-sig")
    tree = ast.parse(original)
    names = {"Incident", "ReachGraph", "footprint", "RawCell"}
    classes = ast.Module(
        body=[n for n in tree.body if getattr(n, "name", None) in names], type_ignores=[]
    )
    bits = (1 << 256) - 1
    scope = dict(
        incidence=incidence, defaultdict=defaultdict, deque=deque, dataclass=dataclass, MASK=bits
    )
    exec(compile(classes, "<frozen receiver incidence>", "exec"), scope)
    r = 0
    t = 1
    N = 432
    group = incidence.groups(r, t, N)[0]
    graph = scope["ReachGraph"](N)
    x, y = group[1:3]
    events = [scope["Incident"]("island", r, o) for o in (x, y)]
    union = set().union(*(graph.reach(token) for token in events))
    hosts, slots = graph.project(union, r, group)
    need(hosts == {r} and slots == {1, 2}, "Host identification collapsed two physical slot events")
    remote = 1
    observed = next(
        gr for t in incidence.neighbors(remote, N) if r in (gr := incidence.groups(remote, t, N)[0])
    )
    hs, js = graph.project(union, remote, observed)
    need(
        hs == {r} and js == {observed.index(r)} and ("outgoing", x) not in union,
        "Off-body damage gained an uninstalled sending identity",
    )
    cell = scope["RawCell"]()
    cell.receive(771, 17)
    for _ in range(16):
        cell.tick()
    need(cell.capture() == 771, "Stopped/elapsed receiver distinction disappeared")
    cell.tick()
    need(cell.capture() == bits, "Actual expiry did not clear the returned origin's old operand")
    return (events[0].kind, r, x)


def recurrent_witness(h, rate):
    # Each realized next cluster can wait longer than the periodic example.
    # The per-stream proof in the note uses its minimum spacing only.
    starts = [n * 40 * h + shift for n in range(4) for shift in (0, 250, 600)]
    for i, a in enumerate(starts):
        for j in range(i, len(starts)):
            need(j - i + 1 <= floor(3 + rate * (starts[j] - a)), "Closed endpoints exceed raw occupancy")
    ends = sorted({t for s in starts for t in (s, s + 500)})
    need(
        max(sum(s <= t < s + 500 for s in starts) for t in ends) == 2
        and Q(3, 40 * h) <= rate
        and Q(600) < Q(7500000000, 11),
        "No real overlap/strict nonreturn separation",
    )


def main():
    isa, c, _, cert, _, _, _, _ = seat.compile_images()
    t = bound_record(
        "7bce24369d3a7c31331704bb3c7038fac0e4374e", "portability/a80_return_seat_results.json"
    )["time_and_resources"]
    source = bound_record(seat.gate.FROZEN, "local-control/port_source_results.json")
    initial = bound_record(seat.gate.FROZEN, "local-control/initial_return_results.json")
    nums = proof_arithmetic(cert, t, source, initial)
    print("Strict release margin and cold-capture aperture slack", audited_bounds(t, source))
    recurrent_witness(Q(t["H"]), Q(t["unchanged_rate"]))
    print(
        "Expanded planning rate exposure",
        nums["planning"],
        "and strict return slack",
        nums["return_slack"],
    )
    print(
        "Unchanged addressed cells/registers",
        unchanged_routines(isa, c),
        "and selected-body bound",
        selected_body_witness(isa, c),
    )
    print(
        "A80 primary-dependent factual calls",
        factual(isa, c),
        "and quantized WORLD",
        world_actions(isa, c),
    )
    print("Two island slots stay distinct at the receiver. One example is", footprint())
    print(
        "Regional signed margins", nums["upper"], nums["lower"], "and delivered floor", nums["service"]
    )


if __name__ == "__main__":
    main()

"""Finite custody and aisle handoff. Python 3.12, standard library only."""
import argparse
from dataclasses import dataclass
from itertools import product
import json

TRANSFER_LOAD, CAPACITY = 4, 4
EARLY = ("wait", "probe", "prepare_cradle")
LATE = ("wait", "release", "cradle", "interlock")


@dataclass(frozen=True)
class World:
    partial: bool
    lost: bool
    # A fixed prior support duty occupies the early transfer preparation
    # position. During the probe phase its remaining support load is 2 or 3.
    probe_duty: int = 2
    # A different recurring demand on the same support starts at t=3 in the
    # reference, or one tick sooner in the adverse instance.
    other_early: bool = False
    error: int = 0  # in half-load units


def worlds(sensor="exact", probe_duty=2, other_early=False):
    return [
        World(partial, lost, probe_duty, other_early, error)
        for partial, lost in product((False, True), repeat=2)
        for error in ((0,) if sensor == "exact" else (-1, 0, 1))
    ]


def prefix():
    """Executed identical actions before exogenous latch motion/report split."""
    return [[-1, "A-approaches-with-load"], [0, "A-engages-support"],
            [0, "B-commands-latch"], [0, "D-holds-cradle-setup-position"]]


def step_to_decision(w, first):
    trace = prefix()
    trace += [[1, "latch-partial" if w.partial else "latch-seated"]]
    # Allocation of the full four units by support: in a partial latch B can
    # take one unit; in a seated latch B can take three before A retracts.
    b_base = 1 if w.partial else 3
    demand = 0
    if first == "probe":
        # The test places one unit from A plus the not-yet-latched
        # differential on the shared support. Keep A loaded throughout.
        demand = min(2, TRANSFER_LOAD - b_base)
    if first == "prepare_cradle":
        # A full cradle cannot make an early transfer while setup remains
        # physically held. The attempted action is refused and consumes the
        # test phase. No hidden latch sensor or new authority is acquired.
        trace += [[1, "early-cradle-refused-setup-in-use"]]
    a_during = TRANSFER_LOAD - b_base - demand
    assert a_during >= 0 and a_during + b_base + demand == TRANSFER_LOAD
    safe = demand + w.probe_duty <= CAPACITY
    if first == "probe":
        trace += [[1, "probe-load-share", dict(A=a_during, B=b_base, cradle=demand,
                                                D=w.probe_duty, capacity=CAPACITY)]]
    report = "missing" if w.lost else "partial" if w.partial else "seated"
    signal = str(2*demand + w.error) if first == "probe" else "none"
    observation = (report, signal)
    trace += [[2, "local-evidence", observation]]
    return (trace, observation, safe)


def finish(w, first, f, *, true_chooser=False):
    trace, obs, safe_so_far = step_to_decision(w, first)
    if true_chooser:
        # This comparator explicitly adds a direct hardware latch-state
        # interface; it is not a permitted controller in the base game.
        f = "cradle" if w.partial else "release"
    joint_service = False
    if f == "wait":
        trace += [[2, "wait-with-old-support"]]
    elif f in ("release", "interlock"):
        if w.partial and f == "interlock":
            trace += [[2, "passive-interlock-refuses-old-carrier-release"]]
        elif w.partial:
            safe_so_far = False
            trace += [[2, "unsafe-release-without-custody"]]
        else:
            joint_service = True
            trace += [[2, "release-start"], [3, "B-load-bearing-and-A-clear"]]
    elif f == "cradle":
        if not w.partial:
            trace += [[2, "seated-geometry-blocks-cradle"]]
        else:
            ongoing_duty = 1 if w.other_early else 0
            if TRANSFER_LOAD + ongoing_duty <= CAPACITY:
                trace += [[2, "cradle-takes-load", dict(cradle=4, D=ongoing_duty, capacity=CAPACITY)], [3, "load-settled-on-fixed-rack-and-A-clear"]]
                joint_service = True
            else:
                trace += [[2, "cradle-refused-live-duty"]]
    else:
        raise ValueError(f)
    if w.other_early:
        trace += [[2, "D-next-duty-start"]]
    else:
        trace += [[3, "D-next-duty-start"]]
    # C has a distinct passage obligation, witnessed by the aisle being
    # clear at its given passage event. D uses the separate support stock;
    # protecting that allocation by refusal can leave C unserved.
    trace += [[3, "C-passes" if joint_service else "C-passage-missed"]]
    d_service = first != "probe" or w.probe_duty + (2 if w.partial else 1) <= CAPACITY
    return dict(safe=safe_so_far, service=joint_service, d_service=d_service, observation=obs,
                trace=sorted(trace,key=lambda x:x[0]))


def winner_sets(ws, first):
    """Independent relational reference using support balance and action domains."""
    allowed_by_observation = {}
    for w in ws:
        # Derive exact feasible last actions from custody and capacity. This
        # does not call either simulator step when calculating the answer.
        obs = ("missing" if w.lost else "partial" if w.partial else "seated",
               str((4 if w.partial else 2) + w.error) if first == "probe" else "none")
        safe_probe = first != "probe" or w.probe_duty + (2 if w.partial else 1) <= CAPACITY
        accepted = ({"cradle"} if not w.other_early else set()) if w.partial else {"release", "interlock"}
        if not safe_probe:
            accepted = set()
        allowed_by_observation.setdefault(obs, set(LATE)).intersection_update(accepted)
    # Cross-check reference against simulator and every final command.
    for obs, allowed in allowed_by_observation.items():
        concrete = set()
        for late in LATE:
            arms = [finish(w, first, late) for w in ws if step_to_decision(w, first)[1] == obs]
            if all(o["safe"] and o["service"] and o["d_service"] for o in arms):
                concrete.add(late)
        assert concrete == allowed
    return allowed_by_observation


def case(sensor, probe_duty, other_early):
    ws = worlds(sensor, probe_duty, other_early)
    return {first: [{"observation": list(obs), "choices": sorted(actions)}
                    for obs, actions in sorted(winner_sets(ws,first).items())]
            for first in EARLY}


def main():
    baseline = worlds()
    incumbent, repaired, added_interface = [], [], []
    for w in baseline:
        report = step_to_decision(w, "wait")[1][0]
        inc = finish(w,"wait","cradle" if report == "partial" else "release")
        measurement = step_to_decision(w, "probe")[1][1]
        rep = finish(w,"probe","cradle" if int(measurement) > 3 else "release")
        oracle = finish(w,"wait","wait",true_chooser=True)
        config = dict(partial=w.partial,lost=w.lost)
        incumbent.append(dict(config, **inc))
        repaired.append(dict(config, **rep))
        added_interface.append(dict(config, **oracle))
    assert [(r["safe"],r["service"]) for r in incumbent] == [(True,True)]*3+[(False,False)]
    assert all(r["safe"] and r["service"] and r["d_service"] for r in repaired + added_interface)
    assert all(r["trace"][:len(prefix())]==prefix() for r in incumbent+repaired)
    scenarios = {"exact": case("exact",2,False),"ambiguous": case("overlap",2,False),
                 "probe_overload": case("exact",3,False),"earlier_duty": case("exact",2,True)}
    for scenario, cases in scenarios.items():
        for strategy, fibres in cases.items():
            assert all(f["choices"] for f in fibres) == (scenario=="exact" and strategy=="probe")
    assert finish(World(True,True),"wait","interlock")["safe"]
    assert not finish(World(True,True),"wait","interlock")["service"]
    envelopes = {
        "aligned": [World(partial, lost, 3 if partial else 2) for partial,lost in product((False,True),repeat=2)],
        "complementary": [World(partial, lost, 2 if partial else 3) for partial,lost in product((False,True),repeat=2)],
    }
    aligned, complementary = envelopes.values()
    for get in (lambda w: w.partial, lambda w: w.probe_duty, lambda w: w.lost):
        assert sorted(map(get,aligned)) == sorted(map(get,complementary))
    coupling = {}
    for name, ws in envelopes.items():
        coupling[name] = dict(support_pairs=sorted({(2 if w.partial else 1,w.probe_duty) for w in ws}),
                              winning={first: [{"observation": list(obs), "choices": sorted(actions)}
                                      for obs, actions in sorted(winner_sets(ws,first).items())] for first in EARLY})
    for name, envelope in coupling.items():
        assert [a for a, fs in envelope["winning"].items() if all(f["choices"] for f in fs)] == (
            ["probe"] if name == "complementary" else [])
    return dict(incumbent=incumbent,repaired=repaired,added_interface=added_interface,winning=scenarios,coupling=coupling)


if __name__ == "__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--json",action="store_true")
    out=main()
    if p.parse_args().json:
        print(json.dumps(out,sort_keys=True,indent=2))
    else:
        for pair in zip(out["incumbent"],out["repaired"]):
            a,b=pair
            print(f'partial={a["partial"]} lost={a["lost"]}: '
                  f'incumbent (safe={a["safe"]}, service={a["service"]}), '
                  f'probe (safe={b["safe"]}, service={b["service"]})')
        for scenario, cases in out["winning"].items():
            print(scenario + ": " + str([k for k,v in cases.items() if all(f["choices"] for f in v)]))

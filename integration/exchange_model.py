"""Same-mission protected-limiter removal and actual peer-enforcement replacement."""
from __future__ import annotations
from dataclasses import replace
from itertools import product
from pathlib import Path
import argparse, hashlib, json
import core_bridge as bridge
s = bridge.source

class RequestedMotor(s.PeerBrakes):
    """Same requested-input alphabet/carrier/faults; optional baseline-only limiter."""
    def __init__(self, limited):
        super().__init__(s.BrakeConfig())
        self.limited = limited
    def outcomes(self, fault, state, observation, issued):
        for out in super().outcomes(fault, state, observation, issued):
            effective = out.event["motor_input"]
            requests = range(7) if fault.motor_bad else (4,)
            for request in requests:
                realized = min(request, 5) if self.limited else request
                if realized == effective:
                    event = dict(out.event, requested_motor_input=request,
                                 effective_motor_input=realized,
                                 protected_limiter=self.limited)
                    yield s.Outcome(out.state, out.delivered, out.violations, event)

def off_policy():
    t = s.Table(("low", "high"), ("boot",), (0,), ((0, 0),), ((0, 0),))
    return (t,) * 3

def failure_trace():
    k = RequestedMotor(False)
    f = s.BrakeFault(True)
    x = s.BrakeState(4, 0, ((0, 0, 0),), ())
    trace = []
    for _ in range(3):
        o = next(iter(k.observations(f, x)))
        out = next(y for y in k.outcomes(f, x, o, (0, 0, 0))
                   if y.event["requested_motor_input"] == 6 and y.event["actual_delivery"] == 0)
        trace.append({"before": s.serial(x), "event": out.event,
                      "after": s.serial(out.state), "violations": out.violations})
        x = out.state
    assert [r["after"]["x"] for r in trace] == [8, 10, 11]
    assert trace[-1]["violations"] == ("world_speed",)
    # Same actual history in the normal companion delivers positive service.
    companion = s.BrakeState(4, 0, ((0, 0, 0),), ())
    delivery = []
    for _ in trace:
        o = next(iter(k.observations(s.BrakeFault(False), companion)))
        out = next(iter(k.outcomes(s.BrakeFault(False), companion, o, (0, 0, 0))))
        assert not out.violations and out.event["actual_delivery"] >= 1
        delivery.append(out.event["actual_delivery"])
        companion = out.state
    return {"adversarial_device": trace, "normal_companion_delivery": delivery,
            "joint_fault": "one bad motor, zero bad planners/actuators; two-device aggregate service remains positive"}

def local_checks(k, tables):
    result = s.verify(k, tables, full=True)
    assert result["winning"]
    # Intact program OFF never suppresses independently faulty effects.
    f = s.BrakeFault(True, (), (0,))
    x = s.BrakeState(4, 6, ((0, 0, 0),), ())
    o = next(iter(k.observations(f, x)))
    outcomes = tuple(k.outcomes(f, x, o, (0, 0, 0)))
    assert any(y.event["actual_engagement"][0] == 1 and
               y.event["issued"][0] == 0 for y in outcomes)
    assert {y.event["requested_motor_input"] for y in outcomes} == set(range(7))
    return result

def envelope_baseline():
    # Cartesian arithmetic check complements the analytic invariant proof.
    cases = 0
    for x, h, e, u in product(range(11), range(7), range(4), range(6)):
        xp = max(0, (5*x + 10*u - 10*e)//10)
        hp = (5*h + x*e)//10
        assert xp <= 10 and hp <= 6
        if x >= 1 and u == 4:
            assert xp >= 1
        cases += 1
    return cases

def common_input_check():
    limited, free = RequestedMotor(True), RequestedMotor(False)
    assert limited.config == free.config
    assert (limited.x_cap, limited.heat_cap) == (free.x_cap, free.heat_cap)
    faults = tuple(free.faults())
    assert faults == tuple(limited.faults())
    initial_count = 0
    for f in faults:
        assert tuple(free.initials(f)) == tuple(limited.initials(f))
        assert free.service(f) == limited.service(f)
        assert free.recurrent_service(f) == limited.recurrent_service(f)
        for initial in free.initials(f):
            initial_count += 1
            assert tuple(free.observations(f, initial.state)) == tuple(limited.observations(f, initial.state))
    return {"joint_faults": len(faults), "initial_scenarios": initial_count,
            "same_config_carrier_initial_information_observations_mission": True,
            "source_carrier_bounds": [free.x_cap, free.heat_cap],
            "only_effect_difference": "effective torque for a faulty request6 is5 or6"}

def bridge_probe(k, tables):
    initial = bridge.initial_boundaries(k, tables)
    b = next(b for b in initial if b.node.fault == s.BrakeFault(True, (), (0,))
             and b.node.state.x == 4 and b.node.state.heat == 6)
    actual = tuple(bridge.core_successors(k, b, bridge.profile(k, tables, b)))
    expected = tuple(k.outcomes(b.node.fault, b.node.state, b.observation,
                               bridge.masks(k,b,bridge.profile(k,tables,b))[0]))
    assert len(actual) == sum(len(tuple(k.observations(b.node.fault, out.state))) for out in expected)
    assert all(not y.violations for y,_ in actual)
    assert all(y.previous_effect.performed for y,_ in actual)
    assert any(event["requested_motor_input"] == 6 for _,event in actual)
    return {"actual_source_outcomes": len(expected), "prepared_core_successors": len(actual)}

def reproduce():
    common = common_input_check()
    baseline = local_checks(RequestedMotor(True), off_policy())
    replacement = local_checks(RequestedMotor(False), s.threshold_policy())
    no_replacement = s.verify(RequestedMotor(False), off_policy())
    assert not no_replacement["winning"] and "world_speed" in no_replacement["violations"]
    # The original parameter theorem and actual-source exhaustive result, rather
    # than these boundary probes, support the unbounded replacement policy.
    return {"common_context": common, "baseline_envelope_arithmetic_cases": envelope_baseline(),
            "limited_off_policy": baseline, "unlimited_threshold_policy": replacement,
            "unlimited_off_policy": no_replacement, "same_mission_failure": failure_trace(),
            "core_bridge_probes": {"limited": bridge_probe(RequestedMotor(True), off_policy()),
                                  "unlimited": bridge_probe(RequestedMotor(False), s.threshold_policy())},
            "fleet_scope": {"J": "any finite J>=2", "bad_motor_bound": "0<=p<J",
                            "per_tick_actual_delivery_lower_bound": "J-p",
                            "separate_heat_sum_bound": "6*J",
                            "full_global_graph_enumerated": False},
            "source_hashes": {p.name: hashlib.sha256(p.read_bytes().replace(b"\r\n", b"\n")).hexdigest()
                              for p in [Path(__file__), Path(__file__).with_name("EXCHANGE.md"),
                                        Path(__file__).with_name("Exchange.lean"), Path(bridge.__file__),
                                        Path(s.__file__)]}}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--write", action="store_true")
    ap.add_argument("--check", action="store_true")
    args=ap.parse_args()
    if args.write == args.check:
        ap.error("choose exactly --write or --check")
    result=reproduce()
    text=json.dumps(result,indent=2,sort_keys=True)+"\n"
    path=Path(__file__).with_name("exchange_results.json")
    if args.write: path.write_text(text,encoding="utf-8",newline="\n")
    elif path.read_text(encoding="utf-8") != text: raise SystemExit("Exchange reproduction mismatch")
    print(json.dumps({k: {a:v for a,v in result[k].items() if a in ("winning","explored_states","checked_edges")}
                      for k in ("limited_off_policy","unlimited_threshold_policy","unlimited_off_policy")},sort_keys=True))
if __name__=="__main__": main()

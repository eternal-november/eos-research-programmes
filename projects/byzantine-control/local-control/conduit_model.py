"""Exact contact-network adapter. Physical source admission is separate."""
from __future__ import annotations

import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
import json
from pathlib import Path
import sys

if sys.flags.optimize:
    raise RuntimeError("Unoptimized Python is required")

HERE = Path(__file__).resolve().parent
NAMES = (
    "SUPPLY_IN", "SUPPLY_RETURN", "MAINTENANCE_FEED", "MAINTENANCE_RETURN",
    "WORLD_1", "WORLD_2", "DATA_TX", "DATA_RX", "RUNTIME_WRITE",
    "ACTIVE_SENSE", "SERVICE",
)


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def serial(obj):
    if isinstance(obj, F):
        return str(obj)
    if isinstance(obj, dict):
        return {key: serial(value) for key, value in obj.items()}
    if isinstance(obj, (list, tuple)):
        return [serial(value) for value in obj]
    return obj


def source_hash(name):
    raw = (HERE / name).read_text(encoding="utf-8-sig").replace("\r\n", "\n")
    return sha256(raw.encode("utf-8")).hexdigest()


def contact(c, b, j, voltage, rating=F(1), scale=F(1)):
    h = c * (1-b)
    node = scale*j + h*voltage
    current = rating*h/scale*(node-voltage)
    dump = rating*(1-h)/scale*node
    source_power = rating*j*node
    body_power = current*voltage
    branch_heat = rating*h/scale*(node-voltage)**2
    dump_heat = rating*(1-h)/scale*node**2
    return dict(h=h, node=node, current=current, dump=dump,
                source_power=source_power, body_power=body_power,
                branch_heat=branch_heat, dump_heat=dump_heat)


def algebra():
    values = [F(i, 10) for i in range(11)]
    count = 0
    for c, b, j, voltage in product(values, values, (F(19,10), F(39,20), F(2)),
                                  (F(-1,5), F(-1,10), F(0), F(1,10), F(1,5))):
        out = contact(c, b, j, voltage)
        require(out["current"] + out["dump"] == j, "KCL fails")
        require(out["source_power"] == out["body_power"] + out["branch_heat"] + out["dump_heat"],
                "Power identity fails")
        require(out["branch_heat"] >= 0 and out["dump_heat"] >= 0, "Active resistor hidden")
        h = out["h"]
        require(out["current"] == h*j-h*(1-h)*voltage, "Wrong current relation")
        require(out["current"] >= 0, "Normalized magnitude needs sign accounting")
        e = out["current"]-2*h
        require(F(-3,20) <= e <= F(1,20), "Coarse residual interval fails")
        # The sharp lower comparison is e >= (h-3/4)^2/5 - 9/80.
        lower = (h-F(3,4))**2/F(5)-F(9,80)
        require(e >= lower >= F(-9,80), "Sharp quadratic bound fails")
        if c == 0 or b == 1:
            require(out["current"] == 0, "Open or full-shunt current is not zero")
        if c == 1 and b == 0:
            require(out["current"] == j >= F(19,10), "Loaded contact lost")
        count += 1
    # Endpoint minimizers show the sharper residual interval is attained.
    low = contact(F(3,4), F(0), F(19,10), F(1,5))["current"]-F(3,2)
    high = contact(F(1,2), F(0), F(2), F(-1,5))["current"]-1
    require(low == F(-9,80) and high == F(1,20), "Sharp witnesses missing")
    return dict(cases=count, KCL=True, exact_power_identity=True,
                coarse_residual=[F(-3,20), F(1,20)],
                sharp_residual=[low,high], sharp_residual_range=high-low,
                pressure_cap=F(41,20), actual_open_current=0,
                source_power_per_rating_scale=F(22,5))


def temporal():
    # Each pair respects actual motion. Source/terminal values can jump freely
    # inside their ranges; compare against the later maximum at the same lane.
    cases = 0
    speed = F(11,10)
    rate_c = speed/60000
    rate_b = speed/40000
    load_rate = 2*(rate_c+rate_b)
    require(load_rate == F(11,120000) < F(1,10000), "Speed conversion fails")
    points = [F(i, 4) for i in range(5)]
    for dt, c0, b0, dc, db in product((F(0),F(1),F(100),F(2000),F(40000)),
                                    points, points, (-1,0,1), (-1,0,1)):
        c1 = min(F(1), max(F(0), c0+dc*rate_c*dt))
        b1 = min(F(1), max(F(0), b0+db*rate_b*dt))
        for j0,j1,v0,v1 in product((F(19,10),F(2)),(F(19,10),F(2)),
                                   (F(-1,5),F(1,5)),(F(-1,5),F(1,5))):
            l0=contact(c0,b0,j0,v0)["current"]
            l1=contact(c1,b1,j1,v1)["current"]
            require(l1-l0 <= load_rate*dt+F(13,80), "Current future envelope fails")
            cases += 1
    # A real reconnection starts at c=0 and respects travel, not a binary jump.
    reconnect=[]
    for dt in (F(0),F(100),F(2000),F(600000,11)):
        c=min(F(1),rate_c*dt)
        load=contact(c,F(0),F(2),F(-1,5))["current"]
        require(load <= load_rate*dt+F(1,5), "Reconnection lacks margin")
        reconnect.append(dict(time=dt,conductance_fraction=c,actual_load=load))
    return dict(cases=cases, load_slew=load_rate, retained_slew=F(1,10000),
                arbitrary_residual_variation=True, opening_and_reconnection=reconnect)


def fixed_failures():
    # h is a convex combination of 1,c,1-b,c(1-b), not a reported pose.
    weights=[]
    for a,b,c,d in product(range(5),repeat=4):
        if a+b+c+d<=4:
            weights.append(tuple(F(x,4) for x in (a,b,c,d)))
    count=0
    for w,c,b in product(weights,(F(0),F(1,3),F(1)),(F(0),F(1,2),F(1))):
        h=w[0]+w[1]*c+w[2]*(1-b)+w[3]*c*(1-b)
        derivative_c=w[1]+w[3]*(1-b)
        derivative_b=-(w[2]+w[3]*c)
        require(0<=h<=1 and abs(derivative_c)<=1 and abs(derivative_b)<=1,
                "Fixed passive failure leaves the Lipschitz class")
        count+=1
    return dict(cases=count, coefficient_patterns=len(weights),
                failed_shunt_closed_load=F(2), failed_target_return_promised=False)


def isolation():
    rate=F(11,400000)
    count=0
    for d,k,y0,dt,direction,p0,p1 in product(
            (F(0),F(1,2),F(1)),(F(0),F(1,2),F(1)),
            (F(0),F(1,2),F(1)),(F(0),F(10),F(2000),F(40000)),
            (-1,0,1),(F(0),F(1,10)),(F(0),F(1,10))):
        if d+k>1:
            continue
        y1=min(F(1),max(F(0),y0+direction*rate*dt))
        z0=max(F(0),1-d-k*(1-y0)-p0)
        z1=max(F(0),1-d-k*(1-y1)-p1)
        require(z0-z1 <= rate*dt+F(1,10), "Functional isolation bound fails")
        count+=1
    return dict(cases=count, slew=rate, parasitic_range=[F(0),F(1,10)],
                jump_bound=F(1,10), nominal_full_stop_lower=F(199,200),
                permanent_full_short_isolation=0, new_full_short_covered=False)


def guard_and_bundles():
    geometry=json.loads((HERE/"geometry_results.json").read_text(encoding="utf-8-sig"))
    cert=geometry["guard_jump_certificate"]
    for name,expected in geometry["sources"].items():
        # Geometry includes Git snapshot names; the direct local names can be
        # checked without reinterpreting those immutable snapshot dependencies.
        if (HERE/name).is_file():
            require(source_hash(name)==expected, "Geometry direct source changed: "+name)
    horizon=F(cert["horizon"])
    error=F(1,100)
    load=error+horizon/F(10000)+F(1,5)
    iso=error+F(11,400000)*horizon+F(1,10)
    require(load<F(1,2) and iso<F(9,50), "Stored guard margins fail")
    require(load==F(cert["required_load_margin"]) and iso==F(cert["required_isolation_margin"]),
            "Wrong geometry certificate consumed")
    count=0
    for old in product((F(0),F(1,5),F(1),F(2)),repeat=3):
        for increments in product((F(-2),F(-1),F(0),F(1,5)),repeat=3):
            new=[max(F(0),x+d) for x,d in zip(old,increments)]
            require(max(new)-max(old)<=F(1,5), "Max bundle loses lane envelope")
            count+=1
    # One failed lane may be averaged only if actual load is an additive
    # physical quantity, not a maximum of individually constrained contacts.
    candidate_n=40
    one_failed_lane_jump=F(3,candidate_n)
    candidate_load=error+F(11,120000)*horizon+F(13,80)+one_failed_lane_jump
    require(candidate_load<F(1,2), "Parallel candidate margin fails")
    return dict(horizon=horizon, load_margin_needed=load, isolation_margin_needed=iso,
                load_upper_on_passing_report=F(1,2)+load,
                isolation_lower_on_passing_report=F(49,50)-iso,
                maximum_bundle_cases=count, catalogue=list(NAMES),
                parallel_candidate=dict(lanes=candidate_n,physical_fault_lanes=1,
                    per_lane_absolute_cap=3,required_margin=candidate_load,
                    actual_additive_rating_and_fault_placement_not_constructed=True))


def countercases():
    # Each witness identifies the exact altered premise.
    dt=F(1,1000)
    false_zero_slew_current=contact(F(1),F(0),F(2),F(0))["current"]
    require(false_zero_slew_current>dt/F(10000)+F(1,5), "Reconnect countercase missing")
    isolation_before=F(1)
    isolation_after=F(0)
    require(isolation_before-isolation_after>F(11,400000)*dt+F(1,10),
            "Fresh-short countercase missing")
    source_bypass=contact(F(1),F(0),F(20),F(0))["current"]
    require(source_bypass>F(41,20), "Source bypass countercase missing")
    global_bound=F(1)
    r=5*global_bound
    v=2*r
    require(v>global_bound, "Voltage circularity countercase missing")
    return dict(binary_open_to_loaded_reconnect=dict(dt=dt,before=0,after=2),
                new_shunt_bypass=dict(before=0,after=2,constant_coefficients_violated=True),
                fresh_full_isolation_short=dict(dt=dt,before=1,after=0),
                bypassed_current_source=dict(normal_source_upper=2,actual_source=20,
                                             actual_contact_load=source_bypass),
                self_referential_global_voltage=dict(global_bound=global_bound,R=r,node=v))


def raw_point():
    body=1<<64
    feed=1<<96
    cmin=F(1,1<<32)
    vbody=F(1<<49)
    scale=F(1<<52)
    rating=F(1<<15)
    require(cmin*vbody*vbody/2>=body,"Body energy-voltage upper bound fails")
    require(scale>=5*vbody,"Body terminal too large for residual")
    upper_node=2*scale+vbody
    require(upper_node<1<<54,"Feed node bound fails")
    require(cmin*upper_node**2/2<feed,"Feed node energy exceeds candidate stock")
    power=F(22,5)*rating*scale
    require(power<1<<70,"Power estimate fails")
    return dict(body_hard_stock=body,feed_hard_stock=feed,body_terminal_capacitance_min=cmin,
                body_voltage_bound=vbody,source_voltage_bound=upper_node,
                contact_rating=rating,voltage_scale=scale,source_power_per_loop=power,
                resource_or_fault_admission=False)


def main():
    p=argparse.ArgumentParser()
    group=p.add_mutually_exclusive_group(required=True)
    group.add_argument("--write",action="store_true")
    group.add_argument("--check",action="store_true")
    args=p.parse_args()
    names=("CONDUITS.md","conduit_model.py","PORTS.md","PROBE-MAP.md",
           "GEOMETRY.md","geometry_model.py","geometry_results.json")
    hashes={name:source_hash(name) for name in names}
    result=serial(dict(status="conditional actual-current/isolation adapter; W0 not admitted",
        sources=hashes,algebra=algebra(),temporal=temporal(),fixed_failures=fixed_failures(),
        isolation=isolation(),guard=guard_and_bundles(),countercases=countercases(),
        candidate_raw_point=raw_point()))
    require(hashes=={name:source_hash(name) for name in names},"Sources changed during check")
    dest=HERE/"conduit_results.json"
    if args.write:
        dest.write_text(json.dumps(result,sort_keys=True,indent=2)+"\n",encoding="utf-8")
    else:
        require(json.loads(dest.read_text(encoding="utf-8"))==result,"Record differs; inspect before rewriting")
    print(json.dumps({"status":"passed","algebra_cases":result["algebra"]["cases"],
                      "temporal_cases":result["temporal"]["cases"],
                      "source_admitted":False}))


if __name__=="__main__":
    main()

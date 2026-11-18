"""Exact B floating-reference, current, work and cutoff checks."""

from fractions import Fraction as Q
from hashlib import sha256
from itertools import product
from pathlib import Path
import argparse
import json
import subprocess

HERE = Path(__file__).resolve().parent
OLD = "5c9f261"
LOCAL = "theories-and-designs/byzantine-control/local-control/"


def need(check, reason):
    if not check:
        raise ValueError(reason)


def read(name):
    return json.loads((HERE / name).read_text(encoding="utf-8"))


def old_document(name):
    return subprocess.check_output(["git", "show", OLD + ":" + LOCAL + name], cwd=HERE).decode("utf-8-sig").replace("\r\n", "\n")


def current_cut():
    receiver = read("../local-control/receiver_power_results.json")["bank_current_refinement"]
    ordinary = next(v for v in read("legacy_realization_results.json").values()
                    if isinstance(v, dict) and "ordinary_port_capsules" in v)
    slots = ordinary["ordinary_port_capsules"]
    need(slots == 31138 and ordinary["raw_capture_cells_per_receiver"] == 160, "New B roster")
    Ipriv = 81*(Q(receiver["forward_pole_current_limit"])+Q(receiver["return_pole_current_limit"])+2)
    n = 2**35
    k = 4*40*8192*192
    # Separate near/far ten-pin endpoint shells, plus paired raw rails, private
    # signal bundles and generous externally accessible ordinary slots.
    installed = 20*3*k + 2*16*322240 + 2*81*4096 + 2*slots*1024 + 2**28
    need(installed < n and 16*n < 2**40, "Sleeves or material terminals exceed their allocation")
    j_sleeve = Q(n, 2**24)
    j_other = 4*(slots*2**27 + 2**42) + 2*2**30 + j_sleeve
    need(j_other < 2**45, "Other operating-body current no longer fits")
    j = j_other + Ipriv
    need(j < 2**48, "Total working reference current exceeded")
    raw = Q(read("b_host_flow_results.json")["return_boundary"]["raw_rail_single_end_current_sum"])
    need(raw > 6*2**45 and raw < 2**48, "Misplaced raw-rail cut no longer discriminates")
    hard_per_pair = 2**48*128 + 4*2**48 + 2**52
    hard_per_bank = 2**48*128 + 40*(4*2**48 + 2**52)
    need(hard_per_pair < 2**56 and hard_per_bank < 2**58, "Damaged terminal bound understated")
    return {"hard_pair": hard_per_pair, "hard_bank": hard_per_bank, "functional_shell_pins_upper": installed,"ordinary_external_slots": slots,
            "private_absolute_current": str(Ipriv), "other_absolute_current": str(j_other),
            "headroom_under_2_to_45": str(2**45-j_other), "total_current": str(j),
            "raw_misplacement": str(raw)}


def charge_point(j):
    c_lo, c_hi = Q(2**48), Q(2**49)
    cn, ch = Q(1,2**20), Q(1,2**44)
    c = cn+ch
    z = cn*1001+ch*2**45
    zhard = cn*2**20+ch*2**45
    g_lo, g_hi = Q(2**64,41), Q(2**64,21)
    eps = Q(1,1000)
    ref = (1+c/c_lo)*j/g_lo+2*z/c_lo
    need(ref < eps and Q(2*81,2**42)+Q(2**35,2**64) < cn, "Working charge/voltage floor failed")
    hard_j = Q(2**58)
    # A charged enclosure may lose the soft anchor and acquire a genuine raw rail.
    # The separate hard bipolar housing clamp conducts after one-half volt.
    q_hard_ratio = Q(3,2)
    inside_positive = q_hard_ratio - (q_hard_ratio*c+zhard)/c_lo
    need(inside_positive > 1 and 2**62*(inside_positive-Q(1,2)) > hard_j,
         "Hard charge face has no physical sink")
    need(q_hard_ratio + zhard/c_lo < 2, "Hard charge does not bound the actual plate")
    exponent = g_lo*Q(1,16)/(c_hi+c)
    need(exponent > 49, "Recovery interval too short")
    recovered = (1+c/c_lo)*j/g_lo + 2*zhard/c_lo + 4*Q(1,2**49)
    need(recovered < eps, "Previously charged pad does not recover at the chosen wait")
    # Charges on native/high plates are separate from their differential storage.
    energy = (c_hi*4 + cn*(2+2**20)**2 + ch*(2+2**45)**2)/2
    need(energy < 2**52, "Refundable reference storage undercounted")
    return {"working_r_upper": str(ref), "after_one_sixteenth": str(recovered),
            "hard_reference_energy_upper": str(energy), "hard_charge_ratio": str(q_hard_ratio),
            "working_anchor_heat_upper": str(g_hi*eps**2), "recovery_exponent_lower": str(exponent)}


def weak_path(va, vb, ua, ub, cap_v=Q(0)):
    """Explicit resistor and series RC leakage. va,vb use one gauge; ua,ub use local midpoints."""
    d = va-vb-cap_v
    i0, peak, conductance = Q(1,2**25), Q(1,2**17), Q(1,2**24)
    if not d:
        return Q(0), Q(0)
    mag = min(conductance*abs(d), i0,
              peak/max(1,abs(ua)), peak/max(1,abs(ub)),
              peak/max(1,abs(d)), peak/max(1,abs(cap_v)))
    current = mag if d > 0 else -mag
    return current,d*current


def interface_fixture():
    tests = 0
    for left, right, uraw, ubank, cap in product((Q(-2**30),Q(1,4),Q(3)),
                 (Q(-1),Q(0)), (Q(300),Q(1)), (Q(901),Q(-1)), (Q(-1),Q(0),Q(1))):
        ma,mb=left,right
        va,vb=ma+uraw,mb+ubank
        ia,heat_dc=weak_path(va,vb,uraw,ubank)
        ic,heat_rc=weak_path(va,vb,uraw,ubank,cap)
        i=ia+ic
        # RC plate's own bleed has coefficient 2^-24 and actual finite charge.
        cap_i=ic-Q(1,2**24)*cap
        cap_rate=cap*cap_i
        loss=heat_dc+heat_rc+Q(1,2**24)*cap*cap
        need((uraw-ubank)*i+(ma-mb)*i == loss+cap_rate, "Paired common-mode work has a missing end")
        need(abs(i)<=Q(1,2**24) and abs(uraw*i)<=Q(1,2**16) and abs(ubank*i)<=Q(1,2**16),
             "Leakage cap failed")
        need(not (cap == 1 and cap_i > 0 or cap == -1 and cap_i < 0), "RC plate escaped")
        tests += 1
    # Fixed rated current into a disabled body through a genuine raw fault weld.
    vulnerable = Q(40)*2**40
    need(vulnerable > 2**45 and vulnerable < 2**58, "Weld witness at wrong grade")
    return {"two_ended_cuts":tests,"fault_weld_current":str(vulnerable),
            "one_native_perturbation_settling":str(Q(4,2**64)*2**14)}


def neutral(points, current, loss):
    # Oriented physical capacitor/shunt pairs between consecutive source enclosures.
    n = len(points)
    need(n == len(current) == len(loss) and sum(points) == 0, "Impossible midpoint differences")
    hard_g = Q(2**63)
    cap = Q(2**18)
    outputs = [hard_g*max(0,abs(d)-32)*(1 if d>=0 else -1)+s*d for d,s in zip(points,loss)]
    residual=[a-b for a,b in zip(current,outputs)]
    common=sum(residual)/n
    speeds=[(v-common)/cap for v in residual]
    need(sum(speeds)==0 and sum(d*p for d,p in zip(points,current))==
         sum(cap*d*v+d*y for d,v,y in zip(points,speeds,outputs)),
         "Shield current or conjugate energy failed")
    return common,speeds


def neutral_point():
    g=Q(2**63)
    per_pair=Q(2**56)
    crossed = 2*sum(range(1,21))
    b=crossed*per_pair
    need(crossed==420 and 2*b+g*64/16 < 16*g, "No inward hard face on the physical ring")
    for sign in (-1,1):
        d=[sign*Q(64),sign*Q(-32),sign*Q(-32),Q(0)]
        for raw in (b,-b):
            common, v=neutral(d,[raw,-raw,-raw,raw],[Q(0),g/8,g/8,Q(0)])
            need(sign*v[0]<0 and abs(common)<=b+36*g, "Failed all-mode ring face")
    # Positive electrical leakage from host 0 to 2 removes midpoint charge at 0.
    # Check the combined episode, so that two separately correct conservation equations
    # cannot hide an opposite choice of the endpoint-incidence sign.
    m = [Q(2), Q(-1), Q(1), Q(-2)]
    d = [m[k]-m[(k+1)%4] for k in range(4)]
    uraw, ubank, z = Q(300), Q(1,2), Q(1,4)
    ia, la = weak_path(m[0]+uraw, m[2]+ubank, uraw, ubank)
    ic, lc = weak_path(m[0]+uraw, m[2]+ubank, uraw, ubank, z)
    current = ia+ic
    soft = [Q(1), Q(2), Q(0), Q(1)]
    _,dv = neutral(d, [-current,-current,Q(0),Q(0)], soft)
    neutral_energy_heat = sum(Q(2**18)*x*y + s*x*x for x,y,s in zip(d,dv,soft))
    cap_and_bleed = z*ic
    need(neutral_energy_heat+(ubank-uraw)*current+la+lc+cap_and_bleed == 0,
         "Wrong direction of charge injection into the actual midpoint pair")
    cap_energy=Q(2**18)*64**2/2
    # Heating plus bounded continuing two-ended incidence, counted at both neighboring stations.
    # At |d|<=64 the two bleed paths can draw up to (32+8)g.
    heat=2*64*40*g
    return {"raw_routes_across_link_upper":crossed,"one_edge_energy":str(cap_energy),
            "two_adjacent_exhaust_peak":str(heat),"scaled_inward_margin":str((16*g-2*b-4*g)/g)}


def retirement(j, neutral_bounds):
    old=read("../local-control/port_resource_results.json")["transit"]
    native=read("threshold_field_source_results.json")["point"]["resources"]
    host=read("b_host_flow_results.json")
    on,off,em=map(Q,(old["actual_Eon"],old["actual_Eoff"],old["actual_Emax"]))
    t=Q(native["new_bank_rate"])/2
    refund=Q(2**52)
    ret=Q(old["residual_input_power"])+2**44
    rho=ret+refund/10
    need(rho < off/40 and em+t+refund < 4*off and off+t+refund < on,"Cutoff bridge fails")
    extra_rate=Q(2**44)
    startup=Q(native["startup_margin"])-6*extra_rate-refund
    post=Q(native["post_on_margin"])-6*extra_rate-refund
    need(min(startup,post)>0 and Q(native["new_bank_rate"])>10*extra_rate,
         "Larger reversible reference load is not supported")
    capacity=2*refund+2*Q(neutral_bounds["one_edge_energy"])
    remaining=Q(host["paid_trigger"]["after_capacity_voltage_floor_slack"])-Q(3,4)*capacity-4*extra_rate
    need(remaining>0,"Reference hardware erased raw U voltage")
    zone=Q(host["paid_trigger"]["all_mode_bath_margin_after_slot_terminals"])
    # Two bank hard clamps and pad returns plus both adjacent neutral enclosures and all
    # added damage strands, and a conservative allowance for frame power at the 20-hop source interface.
    allocated = 4*41*(2*(2**65+2**64)+Q(neutral_bounds["two_adjacent_exhaust_peak"])
                      +2**48*2**30 + 40*1280*2**56 + 40*4*900*2**48)
    reaction = Q(host["paid_trigger"]["remaining_reaction"])-Q(41*(16*2**35+8),2**62)
    tmax = Q(native["new_bank_rate"])/2
    need(reaction>0 and 4*tmax/2**30 < 2**30 and 2**60 + 2*em*2**27 < 2**90,
         "New mount force, carrier voltage or supply current out of bounds")
    need(zone>allocated and 2*extra_rate < Q(read("world_channel_results.json")["source"]["remaining_supply_rate"]),
         "Reference bills exceed the changed host")
    return {"remaining_mechanical_reaction":str(reaction), "Fmax_over_off":str((em+t+refund)/off),"fourfold_rho_over_kEoff":str(40*rho/off),
            "low_sample_to_rearm_margin":str(on-off-t-refund),"six_q_startup_margin":str(startup),
            "post_on_margin":str(post),"U_working_quarter_margin":str(remaining),
            "remaining_zone_work_margin":str(zone-allocated),"added_capacity":str(capacity)}


def main():
    curr=current_cut()
    j=Q(curr["total_current"])
    bus=neutral_point()
    files=("B-REFERENCE-RETURN.md","b_reference_return.py","B-HOST-FLOW.md","b_host_flow_results.json",
           "LEGACY-REALIZATION.md","PRIVATE-COMPARISON.md","../local-control/RECEIVER-POWER.md",
           "../local-control/HARD-BOUNDARY.md","../local-control/receiver_power_results.json",
           "../local-control/port_resource_results.json","threshold_field_source_results.json")
    return {"local_sha256_lf":{f:sha256((HERE/f).read_text(encoding="utf-8").encode()).hexdigest() for f in files},
            "historical_current_cut":{f:sha256(old_document(f).encode()).hexdigest()
                                      for f in ("CURRENT-CUT.md","current_cut_model.py","current_cut_results.json")},
            "working_cut":curr,"charge":charge_point(j),"physical_pairs":interface_fixture(),
            "midpoints":bus,"retirement":retirement(j,bus)}


if __name__ == "__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write",action="store_true")
    result=main()
    path=HERE/"b_reference_return_results.json"
    if parser.parse_args().write:
        path.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n",encoding="utf-8")
    else:
        need(result==json.loads(path.read_text(encoding="utf-8")),"Stale B reference result")
    print("Checked B floating charge, nonzero two-ended return, damaged weld, heat and cutoff.")

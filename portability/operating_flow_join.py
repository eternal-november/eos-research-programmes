"""Check the operating-bank flow lemma's exact separating examples and B parameters."""
import json
import sys
from fractions import Fraction as Q
from pathlib import Path

from shared_bank_charging import log_bounds


HERE = Path(__file__).resolve().parent


def hard_store(stock, capacity, net):
    """The upper-stop port receives actual surplus. Test the real zero face."""
    if not 0 <= stock <= capacity or (stock == 0 and net < 0):
        raise ValueError("The supplied physical port leaves the stock domain")
    spill = max(0, net) if stock == capacity else 0
    return net - spill, spill


def can_restart_from_empty():
    # d=2, Tcap=1, P_T=41/10, eta=1/2, E(0)=T(0)=0.
    # At t=log(2)/lambda: T=1/2. E solves E'+lambda*E=4T.
    # Coefficients (a,b) below represent a+b*log(2).
    lam = Q(41, 10)
    U_debit = (Q(0), Q(2))
    convert_heat = (Q(0), Q(1))
    transit = (Q(1, 2), Q(0))
    transit_bleed = (-Q(1, 20) / lam, Q(1, 10) / lam)
    E = (2 / lam, -2 / lam)
    availability = (-4 / lam**2, 6 / lam**2)
    # A physical unit-rate free slot receives A. Other generic routes receive (lambda-1) A.
    goods = (transit, transit_bleed, convert_heat, E, availability,
             tuple((lam - 1) * a for a in availability))
    assert tuple(sum(z[k] for z in goods) for k in (0, 1)) == U_debit
    lo, hi = log_bounds(2, Q(1, 10**9))
    assert 0 < E[0] + E[1] * hi <= E[0] + E[1] * lo < 1
    assert 0 < availability[0] + availability[1] * lo
    # E'(s)=4 lambda*s*exp(-lambda*s)>=0 on this arc, so E<1 throughout.
    return "empty connected bank and transit recover jointly"


def saturation_and_release():
    # Constant funded T=1 with 4T=4, actual E at its upper stop=10.
    # Each of two independent cells reaches 1/2 after 1/2 at rate 1.
    def full_bank(time, active):
        derivative, spill = hard_store(10, 10, 4 - 1 - sum(active))
        assert derivative == 0
        credits = tuple(time * r for r in active)
        assert 4 * time == sum(credits) + time + spill * time
        return credits, spill

    credits, spill = full_bank(Q(1, 2), (1, 1))
    assert credits == (Q(1, 2), Q(1, 2)) and spill == 1
    # Both caps stop drawing. One funded local parcel has now spent 1/4 in
    # its own cell. Its old reservation inhibits refill until it is released.
    assert full_bank(Q(1, 4), (0, 0)) == ((0, 0), 3)
    refill, spill = full_bank(Q(1, 4), (1, 0))
    assert refill == (Q(1, 4), 0) and spill == 2
    assert full_bank(Q(1, 4), (0, 0)) == ((0, 0), 3)
    # Failure of independent reflected projections as an accounting model:
    # with all cells full, leaving the old nominal E debits burns 2/q with no destination.
    _, wrong_dump = hard_store(10, 10, 4 - 1 - 2)
    actual_other_draw = 1
    delivered_to_full_cells = 0
    missing_export = 4 - actual_other_draw - delivered_to_full_cells - wrong_dump
    assert missing_export == 2
    # At physically rerouted P_T=5 the true T upper-stop surplus is 9/10.
    assert hard_store(1, 1, 5 - Q(41, 10)) == (0, Q(9, 10))
    try:
        hard_store(0, 10, -1)
    except ValueError:
        pass
    else:
        raise AssertionError("A negative empty-bank drift was supplied by reflection")
    return "two tied caps, inhibited debit, later recharge, upper spill and empty-face failure"


def b_comparisons():
    def read(name):
        return json.loads((HERE / name).read_text(encoding="utf-8-sig"))

    inventory = read("legacy_realization_results.json")["inventory"]
    thresholds = read("../local-control/port_resource_results.json")["transit"]
    d = Q(inventory["retained_downrated_bank_allowance"])
    e_max = Q(thresholds["actual_Emax"])
    e_on = Q(thresholds["actual_Eon"])
    e_off = Q(thresholds["actual_Eoff"])
    assert e_max == Q(read("parent_realization_results.json")["cost_bounds"]["actual_bank_capacity"])
    actual_parent_bank = Q(read("parent_retirement_results.json")["resources"]["updated_actual_bank_rate"])
    native = read("native_clock_source_results.json")["scarcity"]
    native_rate = Q(native["aggregate_rate"])
    assert native_rate <= actual_parent_bank <= d
    t_cap = d / 2
    assert e_max + t_cap < 4 * e_off and e_off + t_cap < e_on
    assert 1 + 2 * e_max / d < 21
    delta = Q(1, 2**30)
    # Under actual inward/zero backfeed, at most .1E additional bleed and all
    # generic E draws in d, the worst lower bound for this short held interval.
    floor = e_off - (d + e_max / 10) * 2 * delta
    assert floor > 1
    # Isolated E can increase while F=E+T decreases. All consumers disabled.
    t = Q(1)
    e = Q(0)
    dE, dump_E = hard_store(e, e_max, 4 * t - e / 10)
    dT, dump_T = hard_store(t, t_cap, -Q(41, 10) * t)
    assert dE > 0 and dump_E == dump_T == 0 and dE + dT == -(e + t) / 10
    return f"B conditional two-delta E floor {floor}, no-rearm margin {e_on-e_off-t_cap}"


if __name__ == "__main__":
    if sys.version_info[:2] != (3, 12) or not __debug__:
        raise SystemExit("Use unoptimized Python 3.12")
    print(can_restart_from_empty())
    print(saturation_and_release())
    print(b_comparisons())

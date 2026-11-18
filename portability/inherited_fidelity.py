"""Check the pinned arithmetic and source-contract cross references in the fidelity review."""

from fractions import Fraction as Q
from hashlib import sha256
from math import ceil, floor
from pathlib import Path, PurePosixPath
from posixpath import normpath
import json
import re
import subprocess

HERE = Path(__file__).resolve().parent
SOURCE = "theories-and-designs/byzantine-control/portability"
REVIEWED = "522eb12c0731193050735adb6b7d5d75da286bf0"
INSTALLATION = "f08190a108fd02eddc6bc377cfaeff644dba20ec"
CUTS = "c81e6b8242ac797133203077ec29feba68cb8414"
LATER_VISIT = "65913f166973039d0f96eaeb8e7fd80fa8565870"
SCIENCE = "56c4cff67e8d36c88f6b7a51c68d0f4af861cf03"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def receipt(revision, name):
    value = subprocess.check_output(
        ["git", "show", f"{revision}:{SOURCE}/{name}"], cwd=HERE
    )
    return json.loads(value)


def contract_coverage():
    audit = (HERE / "INHERITED-FIDELITY.md").read_text(encoding="utf-8-sig")
    source = (HERE.parent / "FAULT-COVERAGE.md").read_text(encoding="utf-8-sig")
    required = re.findall(r"^\| (M\d\d) \|[^|\n]+\| ([PJTBA,]+);", source, re.M)
    seen = re.findall(r"^\| (M\d\d) [^|]+\| ([PJTBA,]+) \|", audit, re.M)
    require(len(required) == len(seen) == 45, "incomplete or duplicated fault coverage")
    require(required == seen, "a source family or its required modes changed")
    chains = re.findall(r"^\| (\d+) \|", audit, re.M)
    require(list(map(int, chains)) == list(range(1, 19)), "chain missing or reordered")
    for family, count, width in [("BC", 7, 1), ("RN", 5, 1), ("IA", 4, 1),
                                  ("AC", 6, 1), ("A", 18, 2), ("C", 10, 2)]:
        actual = re.findall(rf"^\| ({family}\d+)(?: |\|)", audit, re.M)
        expected = [f"{family}{i:0{width}d}" for i in range(1, count + 1)]
        require(actual == expected, f"{family} obligations missing or duplicated")
    for relative in re.findall(r"\]\(([^)]+)\)", audit):
        if (HERE / relative).is_file():
            continue
        # The audit branch can predate a reviewed source file on the integration branch.
        target = normpath(str(PurePosixPath(SOURCE) / relative))
        subprocess.run(["git", "cat-file", "-e", f"{SCIENCE}:{target}"], cwd=HERE, check=True)


def support_and_service(cuts):
    rate = Q(1, 104548602495950)
    a_horizon = 10456118540836
    a_job = Q(5347794885226509, 1048576)
    b_horizon = 2 * 10**13
    b_job = Q(cuts["inequalities"]["supplier_window"])
    for horizon, job in [(a_horizon, a_job), (b_horizon, b_job)]:
        require(1 + 2 + floor(3 + rate * (2 * horizon + 2 * job)) == 6,
                "planning envelope changed")
    # Each copy of the same pair retains the original two physical origins.
    footprints = [6] + [6 - pair_hits + 2 for pair_hits in range(1, 7)]
    require(max(footprints) == cuts["incidence"]["attained_raw_slots"] == 7,
            "fixed-pair input reach or quorum changed")
    require(15 - max(footprints) == 8 and 4 + 2 * 2 == 5 + 3 == 8,
            "alternate physical layouts should lose the genuine-vote implication")
    bounds = cuts["inequalities"]
    require(Q(bounds["upper_collar_actual_min"]) > Q(".74"), "upper collar")
    require(Q(bounds["lower_collar_actual_max"]) < Q(".46"), "lower collar")
    require(Q(bounds["service_min"]) > Q(".1"), "actuator service")
    rise = Q(".61") + Q(".6") - 1 - Q(".10") - Q(".02")
    require(rise == Q(".09") and (Q(".65") - Q(".60")) / rise == Q(5, 9),
            "increased independent-inlet capacity boundary")


def final_contact_and_current(installation, cuts):
    contact = installation["contact"]
    effect_age = Q(cuts["inequalities"]["protected_factual_horizon"])
    require(effect_age == Q(contact["effect_age"]), "incompatible guard ages")
    drift = (2**20 + 22 * Q(311296891, 2000)) / (128 * Q(2**29))
    force = Q(3, 2) * (Q(".5") + Q(".01"))
    force += drift * effect_age + Q(contact["known_parallel_force"]) / 128
    require(force == Q(contact["full_contact_upper"]) < Q(".801"), "full blade load")
    deficit = Q(".02") + Q(".01") + Q(".1") + 11 * effect_age / 400000
    require(deficit == Q(contact["nominal_clearance_deficit"]) < Q(".146"),
            "clearance over the entire effect interval")
    require(80 * Q("2.2") / 128 == Q(contact["parallel_coil_mount_countercase"]) > 1,
            "alternative mounting no longer separates the factual claims")
    budget = installation["budget"]
    joined = cuts["installed_faces"]
    subtotal = Q(budget["nonprivate_current_upper"])
    private = Q(joined["installed_private_current"])
    total = subtotal + private
    require(total == Q(joined["installed_total_current"]) == Q(budget["total_current_including_private"]),
            "private poles missing from total current")
    require(subtotal < 2**45 < total < 2**48, "working current grades conflated")
    require(2**48 - total == Q(joined["installed_total_slack_to_2_to_48"]), "full-current grade")
    headroom = 2**45 - subtotal
    preliminary = Q(cuts["circuit_and_cue"]["earlier_reference_only_nonprivate_current_headroom"])
    require(headroom == Q(budget["nonprivate_slack_to_2_to_45"]) > 872 * 10**9, "co-installed headroom")
    require(340 < preliminary - headroom < 341, "historical current discrepancy changed")


def material_and_roster(installation, cuts):
    raw = installation["raw_paths"]
    shunt = Q(1, 2**17)
    leakage = Q(1, 2**20)
    require(shunt - leakage == Q(7, 2**20), "unpowered bit face must point inward")
    require(Q(1, 2**14) - shunt - leakage == Q(55, 2**20), "signed powered settling")
    require(4096 * shunt == Q(raw["additional_terminal_shunt_load"]) == Q(1, 32), "shunt heat")
    high = Q(raw["initial_high_work_margin"]) - Q(1, 16) - Q(1, 32)
    cold = Q(raw["initial_cold_current_margin"]) - Q(1, 4096) - Q(1, 32 * 99)
    require(high == Q(raw["remaining_high_work_margin"]) > Q(".7715"), "high-band work")
    require(cold == Q(raw["remaining_cold_current_margin"]) > Q(".0117"), "cold current")
    flex = installation["flexures"]
    require(0 < Q(flex["total_host_elastic_store"]) < 1, "absolute guide storage")
    require(Q(flex["completed_route_work"]) > 0 and Q(flex["completed_route_heat"]) > 0,
            "routed fixture should retain its dissipative physical history")
    local = cuts["regional_staffing"]
    require(local["receiving_bag_columns"] == 3 and local["straddling_footprint_retained"],
            "regional reach must include straddling physical effects")
    require(local["simultaneous_centers_on_checked_ladders"] > 6,
            "a global six-center cap would reject the exhibited history")
    cohort = 12 * (6 + 2**98) + 2
    require(cuts["circuit_and_cue"]["participating_incarnations_per_region"] == 2 * cohort,
            "census must cover the physical two-bank roster")


def spatial_history(spatial, cuts):
    horizon = Q(spatial["H"])
    period = Q(spatial["period"])
    onset_window = 2 * horizon
    last_release_tail = 1100
    quiet_after_release = period - onset_window - last_release_tail
    both_orientations = Q(cuts["circuit_and_cue"]["both_oriented_phase_two_by"])
    extra_half_upper = Q(cuts["inequalities"]["partial_orbit_and_two_postrelease_sweeps"])
    require(both_orientations + extra_half_upper < onset_window < quiet_after_release < 40 * horizon,
            "actual quiet separation no longer funds the alternate cue")
    cue = cuts["circuit_and_cue"]
    require(quiet_after_release == Q(cue["between_blocks_release_clearance"]), "post-release quiet")
    require(Q(cue["return_including_wait"]) < 340346 * 10**6, "useful return including reference wait")
    require(Q(cue["phase_two_work_contact_by"]) < onset_window, "actual later working cue")
    bins = ceil(onset_window / 140)
    require(bins == spatial["maximum_time_bins"], "time bin count")
    require(Q(1, 18 * bins) == Q(spatial["simultaneous_fraction"]), "simultaneous fraction")
    require(Q(3, 20 * period) == Q(spatial["average_fresh_exposure_density"]), "local density")
    weighted_output = Q(789, 800) * Q(-1, 2) + Q(11, 800)
    require(weighted_output == Q(spatial["adverse_weighted_host_output_upper"]), "actual impairment")
    require(490 - 210 - 140 == spatial["physical_effect_lower"], "common duration")


def later_visit(installation, cuts):
    name = "b_phase_ten_history_results.json"
    witness = receipt(LATER_VISIT, name)
    data = witness["cost"]
    bindings = witness["bindings"]
    require(bindings["flexure"] == INSTALLATION and bindings["programme"].startswith("1be94c7"),
            "fork belongs to a different material or programme")
    old_cuts = receipt(bindings["cut"], "b_cut_induction_results.json")
    require(old_cuts["inequalities"] == cuts["inequalities"], "earlier-cut timing or load changed")
    old_lead = receipt(bindings["lead"], "b_lead_installation_results.json")
    require(Q(old_lead["contact"]["known_parallel_force"]) == Q(data["mount_force"])
            == Q(installation["contact"]["known_parallel_force"]), "changed physical force")
    body = subprocess.check_output(["git", "show", f"{LATER_VISIT}:{SOURCE}/b_phase_ten_history.py"], cwd=HERE)
    require(sha256(body.replace(bytes([13, 10]), bytes([10]))).hexdigest()
            == witness["implementation_sha256"], "later-visit executable identity")
    tau = 2**29
    drift = Q(".01") + Q("4.2") + 64 * 261
    delta_q = drift * 11 * Q(cuts["inequalities"]["qualified_frame"][1]) / tau
    effect = Q(installation["contact"]["effect_age"])
    mount = Q(data["mount_force"]) / 128
    spread = Q(data["spring_spread"])
    high = (132 - delta_q - drift * effect / tau) / 128 - mount
    low = Q(11, 16) + spread + drift * effect / (Q(3, 2) * tau * 128) + mount
    require(low == Q(data["low_load_upper"]) < Q(".687695") < 1, "low branch physical bound")
    require(high == Q(data["high_load_lower"]) > Q("1.031114") > 1, "high branch physical bound")
    q_lo, q_hi = map(Q, data["q_over_tau_at_branch"])
    debit_lo, debit_hi = map(Q, data["paid_jump_work"])
    require(debit_lo == q_lo**2 * tau / 6 <= debit_hi == q_hi**2 * tau / 6,
            "branch jump must retain q and pay its actual work")
    readings = list(map(Q, data["quantizer_input"]))
    require(Q(".6875") < readings[0] <= readings[1] < Q(".6885"), "genuine 688 bin")
    require(1000 - 1000 * Q(data["working_gap"]) == 5, "retiring clearance deficit")
    require(Q(data["head_change_delay_margin"]) > Q(".1028"), "post-change visibility")
    require(2000 < Q(data["crossing_elapsed"][0]) < Q(data["crossing_elapsed"][1])
            < 25_000_000, "braking interval before the attained cut")
    require(Q(data["whole_incumbent_window"]) < Q(data["watchdog_window"])
            and data["frame_decrements_upper"] < 2_400_000_000, "physical lease and watchdog")
    require(Q(data["positive_action_after_clear"]) < 294, "post-clear action suffix")
    steps = {item["cut"]: item for item in witness["visits"]["steps"]}
    require(steps["phase 10 entry"]["remaining_wait"] == 2100, "actual stage wait")
    for label, port in [("phase 10 mature, both retracted", 3), ("isolation seated", 4),
                        ("later 688 read", 0), ("still eligible after complete clearance", 5)]:
        require(steps[label]["command"][5] == port, f"source control port differs at {label}")
    providers = witness["visits"]["substitution_receipts"]
    require(len({r["provider"] for r in providers}) == 15 and sum(r["calls"] for r in providers) == 98,
            "paid ordinary publisher evidence changed")


def matched_comparison():
    receipt_data = receipt(SCIENCE, "current_publication_comparison_results.json")
    forward, selected = receipt_data["arms"]
    core = 1938 * 20480
    harness = 2 * 20480
    require(core == receipt_data["actual_fanout_parents_work"] and harness == Q(receipt_data["extra_harness_return_parcels"]),
            "source and harness parent work differ")
    for arm in (forward, selected):
        require(arm["producer_retirements"] == 1938 and arm["requested_source_uses"] == 160,
                "different executing parents or raw offers")
        require(Q(arm["parent_work_since_frame"]) == core + harness, "unattributed parent work")
    children = forward["physical_DATA"] - selected["physical_DATA"]
    wire = Q(forward["wire_work"]) - Q(selected["wire_work"])
    cpu = Q(forward["source_processing"]) - Q(selected["source_processing"])
    require(children == 94 and 4 * children == forward["symbols"] - selected["symbols"],
            "different installed incidence or tagged transport")
    require(wire == 48128 and cpu + wire == 4096 * children == 385024, "double-counted signal work")
    require(Q(forward["bank_work_since_frame"]) - Q(selected["bank_work_since_frame"]) == wire + cpu,
            "source supply difference")
    burden = subprocess.check_output(["git", "show", f"{SCIENCE}:{SOURCE}/REPEATED-PROOF-BURDEN.md"], cwd=HERE)
    digest = sha256(burden.replace(bytes([13, 10]), bytes([10]))).hexdigest()
    require(digest == receipt_data["inputs"]["REPEATED-PROOF-BURDEN.md"]
            == "3e8000bf2fc51bbd698efea0a52a3f08b8424b0bac89ee02444f8bc4ea21c2f1",
            "different scientific comparator")
    require(receipt(LATER_VISIT, "b_phase_ten_history_results.json")
            == receipt(SCIENCE, "b_phase_ten_history_results.json"), "integrated RP3 receipt changed")


def main():
    installation = receipt(INSTALLATION, "b_lead_installation_results.json")
    cuts = receipt(CUTS, "b_cut_induction_results.json")
    spatial = receipt(REVIEWED, "spatial_coverage_results.json")
    integrated = receipt(REVIEWED, "b_lead_installation_results.json")
    old_links = installation.pop("join_sha256_lf")
    new_links = integrated.pop("join_sha256_lf")
    require(installation == integrated, "integrated material calculation differs")
    rebound = {"b_host_flow_results.json", "b_reference_return_results.json"}
    require(old_links.keys() == new_links.keys(), "integration changed the material source roster")
    require({name for name in old_links if old_links[name] != new_links[name]} == rebound,
            "unexpected physical dependency rebinding")
    for rev, bindings in [(INSTALLATION, old_links), (REVIEWED, new_links)]:
        for name, digest in bindings.items():
            content = subprocess.check_output(["git", "show", f"{rev}:{SOURCE}/{name}"], cwd=HERE)
            require(sha256(content.replace(bytes([13, 10]), bytes([10]))).hexdigest() == digest,
                    f"material source binding mismatch at {rev} for {name}")
    require(cuts == receipt(REVIEWED, "b_cut_induction_results.json"), "integrated prefix proof differs")
    require(cuts["installed_faces"]["material"] == INSTALLATION, "physical installation mismatch")
    contract_coverage()
    support_and_service(cuts)
    final_contact_and_current(installation, cuts)
    material_and_roster(installation, cuts)
    spatial_history(spatial, cuts)
    later_visit(installation, cuts)
    matched_comparison()
    print("Checked source-mode register, links, support, service, guard, current, spatial, later-visit and matched-parent/child bounds.")
    print("Physical identifications and inhabited source histories require their separate proofs.")


if __name__ == "__main__":
    main()

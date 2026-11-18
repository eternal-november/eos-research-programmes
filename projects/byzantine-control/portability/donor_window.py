"""Check the strict formation/overlap and post-WARM distances on both source points."""
import json
import subprocess
from fractions import Fraction as Q
from pathlib import Path


HERE = Path(__file__).resolve().parent
BASE = "003d9e7f92874ff32ce405eaea788f7bff82f0fa"
PREFIX = "theories-and-designs/byzantine-control/"


def record(path):
    blob = subprocess.check_output(["git", "show", BASE + ":" + PREFIX + path], cwd=HERE)
    return json.loads(blob)


def check_family(name, timer, phases, speed, warm, driver, setup, commission, expected):
    job = Q(timer["private_job_window"])
    sample = Q(timer["sample_wait"])
    span = (warm-driver)/speed
    overlap = span-setup
    assert speed > 0 and warm > driver > 0 and overlap == Q(timer["whole_bank_overlap"])
    seed_margin = warm/speed - commission - job
    sponsor_margin = overlap-job
    # From the coherent WARM sample used at the stage-8 stop, conservatively
    # pay the remaining cam movement, both intervening phases and sample edges.
    costs = {int(key.split("_")[0]): Q(value) for key, value in phases.items()}
    post = sample + costs[9] + costs[10] + 3*(Q(timer["nominal_band_upper"])+sample)
    physical_clearance = warm-driver-speed*post
    assert (sponsor_margin, seed_margin, post) == expected
    assert sponsor_margin > 0 and seed_margin > 0 and physical_clearance > 0
    print(f"{name}: handoff slack {sponsor_margin}q; seed slack {seed_margin}q; "
          f"minimum ACT clearance above DRIVER after WARM {physical_clearance}")


def main():
    orbit = record("portability/normal_orbit_results.json")
    primary = record("local-control/geometry_results.json")
    p = dict(primary["design"]["physical_parameters"])
    a = primary["geometry"]
    phase_a = record("local-control/port_source_results.json")["return_schedule"]["phase_bounds"]
    speed = Q("11/10")
    check_family("A-prime",orbit["primary_timer"],phase_a,speed,
                 Q(p["WARM_AT"]),Q(a["driver_at"]),Q(a["post_driver_information"]),
                 Q(primary["timing"]["commissioning"]),
                 (Q(418475203948401,11534336),Q(8282543545708401,11534336),Q(9908050854382639,39321600)))
    b = record("portability/threshold_geometry_results.json")["arithmetic"]
    k = b["physical_inputs"]
    boot = record("portability/threshold_initialization_results.json")["bootstrap"]
    check_family("B",orbit["B_sampled_candidate"]["timer"],b["phase_bounds"],Q(k["stroke_max"]),
                 Q(k["warm_at"]),Q(k["vector_driver_at"]),Q(b["vectors"]["first_after_route_engagement"]),
                 Q(boot["all_role_commissioning"]),
                 (Q(b["geometry"]["timer_overlap_slack"]),Q(boot["initial_whole_job_slack"]),Q(9908323912729039,39321600)))
    assert Q(b["geometry"]["overlap_after_recounting_preparation"]) == Q(90344349770919305,738197504) > 122_000_000


if __name__ == "__main__":
    main()

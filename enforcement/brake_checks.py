"""Exact arithmetic checks for BRAKE-PROOFS.md, not unbounded model checking."""
from fractions import Fraction as F
import json


def envelope(a, torque, depth, value):
    for _ in range(depth):
        value = a * value + torque
    return value


def speed(x, u, engagement, strength=1):
    return max(0, (5 * x + 10 * u - 10 * strength * engagement) // 10)


def heat(h, engagement, x, strength=1):
    return (5 * h + strength * engagement * x) // 10


def main():
    regimes = {
        "real_identity": dict(c=F(1, 10), normal=F(4, 5), maximum=F(13, 10),
                              strength=F(1, 5), low=F(1), high=F(10), threshold=F(41, 5),
                              error=F(1, 10), authorization=F(6), beta=F(9, 10),
                              kappa=F(1, 10), thermal=F(6), m=3, faulty=1, delay=1),
        "integer_floor_adapter": dict(c=F(1, 2), normal=F(4), maximum=F(6),
                                      strength=F(1), low=F(1), high=F(10), threshold=F(3),
                                      error=F(1), authorization=F(2), beta=F(1, 2),
                                      kappa=F(1, 10), thermal=F(6), m=3, faulty=1, delay=1),
    }
    results = {}
    for name, p in regimes.items():
        a = 1 - p["c"]
        lower = a * p["low"] + p["normal"] - p["strength"] * p["m"]
        upper = a * p["high"] + p["maximum"] - p["strength"] * (p["m"] - p["faulty"])
        delayed = envelope(a, p["maximum"], p["delay"] + 1, p["threshold"] + p["error"])
        thermal = p["beta"] * p["thermal"] + p["kappa"] * p["strength"] * p["m"] * p["high"]
        assert lower >= p["low"]
        assert upper <= p["high"]
        assert delayed <= p["high"]
        assert thermal <= p["thermal"]
        assert p["threshold"] - p["error"] >= p["authorization"]
        assert 0 <= p["threshold"] + p["error"] <= p["maximum"] / p["c"]
        assert p["low"] <= p["threshold"] + p["error"]
        results[name] = {"lower_update": str(lower), "all_good_on_upper_update": str(upper),
                         "delayed_unbraked_bound": str(delayed), "thermal_upper_update": str(thermal),
                         "factive_sample_lower_bound": str(p["threshold"] - p["error"]),
                         "fixed_authorization": str(p["authorization"])}
    trajectory = [4]
    for _ in range(3):
        trajectory.append(speed(trajectory[-1], 6, 0))
    assert trajectory == [4, 8, 10, 11]
    assert speed(10, 6, 2) == 9
    # OFF startup; exact epoch-zero source values 4 generate ON for epoch one.
    x1, h1 = speed(4, 6, 0, strength=3), heat(6, 0, 4, strength=3)
    x2, h2 = speed(x1, 6, 3, strength=3), heat(h1, 3, x1, strength=3)
    assert (x1, h1, x2, h2) == (8, 3, 1, 8)
    assert h2 > 6
    results["integer_witnesses"] = {"brake_ablation": trajectory,
                                    "same_input_with_two_brakes": 9,
                                    "strong_brake_off_startup_trajectory": [[4, 6], [x1, h1], [x2, h2]]}
    shared_heat = (5 * 3 + 3 * 8 + 3 * 8 + 3 * 6) // 10
    assert shared_heat == 8 > 6
    results["integer_witnesses"]["naive_shared_heat_composition"] = shared_heat
    print(json.dumps(results, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()

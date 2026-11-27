# Fixed sensing stations and post-capture delay

[Capture_And_Receipt.tex](Capture_And_Receipt.tex) separates reaching a
station, capturing the fixed observation, and receiving it. The mobile
robot can prepare both branches after a stationary capture without waiting
at the station. The exact three-cut condition holds for explicitly bounded
near sites; a farther site separates it from the two scalar tests.

Run python3 -B replay.py and compare stdout with expected.json. The
replay uses exact rational checks and all extrema of the tested paths.
The sensing and reporting premises are modeled, not source-observed.

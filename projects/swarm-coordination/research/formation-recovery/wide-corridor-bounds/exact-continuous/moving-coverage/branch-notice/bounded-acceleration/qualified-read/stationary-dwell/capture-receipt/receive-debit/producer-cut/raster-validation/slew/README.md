# Two-view qualification with a charged slew

[Two_Ray_Slew_Budget.tex](Two_Ray_Slew_Budget.tex) gives the exact open
apertures and a strict travel lower bound. The two-camera-angle proposal
is valuable only if both shorter exposures, settling, and the slew fit.
The original longer dwell contract would not fit twice.

Build the parent raster-validation inputs via the parent's run.sh.
At the parent root run python3 -B slew/yaw_budget.py and compare stdout
to slew/expected.json. The Space package contains the exact parent ZIP.

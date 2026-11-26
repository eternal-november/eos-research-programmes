# How far must the formation move to learn its gap?

The [active measurement proof](Travel_Cost_Of_Seeing_The_Gap.tex) replaces the [ideal gap bit](../README.md) with a deliberately simple range detector. For a detection range shortfall \(d\), choosing the motion and read time costs exactly \(\sqrt{3d/2}\) advance in the stated small-shortfall regime. The robots cannot reach the oracle's target by treating the measurement as free.

At the named shortfall the three closest comparators are 3.575 with an ideal timely bit, 3.5 with a physical approach and an ideal range reading, and 3.4 with no usable bit. The same initial approach can still reach 3.4 safely if the reading is lost. This is a distinct lower service level, not a way to meet the original target after loss.

Run with Python 3 and SciPy:

    python3 replay.py > actual.json
    diff -u results.json actual.json

The exact arithmetic checks physical bounds between knots. The LP is an independent sampled comparison. [Lean](SensingLoss.lean) checks the real inequality and the rational named optimum, not the vehicle dynamics. No camera, real radio, or deployed controller is tested.

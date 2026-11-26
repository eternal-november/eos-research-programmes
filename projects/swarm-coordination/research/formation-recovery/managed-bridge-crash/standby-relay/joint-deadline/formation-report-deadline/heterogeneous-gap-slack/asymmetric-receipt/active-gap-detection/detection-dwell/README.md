# A detector that needs time changes the best approach

The [proof](Required_Detection_Dwell.tex) extends the [point-sample study](../README.md). It requires continuous visibility over a chosen interval of duration \(h\). For a range shortfall \(d\) in the stated small-dwell regime, the exact travel loss grows from \(\sqrt{3d/2}\) to \(\sqrt{3d/2+9h^2/16}\). The best shared prefix reaches the detection threshold at both ends of the observation window and goes farther inside the range between them. Past the derived dwell threshold, the window instead starts as soon as detection is geometrically possible. A missing result still has a safe, explicitly lower service fallback.

Run with Python 3 and SciPy:

    python3 replay.py > actual.json
    diff -u results.json actual.json

The motion replay checks the continuous bounds with rational arithmetic and compares an independent sampled trajectory optimization. The visibility law is hypothetical; this is not an optical hardware test or a general statement about dwell costs.

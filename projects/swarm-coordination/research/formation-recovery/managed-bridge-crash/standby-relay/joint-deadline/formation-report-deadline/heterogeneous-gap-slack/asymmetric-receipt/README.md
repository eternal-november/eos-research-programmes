# Different clearance margins change when the gap report is needed

The [proof](Asymmetric_Gap_And_Receipt.tex) gives the exact advance under an asymmetric clearance and link band with crossed actuator limits. It extends the [symmetric case](../README.md). Then it fixes a physical band, makes the initial gap unknown to the controller, and proves the latest receipt time for one bit. At the critical time the robots are already moving under a common prefix. The two cases use the same target and deadline, but without the report they cannot reach the target.

The replay verifies the continuous gap extrema with exact algebra and compares a direct sampled shared-prefix trajectory optimizer. [Compositional collision and connectivity barriers](https://liwanggt.github.io/files/B5_Composable_Barrier.pdf) provide a safety comparator; they are not benchmarked here. No real sensor supplies the bit in the fixture.

With Python 3, SymPy and SciPy:

    python3 replay.py > actual.json
    diff -u results.json actual.json

[Lean](GapReceiptCut.lean) checks the algebraic peak and exact cutoff implication over the reals. The dynamics and construction are established by the proof and exact trajectory replay, not by the Lean file.

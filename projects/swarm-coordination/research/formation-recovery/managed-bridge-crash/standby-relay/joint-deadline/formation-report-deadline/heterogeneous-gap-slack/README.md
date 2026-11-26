# How gap slack offsets mismatched actuation

The [proof](Gap_Slack_With_Different_Actuators.tex) gives an exact travel limit for two robots with different speed and acceleration bottlenecks. It preserves a positive gap band continuously. In the worked model, exact lockstep allows distance 3; a half-width of 0.1 raises that to 3.2. Each robot could cover 3.5 alone, but moving both that far requires a half-width of at least 0.25, which the proof attains.

This extends the [different actuator boundary](../README.md). The continuous construction uses different velocity profiles instead of synchronous proportional paths. A direct sampled LP agrees, and the proof checks the full time interval. There is no comparison to field motion or claim about packet reliability.

Run with Python 3 and SciPy:

    python3 replay.py > actual.json
    diff -u results.json actual.json

The [asymmetric-gap follow-up](asymmetric-receipt/README.md) distinguishes clearance from link margin and gives an exact receipt deadline when the starting gap is hidden.

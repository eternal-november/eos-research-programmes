# Safe crossing from anonymous bearing histories

The simulator compares a latest-frame bearing stencil with anonymous history tracking at a timed indoor crossing. Both get the same precommit silhouette, sampling, delay, and resource budgets. A separate rational-time reference verifies the exact observation-cell safety boundary.

See [the result and model](Anonymous_Bearing_and_Crossing.tex), [simulator and executable checks](replay.py), [independent reference](reference.py), and [saved results](results.json). Reader-facing examples are under the witness keys in results.json. They distinguish collisions, safety-only refusal, and timed service.

Run from this directory with Python 3.10 or newer:

```sh
sha256sum -c SHA256SUMS
python3 -B replay.py | cmp results.json
```

This is a finite synthetic perception study, not a physical detector comparison.

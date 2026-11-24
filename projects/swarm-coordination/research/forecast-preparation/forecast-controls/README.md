# Forecast visibility, errors, and reversible preparation

[Statement, model, bounds, and evidence](Forecast_Control_Comparisons.tex) · [Executable replay](replay.py)

Run `sha256sum -c SHA256SUMS`, then `python3 -B replay.py | cmp results.json` from this directory. Exact replay uses Python's rational library; original C7 route and C3 closure/relay logic are exercised byte-pinned. The saved route traces are synthetic tests, not physical incidents.

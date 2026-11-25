# Exact diagnostic-order ambiguity for mission risk

[Proof and cap example](Risk_Diagnostic_Order.tex) · [model freeze](FREEZE.txt).
For symmetric joint diagnostic reports, count factoring preserves exact
risk bounds. Sharp examples hide a large union-risk difference even
with identical exact labeled pair laws.

    python3 -B replay.py | cmp results.json -
    OPENBLAS_NUM_THREADS=1 python3 -B check_direct.py | cmp direct.json -

The exact checker uses only Python 3.8+. The second command uses
NumPy and SciPy for a numerical control against full named-world LPs.
Lean checks the cap arithmetic, not the statistical model.

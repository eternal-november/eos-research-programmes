# A whole-law risk certificate across an observed alarm

For a tree of known pair marginals, preserve joint event-and-observation
state rather than taking a separate worst case after each report.
The exact model supports an optional job under the original ex ante cap
while rejecting it under a smaller cap binding the same live work.

[Proof, exact witnesses, and limitations](Evidence_Tree_Risk.tex).

    OPENBLAS_NUM_THREADS=1 python3 -B replay.py | cmp expected.json -

Requires Python, NumPy and SciPy (tested with SciPy 1.17.0). LP comparison
and lifted laws are numerical. The exact small rational event witnesses
are verified separately; this is not a field-risk estimate.

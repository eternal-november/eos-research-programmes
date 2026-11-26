# Named withdrawal after identical old occupancy reports

Actual old warehouse deliveries, unloads and clearing motions
produce two archived snapshots with the same receipts and
occupancy. They disagree when only one legally named shelf may
be relocated. Local conditional execution is checked separately
from acknowledging the grant and from realizing the subsequent goal.

[Claim, assumptions, profile proof and comparators](Named_Withdrawal.tex).
Stage the three named blobs from the repository's earlier
`integration/compound-settlement/SOURCE.tsv`. Python 3 and NumPy:

    python3 -B native.py /path/to/upstream | cmp native.json -
    python3 -B profile.py | cmp profiles.json -

`NamedWithdrawal.lean` was checked with AXLE Lean 4.35.0.
Same-information direct policy ties. The cases use a simulated
qualified same-cell label and installed authority; the study does
not establish either for a real warehouse.

# Native retry eligibility before another report debits the budget

[Scope, proof and comparison](Eligibility_And_Fairness.tex). Native
simulator dispatch shows how an opportunity can appear each period and
still vanish before the old report's retry cut. An authored persistent
headroom rule blocks just the modeled capacity loss, not route loss or
scheduler delay. This checks the assumption consumed by the previous
recurrence study, not a claim that stock SubT offers the guard.

Put exact pinned inputs at the destinations in SOURCE.tsv, then run:

    sh replay.sh /path/to/upstream | cmp expected.json -

Requires Python 3.10+, C++17, git for blob checking. StickyEligibility.lean
is the separately checked logical and arithmetic kernel. Authored test
and fixed-cut fairness model, no field or independent holdout claim.

# Frozen reserve checker interface

The subject is one already assigned additive service obligation at a fixed
finite horizon. Domains describe jointly possible loss of effective supply.
The declared boundary must include shared source IDs and any condition that
correlates retained supply with the incoming provider or with the amount owed.
The profile keeps the least retained supply on each reachable boundary slice
and keeps impossible slices distinct. A module may contribute several
possible capacity/request pairs to one boundary slice. Wiring uses every
combination with the retained slice only when this saturation is justified.

The checker returns a guaranteed bound, an attainable shortfall under exact
saturation, an unbound continuation if an added case was absent from the
old profile, or no continuation if the environment is empty. An unbound
continuation is not a zero reserve proof. Increasing private precision or
forbidding some retained combinations can make an old rejection inconclusive.
No capacity can count unless it is available by the same cut, under its actual
ownership, and its units can be added. This core does not model how capacity
is observed, how an allocation is selected, or risk over a probability law.

Alternative for comparison: explicit same-information join, then check every
complete compatible world. Also compare an ordinary incremental checker that
caches the same per-boundary sufficient statistic; it should tie, not be
penalized for computing the same object.

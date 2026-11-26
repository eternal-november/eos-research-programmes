# Finding a historical clock certificate costs more than checking it

The [proof](Cost_Of_A_Short_Clock_Certificate.tex) gives exact query costs for a fixed empirical risk cap. In the four-block model, four answers suffice to check any correctly chosen certificate. Finding the verdict requires up to sixteen deterministic queries, or ten in worst expected work with zero error and randomization.

The timing construction is a specialization of the [private offset model](../README.md). It embeds a classical [Boolean decision-tree problem](https://doi.org/10.1137/0220062), not a new decision-tree theorem. Each query is an ideal truthful historical offset-class read. The [LinuxPTP source check](../ptp-freshness/README.md) explains why polling a clock does not supply that query.

    python3 replay.py > actual.json
    diff -u results.json actual.json

The experiment prices query work, not network or sensing latency.

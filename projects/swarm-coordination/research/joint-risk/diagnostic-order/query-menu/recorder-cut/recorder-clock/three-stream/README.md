# When a third stream changes the cost of the risk audit

For two complete streams, weighted assignment gives the exact empirical union of failures at either extreme. The [three-stream proof](Three_Stream_Risk.tex) gives a sharp computational boundary for arbitrary source-justified linkage graphs. Even if the two non-anchor streams each have a valid independent join, checking that every joint linkage respects a fixed cap is coNP-complete. The reduction is from [Karp's perfect three-dimensional matching problem](https://www.cs.umd.edu/~gasarch/BLOGPAPERS/Karp.pdf).

There is a useful exception: if successful records in every non-anchor stream can match any episode, one ordinary maximum matching gives the worst count, even with many streams. The hardness proof uses restrictions on the successful records.

Run the standard-library replay:

    python3 replay.py > actual.json
    diff -u results.json actual.json

This extends the [two-stream audit](../README.md) at the level of the declared linkage model. It does not establish hardness for a particular sensor, the shared-offset acquisition graphs used in that replay, or a population law.

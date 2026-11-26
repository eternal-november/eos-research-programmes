# Shared report stages and a protected consuming cut

[Model, proof, provenance and limits](Shared_Stages.tex). A native failed
send that spent capacity can keep several otherwise honest caches stale at
once. On the authored topology, one such send means worst-case five
adaptive reads versus six fixed bare reads, or two fixed reads if each
cache can attest that it refreshed for this specific latch. Two still-live
sends can make identical bare contents require opposite decisions. The
selected native replays also show that a perfectly current snapshot at
acquisition cannot justify use after an unguarded source reentry.

Development only: the topology realizes the existing #636 incidence, the
time/keyed-freshness/hold interfaces are modeled, and no independent
holdout was used. The exact same-information solver supplies the policy.
No field semantics or architecture-level inventory disposition follows.

Materialize the exact sources in `SOURCE.tsv`. With Python 3.10+, NumPy
and C++17:

    set -o pipefail
    sh replay.sh /path/to/materialized-sources | cmp expected.json -

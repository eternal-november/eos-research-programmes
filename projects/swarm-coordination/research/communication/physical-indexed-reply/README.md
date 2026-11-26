# A guarded optical feedback bit for a route-indexed reply

**R1/L2 development, not independent acceptance.** Movement can change
which late reply is sufficient, but only when the endpoint is lawful and
seen by the right owner in time. Correctly decoding a marker does not
establish either freshness or settlement. An unacknowledged readout
also cannot be given to the reply decoder for free.

[Model, proof and checks](Physical_Indexed_Reply.tex) ·
[Development scope](FREEZE.txt) · [Lean kernel](Reply.lean).

Prepare AprilTag files from
[exact commit 94be783](https://github.com/AprilRobotics/apriltag/tree/94be783968e5091bcc9972c72c84fd63efce2935)
according to APRIL.tsv; the SubT layout is in the
[timed source producer](../../integration/subt-relay-debit/pending-scope/timed-source-producer/README.md)
and warehouse layout in the
[reactive-observation study](../../integration/shared-admission-core/reactive-observation/README.md).
Requires Python 3.10+, NumPy, Git, and C/C++ compilers.

    R=/path/to/eos-research-programmes/projects/swarm-coordination/research
    W="$R/multi-owner-coordination/named-withdrawal"
    sh replay.sh /path/to/apriltag /path/to/subt-source-parent \
      "$R/integration/subt-relay-debit/pending-scope/timed-source-producer" \
      "$R/integration/shared-admission-core/reactive-observation" \
      /path/to/warehouse-upstream "$W/in-flight/source-producer" "$W" \
      "$W/in-flight" | cmp expected.json -

The inputs are rendered optical frames, native packet replays,
and reconstructed physical effect traces in authored support laws.
They are not field image rates, a whole
stack result, or a held-out transfer.

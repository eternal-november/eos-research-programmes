# Typed effect-boundary transfer

The same selector runs at the receiving cut of [native station acceptance](../restart-and-replacement/README.md)
and [native warehouse set-down](../physical-restart-transfer/README.md). An old
command can only be covered by a common qualified guard or a real terminal fence.
Receipt, time, exact effect, authority point, site and generation remain separate.

[Typed law, comparison and limitations](Typed_Effect_Transfer.tex) · [Lean kernels](Boundary.lean).

Use the [ACK packing inputs](../ack-packing-window/README.md) with both
native source trees. Requires Python with NumPy, Git and C++17.

    R=/path/to/eos-research-programmes/projects/swarm-coordination/research
    S="$R/integration/shared-admission-core"
    W="$R/multi-owner-coordination/named-withdrawal"
    sh replay.sh /path/to/upstream \
      "$R/integration/subt-relay-debit/pending-scope/timed-source-producer" \
      "$S/restart-and-replacement" "$S/physical-restart-transfer" \
      "$W/in-flight" "$W" "$S" "$S/ack-packing-window" | cmp expected.json -

Receipt delivery and authority assertions are authored; effect and work
verdicts are read from native executions. Development transfer, not
independent acceptance or deployment.

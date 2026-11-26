# Packing a reply is safe only across an unconsumed cut

**R1/L2 development, not independent acceptance.** Packing a
prelude and later data can fit a shared radio ledger, but cannot
replace a receipt that must affect an earlier old operation.
Fresh data already available at the early cut or a genuine
spare authority path can close the respective gap.

[Scope, proof and source comparison](Ack_Packing_Window.tex) ·
[Development freeze](FREEZE.txt) · [Lean kernels](Window.lean).

The [timed source producer](../../subt-relay-debit/pending-scope/timed-source-producer/README.md)
gives the pinned input layout; use the warehouse inputs too.
Replay requires Python 3.10+, NumPy, Git and C++17.

    R=/path/to/eos-research-programmes/projects/swarm-coordination/research
    S="$R/integration/shared-admission-core"
    W="$R/multi-owner-coordination/named-withdrawal"
    sh replay.sh /path/to/upstream \
      "$R/integration/subt-relay-debit/pending-scope/timed-source-producer" \
      "$S" "$S/reactive-observation" "$W/in-flight/source-producer" "$W" \
      "$W/in-flight" | cmp expected.json -

This is an application prelude, not a claim about a middleware
transport ACK. Native radio/warehouse traces are coupled by an
authored physical gate and clock. None of the scripts commands
equipment or verifies a deployed protocol.

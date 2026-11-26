# Source impact compilation before recovery admission

This development adapter supplies the complete changed history fibers required
by [the fixed-cut checker](../named-fiber-revalidation/README.md). One unchanged
current decision can still hide a changed dependency on the next edit.

[Proof, counterexamples and limitations](Scoped_Source_Edits.tex) · [Lean lemmas](Diff.lean).

Follow the [ACK-window](../ack-packing-window/README.md) setup for the two
pinned plants. Replay requires Git, Python with NumPy, and C++17.

    R=/path/to/eos-research-programmes/projects/swarm-coordination/research
    S="$R/integration/shared-admission-core"
    W="$R/multi-owner-coordination/named-withdrawal"
    sh replay.sh /path/to/upstream \
      "$R/integration/subt-relay-debit/pending-scope/timed-source-producer" \
      "$S" "$S/reactive-observation" "$W/in-flight/source-producer" "$W" \
      "$W/in-flight" "$S/ack-packing-window" "$S/named-fiber-revalidation" | cmp expected.json -

The proof assumes complete versioned inputs and declared joint support.
This is not a tool for inferring physical faults or a field controller.

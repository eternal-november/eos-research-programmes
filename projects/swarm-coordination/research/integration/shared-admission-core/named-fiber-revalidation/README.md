# Versioned named-history revalidation

Development checker for one receiving cut and a fixed action menu. Reuse each
unaffected fiber's result, but retain which name supplied which result:
the same current verdict and blocker counts do not justify the same
decision after a named retraction.

[Model, exact information bound, comparison and limitations](Named_Fiber_Revalidation.tex) ·
[Lean lemmas](Fiber.lean).

Run against the pinned ACK-window and its radio/warehouse prerequisites.
See the [ACK-window setup](../ack-packing-window/README.md) for upstream layout.
The upstream source files remain inputs, not bundled or modified here.

    R=/path/to/eos-research-programmes/projects/swarm-coordination/research
    S="$R/integration/shared-admission-core"
    W="$R/multi-owner-coordination/named-withdrawal"
    sh replay.sh /path/to/upstream \
      "$R/integration/subt-relay-debit/pending-scope/timed-source-producer" \
      "$S" "$S/reactive-observation" "$W/in-flight/source-producer" "$W" \
      "$W/in-flight" "$S/ack-packing-window" | cmp expected.json -

The replay is civil simulation using selected pinned code. The checker assumes
qualified, complete history edits and does not infer them. The match to a
factored cached direct method is intentional. This is not an independent
holdout or contract acceptance.

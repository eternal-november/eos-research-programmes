# Restart, supplier rebind and effect-local settlement

One held-in I1 development case: lose the old receipt, restart the owner,
and lose a prepared replacement's path before settlement. The same
immutable obligation can still be supplied by a different path.
The measured effect is one simulated station acceptance, not physical work.

[Operating envelope](Operating_Envelope.txt) ·
[Proof and comparison](Restart_And_Replacement.tex) · [Lean kernels](Restart.lean).

Replay with the pinned SubT input layout from [ACK packing](../ack-packing-window/README.md);
the warehouse sources are not needed. Python, Git and C++17.

    R=/path/to/eos-research-programmes/projects/swarm-coordination/research
    S="$R/integration/shared-admission-core"
    sh replay.sh /path/to/upstream \
      "$R/integration/subt-relay-debit/pending-scope/timed-source-producer" \
      "$S" "$S/ack-packing-window" | cmp expected.json -

The atomic station gate is a modeled RIFL-strength application interface,
not a gain over RIFL or a complete architecture. This development case
does not use an independently selected mission.

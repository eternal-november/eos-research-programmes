# SphereMap endpoint connector

[Technical note](Graph_Path_And_Connectors.tex).
The selected public source distinguishes internal graph search from
certified physical connectors. This is a pinned C++ selector replay
with authored graph/obstacle geometry and a separate Lean-checked
swept-body boundary, not a complete SphereMap or ROS execution.

Stage the exact four files named in SOURCE.tsv under INPUTS, then
run:

    sh run.sh INPUTS | cmp expected.json -

The Space archive includes the staged inputs under up/.
Lean 4.35.0 with Mathlib checks Capsule.lean; all three printed
axiom sets were free of sorryAx.

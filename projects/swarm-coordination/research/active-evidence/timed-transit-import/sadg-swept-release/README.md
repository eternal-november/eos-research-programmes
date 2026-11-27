# Native SADG goal versus physical release qualification

The [technical note](Goal_Pose_And_Swept_Release.tex) gives the exact
half-plane timing boundary when a new rectangular-body plant is
connected to a stock goal-completion callback. This is an inert
selected-source replay with authored body and turn law, not evidence
of a fault in the unmodified simulator.

Supply the exact inputs in SOURCE.tsv under INPUTS:

    sh run.sh INPUTS | cmp expected.json -

The Space archive includes the staged inputs under up/.

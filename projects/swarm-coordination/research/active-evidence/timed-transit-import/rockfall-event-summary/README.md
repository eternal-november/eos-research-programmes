# Held-in cave rockfall event semantics

[Technical note](Rockfall_Events_And_Deployment.tex).
The source and replay distinguish detector entry/exit, a model-creation
call, remaining deployment allowance, and the lossy summary.
This is not a Gazebo collision, live topic or RF replay.

Stage the exact sources in SOURCE.tsv under INPUTS and run:

    sh run.sh INPUTS | cmp expected.json -

The Space backup includes all four inputs under up/.

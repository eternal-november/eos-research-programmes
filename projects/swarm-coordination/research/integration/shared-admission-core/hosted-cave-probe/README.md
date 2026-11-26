# A cave cue can consume an outstanding clearance margin

**I2 development, not independent acceptance.** The native COPS
recovery routes from the [coupled-fork study](../cops-coupled-fork/README.md)
remain individually feasible, but a hosted diagnostic can irrevocably
delay an old physical duty even if no cue arrives and no new report
is attempted. A separately authorized dedicated cue path avoids
that particular interference. The same-information direct check ties.

[Scope and comparison](Hosted_Cave_Probe.tex) · [Development scope](FREEZE.txt) ·
[Lean kernels](Prefix.lean).

Replay with Python 3.10+, SciPy, NumPy, Git and a C++17 compiler.
Prepare the pinned COPS and SubT inputs from the coupled-fork study
and the warehouse inputs from the
[hosted diagnostic study](../reactive-observation/README.md).

    R=/path/to/eos-research-programmes/projects/swarm-coordination/research
    S="$R/integration/shared-admission-core"
    W="$R/multi-owner-coordination/named-withdrawal"
    sh replay.sh /path/to/cops "$S/cops-coupled-fork" "$S" \
      /path/to/subt-source-parent \
      "$R/integration/subt-relay-debit/pending-scope/timed-source-producer" \
      "$S/reactive-observation" /path/to/warehouse-upstream \
      "$W/in-flight/source-producer" "$W" "$W/in-flight" | cmp expected.json -

The orchestration models which real simulation records are coupled;
it does not independently validate the mine geometry, old-duty scope,
or clock binding, and commands no equipment.

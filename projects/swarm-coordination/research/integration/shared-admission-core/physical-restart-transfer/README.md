# Physical restart transfer with a reversible actuator

A held-in comparison to [station acceptance after restart](../restart-and-replacement/README.md).
A delayed native RWARE load toggle can re-pick a shelf. Guarding only the
replacement writer does not prevent that. A state guard on all actuation
paths and a separate physical departure meet the modeled deadline. A
serial drain-then-read policy reaches the same state one tick late in the
unpaid branch.

[Scope, proof, and controls](Physical_Restart_Transfer.tex) · [Lean kernels](Physical.lean).

Use the pinned RWARE layout from the
[ordered command source producer](../../../multi-owner-coordination/named-withdrawal/in-flight/source-producer/README.md).
Requires Python with NumPy and Git. Native code is verified before execution.

    R=/path/to/eos-research-programmes/projects/swarm-coordination/research
    W="$R/multi-owner-coordination/named-withdrawal"
    sh replay.sh /path/to/upstream "$W/in-flight" "$W" \
      "$R/integration/shared-admission-core" | cmp expected.json -

Restart and writer queues are modeled, not field observations. This is not
an independent mission, hardware guarantee, or I1 acceptance.

[Repeated-effect extension](../reopening-physical-effects/README.md): a valid later pickup restores the same latch and pose. An old command can then fire unless the guard also respects duty identity or a genuinely nonreused generation.

# Byzantine Control Research State

Problem maturity: `design`. Handoff artifact: `draft`, ready to execute; author-side structural audit complete, independent semantic review open. The theory itself is not established or accepted.

Program target: generalize Byzantine control over ledger state to distributed control over generally specified state. Finite models and benchmarks supply evidence for that target; complementary mathematical pathways, including DEL, have explicit comparison obligations in R8.

## Active

- Execute [the research handoff](handoff/HANDOFF.md) with its [delegation and Git protocol](handoff/EXECUTION.md): create or reuse a suitable clean research worktree at a recorded commit, delegate related-work checks, integrate the resulting prior-art assessment before substantial original work, and account for R1–R8. Subagents are explicitly authorized for this research task. Preserve the primary checkout's unrelated uncommitted work.
- Reproduce the [foundation checks](handoff/VERIFICATION.md) before extending them. The 15 elementary declarations passed Lean 4.33.0; they establish only the stated logical, arithmetic, and finite-model results.

## Residuals

- Obtain independent semantic review of the handoff's model and the interpretation of its checked foundations. Kernel checking does not establish correspondence with a physical system or distributed protocol.
- Exact theorem imports remain open where the handoff marks primary-source checking as abstract-level or bibliographic only.
- Complete an integrated result connecting information, capabilities, coordination, or realized effects, with an executable instance, explicit service conditions, and a stated consequence for the ledger-to-general-state extension. Explicitly assess R3's information-dependent winning construction and R5's structural quorum generalization. R8 compares the mathematical pathways, including event-update, temporal, and strategic epistemic formulations; select developed bridges by their control contribution. Full protocol verification and the wider extensions have their own dispositions under R1–R8.

The handoff is the execution brief for the next research increment. It does not enact acceptance of a theory or resolve standing disagreements elsewhere in the workspace.

# Byzantine Control Handoff Verification

## Scope and reproducibility

Verification date: 2026-10-04. The handoff is a research specification, not a verified general theory. Its elementary foundation module passes Lean 4.33.0, commit `d8b18978322de05a8f3dba51ef03cf5461676c17`, with the installed standard library and no external package dependency. All 15 named theorem declarations have explicit axiom reports. No report contains `sorryAx`, a task-specific axiom, or a native-computation trust axiom. The dependencies that occur are drawn from `propext`, `Classical.choice`, and `Quot.sound`.

From this directory run:

```powershell
./verify.ps1
```

The script finds the pinned binary in an existing elan installation, checks the version, runs [Foundations.lean](Foundations.lean), and rejects unapproved reported axiom dependencies. It does not install a toolchain or change a global default. To use another location for the same version, pass `-LeanExecutable` with its Lean binary path. Direct execution with `lean Foundations.lean` is also possible when the surrounding environment resolves the pinned toolchain correctly. The `lean-toolchain` file pins the version for elan-aware invocations.

The discovery path matters on Windows: the account executing a command may have a different default elan home from the account owning the installed executable. Locating the pinned toolchain next to the installed elan launcher avoids treating a missing sandbox default as a missing Lean installation.

## Checked statements and their boundaries

The namespace is `ByzantineControl`. The table describes what the formal statements establish; the prose interpretation still requires matching their hypotheses to the target model.

| Declaration | Checked result | Limit on reuse |
|---|---|---|
| `winning_antitone` | A policy satisfying a predicate for every environment in a larger set also satisfies it on an included smaller set. | Policy type and satisfaction predicate remain fixed. Changing hardware, information, or the objective changes the comparison. |
| `coalitionwise_is_not_uniform` | Boolean choices exhibit `forall b, exists a` without `exists a, forall b`. | Logical obstruction only; it does not instantiate a distributed fault model. |
| `pairwise_is_not_joint` | Three finite action sets have pairwise compatible choices but no globally common choice. | One-step compatibility; not a claim that every pairwise test fails or that joint compatibility suffices for future control. |
| `uniform_policy_iff` | For a fixed observation map, a universally safe observation-based action function exists exactly when every observation fiber admits a uniform action. | Classical choice proves existence. The theorem is one-step and single-observer; it supplies no effective distributed selector. |
| `empty_successors_are_not_nonblocking` | An empty transition relation cannot satisfy the nonblocking safe-step definition. | The actual system's execution existence remains to be proved. |
| `invariant_induction` | Initial safety and preservation on every transition imply safety at every natural-number step of a given run. | No policy synthesis, run existence, service, or continuous-time result. |
| `envelope_step` | Coverage, a realized transition, a post-set overapproximation, and a safety certificate imply safety of that next state. | The hypotheses are explicit obligations, not constructed components or recurring estimator guarantees. |
| `same_external_view_does_not_identify_reading` | A constant external observation cannot distinguish two Boolean internal readings. | An indistinguishability witness under hidden internals; additional attestation can change the model. |
| `evidence_monotone` | Universal truth of a fixed proposition persists when compatible worlds shrink. | Formal implication also holds on empty sets; epistemic use separately requires nonempty compatibility and a fixed proposition/context. |
| `more_worlds_weaken_knowledge` | Truth over a larger compatible-world set implies truth over an included smaller set. | No conclusion that warrant remains when the world set expands. |
| `quorum_intersection_arithmetic` | With `n = 3*f+1`, two quorum-size lower bounds and the union-cardinality inequality force overlap greater than `f`. | The set-cardinality inequality is a hypothesis. Authentication, correct signing, and protocol invariants are not formalized. |
| `threshold_gate_feasible` | A natural-number threshold with `f < q` and `q+f <= n` exists exactly when `2*f < n`. | Arithmetic for the single-gate model in the handoff; not Byzantine agreement or physical actuation. |
| `ContinuationCounterexample.full_information_closed` | The explicit state-feedback policy preserves the safe subset of the six-state model. | Model-local closure; infinite iteration additionally uses the supplied induction theorem and the modeled transition relation. |
| `ContinuationCounterexample.uniform_first_step` | One fixed initial action keeps both hidden alternatives in the safe subset. | Only the first transition. |
| `ContinuationCounterexample.no_uniform_two_step_plan` | No fixed pair of actions safely handles both initial alternatives for two steps. | Represents the observation-based two-step problem because the initial observations coincide and every safe first action leads to indistinguishable successors. No communication, new sensing, or randomization is available in this example. |

The continuation example's safe set is exactly the full-information safety-winning set for the stated deterministic model: the explicit policy preserves all its five safe states indefinitely, while state 5 violates safety at the initial instant. Under the stipulated observations, a safe first action must be `wait`; its successors require different second actions. Therefore the checked finite plan failure rules out an observation-based infinite safe policy as well. This interpretation is a direct first-pass argument from the formal model, not a separate mechanized distributed-game semantics.

## Review of the handoff contract

The mathematical review checks the argument consumed by the handoff rather than treating successful compilation as validation of all prose. The corrected contract preserves unknown-fault quantifier order, local-history information limits, whole-fiber compatibility, continuation safety, execution nonemptiness, state-dependent feasibility, and separate progress assumptions. It distinguishes hostile actuation from actuator loss, report provenance from physical truth, historical lock events from current lock values, and institutional validity from realized effects.

The review also checks that one-shot quorum arithmetic is not promoted to a complete protocol proof; an empty certified action set is not promoted to physical impossibility; different safe-action sets are not automatically declared incompatible; and generic evidence monotonicity is not restricted by an unsupported classification of physical versus institutional facts. Shared component attributes are treated as possible dependencies whose consequences require modeling, not as proof that all related components fail together.

The eight research workstreams share one proposed execution contract and expose their assembly obligations. The handoff includes the necessary claims and definitions, a digital and physical benchmark family, primary-source entry points, outcome-dependent branches, and artifact requirements. The working specification has no dependency on other research notes. Its companion proofs check foundations; the program requires an additional integrated result and does not count those foundations as completion of the research.

[EXECUTION.md](EXECUTION.md) supplies the task's explicit subagent authorization and its self-contained orchestration procedure, a bounded prior-art assessment before substantial original work, clean-worktree isolation, ownership of writes and indexes, and result reintegration. These are operational instructions, not an empirically validated orchestration method. Their review checks that separate worktrees are not described as security sandboxes, that uncommitted primary-checkout material is not silently copied or staged, that negative searches do not certify novelty, and that subagent claims remain subject to semantic and evidential checks. The research team and its worktrees have not been launched as part of preparing this packet.

Primary-source checking is claim-scoped in the literature table of [HANDOFF.md](HANDOFF.md). Some entries were checked only at abstract or bibliographic level, and no theorem-level application inherits verification from that check. In particular, the exact attacked-linear-system separation theorem, observer topology results, knowledge-of-preconditions assumptions, barrier-function conditions, and physical-attestation mechanism remain retrieval and refinement obligations.

Scope clarification reviewed 2026-10-21: the program targets the generalization of ledger-state control to generally specified state; the session's bounded examples do not replace that target. R8 now names the complementary mathematical pathways and an explicit DEL–BFT event-update comparison. That comparison is a proposed proof obligation, not a verified encoding, and S11 is checked only at abstract and bibliographic level. Exact query preservation, iteration, and control consequences remain to be established. The Lean foundation module is unchanged by this clarification.

This is author-side structural review and Lean kernel checking of the named statements. Independent human or agent review of the definitions and their intended interpretation has not occurred. General distributed synthesis, a full HotStuff implementation, cryptographic assumptions, physical calibration, institutional recognition, and the proposed cross-domain correspondences are not certified by these checks. They remain explicit work in the handoff.

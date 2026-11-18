# Completion and verification audit

## Verdict

The significant-increment success criterion is met: C1–C4 give one integrated, locally implementable evidence–authorization–actuation construction with recurring service; C5 proves a same-objective interface obstruction; digital recovery, structural access results, and failed transfers explain the ledger-to-general-state consequence. The general theory and the residuals below remain unfinished. No institutional acceptance is asserted.

The maintained definitions, context indices, proofs, preservation laws, counterexamples, and claim ledger are in [README.md](README.md). The source review is in [SOURCES.md](SOURCES.md). This audit records verification and closure; it does not duplicate those definitions.

## Reproduce

From this research directory, run:

    ./verify.ps1

This resolves the existing Lean 4.33.0 toolchain next to the installed elan launcher. An explicit -LeanExecutable path can be passed, as can -PythonExecutable. The verifier changes no global toolchain or package configuration. Python 3.12 and its standard library suffice; no external package or solver is needed.

The script checks Control.lean, requires 14 axiom reports, permits only propext, Classical.choice, and Quot.sound, runs the complete Python model checker, and compares its output with results.json after normalizing line endings. It rejects missing reports, compile failures, unapproved dependencies, failed assertions, or changed results. The sources contain no unfinished proof, custom axiom, native_decide, or external-solver trust bridge.

The packet's separate foundation check was also reproduced with:

    ../handoff/verify.ps1

All 15 original declarations passed the pinned Lean toolchain. Those foundations remain unchanged; they are not counted as the new substantive result. Lean version reported 4.33.0, commit d8b18978322de05a8f3dba51ef03cf5461676c17.

For standalone replay without writing output:

    python check_models.py

The optional --output path regenerates the saved JSON. This is an executable mathematical model, not production networking or device-control software.

## Evidence and trust boundaries

| Check | Observed result | What it does not establish |
|---|---|---|
| New Lean module | 14 declarations checked; all axiom reports within the allowlist. | Fidelity of an unmodeled physical plant, actual signature security, message delivery, or device execution. |
| Physical finite model | 25,242 configurations; 118,998 certified-action transitions; all 16 static fault fibers and 112 safe state/fault records checked. Every admitted certified action is safe and every record has a certificate. | Unrestricted distributed synthesis, continuous dynamics, mobile faults, or longer delays. Counts are enumerated model cases, not statistical samples. |
| Singleton comparison | 12 locally certified median-only tables; all 1,728 three-authorizer profiles fail universal matching. Lean additionally proves the two-selector obstruction symbolically. | Impossibility with extra observations, communication, randomness, or informative setup. |
| Digital baseline | 524 enumeration iterations pass agreement and correct-leader validity; decisions are prescribed at the two-round boundary. Some iterations repeat behavior. | Parser implementation or cryptographic verification. Rejection of late raw proposals is a modeled rule; forged honest signatures are excluded by the idealization. |
| Structural families | 273 nonempty arbitrary fault families on identity universes of sizes 1–3 checked. | Exhaustion of larger families. The unrestricted Q2/Q3 mathematical statements are instead proved in Lean. |
| False-claim delivery | 32 worlds and 2,048 accessibility comparisons preserve atoms/relations and exhibit announcement failures. | Strategic and temporal query transport. |
| Certificate delivery | Six initial worlds; 8/12/20 worlds after successive updates; 1,216 accessibility comparisons, with correct historical/physical knowledge separation. | A proof of the supplied certificate-soundness premise or full protocol/lock encoding. |
| Named perturbations | Exact arithmetic witnesses for capacity, bypass, fault counts, missed reports, error growth, duplicates, stale evidence, and fractional transfer reproduced. | Universal impossibility where only a particular scheme fails; the ledger states the narrower conclusion. |

The finite physical enumeration collapses malicious integer reports to their exact median outcomes, not arbitrary samples: with two fixed honest readings, all integer medians between them are attainable and no other median is possible. All Byzantine authorizer endorsement subsets are enumerated. Correct sensor readings remain shared across recipients; only the faulty sensor equivocates. The same fault pair persists across successors. Infinite-horizon safety comes from the Lean induction plus constructed recurrence, not the number of finite transitions checked.

The formal Accepted relation is a support overapproximation. Its interpretation requires an ideal signature/protocol refinement: actual accepted artifacts have two distinct valid current-epoch endorsements; honest signers issued only certified actions. Availability also requires all honest endorsements to arrive. Neither requirement is hidden as an encoded theorem conclusion.

## Independent challenge and integration

Three read-only reviewers had the exact base, working directory, input packet, scoped obligations, and no write or Git authority. Their first related-work assessments were integrated before the first substantial proof. The coordinator alone authored and integrated files; there were no worker branches or shared-index mutations.

Independent analytic and executable checks challenged different boundaries. One reviewer enumerated 10,647 noisy-report/equivocation scenarios independently: no unsafe certified actions or empty honest intersections at error 1; increased error 2 yielded 5,280 empty intersections among 29,575 scenarios. Another independently exhausted 274 nonempty fault families on universes of sizes 0–3, including quorum-family existence by a different search, and 274 nonredundant broadcast scenarios. These different counts reflect different enumeration domains and duplication, not contradictory outcomes. The epistemic reviewer independently constructed guarded delivery models and inspected the final query-preservation claims.

Final scoped reviews inspected the README, proof statements, executable models, and results. The quorum reviewer independently ran verify.ps1 successfully with 14 declarations; the control reviewer replayed the JSON and inspected C1–C5; the epistemic reviewer replayed both epistemic functions and the obstruction checks. No substantive defect remained within those scopes. Final SOURCES.md and this audit were coordinator-authored; reviewers checked underlying source findings and results rather than these final editorial files.

Review produced material clarifications now integrated: service is actual withdrawal through a trusted port; timely sensing is a safety premise; the integer grid is necessary for availability; signatures grant alternative permissions rather than exclusive decisions; exactly-one effect is essential; the singleton impossibility includes different actor selectors; Q2/Q3 apply to role projections; excess-removal is a bounded counterexample; and repeated enumeration cases are not labeled distinct attack classes. Later precision edits separated explicit Lean conclusions from derived envelope-width reasoning and named the real-reading extension in the fractional counterexample. These changes preserve the proved result while narrowing its interpretation correctly.

## R1–R8 disposition

| Obligation | Delivered result | Precise remaining boundary |
|---|---|---|
| R1 semantic core/BFT recovery | Explicit distributed contract; D1 signed fixed-slot agreement, validity, termination and derived repeated-slot prefix recovery; narrowed historical-certificate knowledge. | Full Basic HotStuff guards, lock evolution, view changes and progress; chained variant separate. E1 does not certify all lock or higher-order protocol claims. |
| R2 sensing | Current noisy-report envelopes; exact state and fault-attribution separation; Byzantine equivocation handled. | Pose/calibration witnesses, moving sensors, physical attestation, and observer-topology imports need their own measurement models. |
| R3 capability/winning | Explicit joint influence and fixed hidden fault family; full safe-region winning construction for this architecture; no-sensing and hostile-capacity obstructions. | General continuation structures with richer histories/capabilities and necessary conditions remain open. The finite epoch compression is task-specific. |
| R4 composition | C1–C4 construct evidence, locally implementable authorization, nonempty selection, realized-effect safety and recurring service; trust termination explicit. | Gate, service port, timing, and physical disturbance bounds are premises rather than verified hardware. |
| R5 coordination/quorums | Exact Q2/Q3 family results, role projections, causal-capacity inequality, C5 singleton impossibility and successful permissive mechanism. | No minimal communication theorem for richer protocols; no claim that the separate access/capacity conditions suffice without the assembly proof. |
| R6 institution/evidence | Stipulated permission/credential/effect distinction and collapse witness; public artifact generation, soundness and non-vacuity. | Jurisdictional recognition, blame, appeal, power changes and reconfiguration authority are not modeled. |
| R7 time/recovery | Stale evidence, missed reports and fractional-state transfer counterexamples; exact delay/grid obligations exposed. | No validated continuous plant, general delay margin, exclusion/repair/reintegration or mobile-corruption guarantee. |
| R8 mathematical pathways | Applied enriched-event/history isomorphism; false public-announcement obstruction; local-policy/effect transport and its kernel. | No full DEL/BFT encoding, strategic equivalence, general finite epistemic quotient, or continuous controller refinement. |

The integrated result has substantive proof and constructive witnesses; this table is not a residual list offered in place of a result. It also does not label every large workstream complete. A next session can select an unblocked residual without repeating the solved core.

## Workspace boundary and recovery

Integration branch: codex/byzantine-control-20261021.

Worktree: C:\Users\Sean\.codex\worktrees\byzantine-control-research\eos-garden.

Selected base: 79b40856f81cd729a3d178a0f20ac29efb650b52. The complete six-file current handoff packet was tracked and clean at that base, and its contents remain unchanged. The attached managed worktree was created from this explicit commit.

The primary checkout began on main at that base, with three modified tracked files, an empty index, and numerous unrelated untracked paths. It was treated read-only. No primary file was staged, committed, stashed, reset, cleaned, restored, moved, or copied into the research. Shared repository objects and the new branch reference are the intentional Git effects of a linked worktree. The final primary status comparison is reported in the session commit and final delivery; no remote push or primary merge is authorized or performed.

All maintained changes belong to theories-and-designs/byzantine-control: this research package and the local TODO. The integration branch is retained for review and continuation. Its commit is the session record; Git preserves authoring history. The next action is selected from the parent TODO, not from an assumed completion of the broader theory.

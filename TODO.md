# Byzantine Control Research State

Problem maturity: design for the general program; the selected discrete fragment is developed and checked. Artifact condition: research package verified within its declared mathematical and executable scopes; handoff remains a research specification. Audit: independent scoped semantic review completed for the new core. Repository acceptance remains pending.

Program target: generalize Byzantine control over ledger state to distributed control over generally specified state. The original [handoff](handoff/HANDOFF.md) remains the program specification and [EXECUTION.md](handoff/EXECUTION.md) governs continued delegation and isolation.

## Checked increment

[Permissive authorization and bounded physical influence](research/README.md) is the maintained synthesis and claim ledger. It constructs a local noisy-sensing/Byzantine-authorization/hostile-flow controller with recurring service; proves that median-only singleton endorsements cannot always match; reconstructs Q2/Q3 access conditions and a signed digital baseline; and records epistemic, delayed, and continuous-transfer failures. [Completion audit](research/COMPLETION.md), [source assessment](research/SOURCES.md), [Lean proofs](research/Control.lean), and [executable checks](research/check_models.py) state verification and residuals. Run research/verify.ps1 to reproduce.

This closes the initial clean-worktree, delegated prior-art, foundation-reproduction, and integrated-result obligations for a significant increment. It does not close the general theory or authorize acceptance.

## Active choices

1. Extend the physical fragment through time: use the exhibited stale-evidence trace to define report age and pending-command state, derive a covering prediction envelope, and construct or refute a policy retaining the same service floor. Completion requires a realized-effect update, local implementation, nonblocking/service proof, and comparison with the zero-delay result.
2. Repair the demonstrated continuous-transfer failure: compare continuous controls with added integer-control margin using explicit real-valued sensing and dynamics. Completion requires a common-action proof plus a genuine physical abstraction/solution contract before exporting a continuous-time guarantee.
3. Broaden the coordination comparison: investigate full report-vector selectors or added inter-authorizer communication. C5 only excludes locally certified median-only singletons; it must not be cited as an impossibility for those richer interfaces.

These are alternatives for Orient, not jointly required next steps. The first two are informed by explicit failure witnesses; the third tests the exact boundary of the proved obstruction.

## Live residuals

- R1: encode Basic HotStuff's actual guards, historical locks and lock evolution before importing cross-view safety or progress. The current signed two-round baseline is a different, precisely scoped recovery. Chained HotStuff remains separate.
- R2/R3: witnessed pose/calibration, active sensing, sensor/actuator identity correlations beyond the present role caps, and changing capabilities need explicit measurement and transition semantics. Generic distributed synthesis remains broader than the epoch compression.
- R4: the gate's exactly-once action, reliable service port, current-epoch authentication, fresh sampling, and timely correct messages are realization premises. A monitor does not discharge them without a detection/response proof.
- R5: Q2 authorization, Q3 conflict exclusion, evidence coverage, and causal capacity remain distinct. Preserve the same joint fault family and the assembly argument in any extension.
- R6/R7: institutional recognition, attribution, repair, effective exclusion, membership changes, mobile corruption and key recovery are not certified by the discrete package.
- R8: E1 is a delivery-fragment correspondence, not a full DEL/BFT model. Temporal, strategic, lock-update and controller-refinement imports require their own preservation laws.
- Independent review of the entire original handoff and every foundation's broader interpretation remains open; completed reviews concern the selected new model and its used source boundaries.
- Literature: reopen the bounded searches before novelty, completeness, or current-frontier claims. Unused handoff references remain unverified for this session.

## Needs adjudication

- Whether to accept the checked increment's definitions and conclusions as a maintained basis for the broader theory. Mathematical verification and source checking do not enact this decision.

Continue in the retained research worktree on codex/byzantine-control-20261021, based on 79b40856f81cd729a3d178a0f20ac29efb650b52. Its location and reproduction instructions are in the completion audit. Preserve the primary checkout's unrelated uncommitted work.

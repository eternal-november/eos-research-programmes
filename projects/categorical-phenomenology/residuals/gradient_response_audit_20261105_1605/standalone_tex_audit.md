# Independent audit of the standalone training-response note

Audit completed: 2026-11-05, approximately 16:57 UTC.

Source audited:
`/workspace/scratch/7c603a38d9f4/universal_property_probe_20261105_1557/Controlled_training_responses.tex`

SHA-256:
`2c95e6f949943813ad3f4404941ad3f5d1c512691eb7ca7be164ecfeaa572dcf`

An unchanged snapshot is retained here as `audited_Controlled_training_responses.tex`.

## Verdict

No material mathematical error found. The theorem statements and proofs agree with the prior independent audit. The newly added global-existence, finite-reconstruction and exact bounded-depth adversarial-noise results also check. The novelty assessment is appropriately restrained and the principal caveats are explicit. This is an independent mathematical/source review, not formal verification or a guarantee that no error remains. I did not compile or render the TeX.

## Checks

1. **Model and quantifiers.** Both factor gradients use old factors; η is the same known fixed nonzero real number in both layers. Positive and negative η are distinguished from ordinary descent. Outputs are the entire matrix, and the definition includes F0. Different positive hidden widths are allowed. All-target-word equivalence is not confused with one two-probe reconstruction or one fixed loss. Adaptation is unnecessary for the separation proof, as the common F1 determines a common second target.

2. **One-step and two-step classifications.** The Gram recursion, scalar-shift kernel, sign convention (state 2 minus state 1), cubic second-response difference and elementary separating residuals all check. The m=n=1 exception is complete: (f,L+R) closes under every discrete target word. No full-rank, balancedness, genericity or small-stepsize hypothesis is missing.

3. **Controlled flow.** Locally bounded piecewise-continuous targets give the usual unique Carathéodory solution. With V=(||A||²+||B||²)/2, its derivative is −2||F||²+2<F,Y>≤||Y||²/2. Consequently parameter norms stay bounded on every finite interval, ruling out finite-time blowup. The shift relation is exactly the global output equivalence relation, not merely a necessary tangent condition.

4. **Fixed-target caveat.** The explicit 1×2 pair and its arbitrary-dimensional diagonal analogue remain indistinguishable for every constant target at every finite discrete time. The SVD/swapped-scalar explanation is sound even if a large-stepsize trajectory is unstable. The successful changing-target experiment and the constant-target failure have distinct quantifiers in the text.

5. **Width and rank.** The threshold h≥max(m,n) is exact for the existence of a nonzero feasible shift between common-width states. Below it, one-step equality already forces Gram equality. Above it, two steps are sharp for nonscalar interfaces. Gram-equivalent factors are orthogonally equivalent after zero-padding. Minimum width uses rank of the full Gram, not rank of the predictor. The zero-width versus positive-width convention is explicit, and the scalar case is handled separately.

6. **Finite reconstruction.** The m+n−1 selected first-step residuals recover off-diagonal entries and diagonal sums, hence a formal representative with L11=0. That representative need not be PSD and is correctly used only in polynomial calculations. The final two-update experiment recovers the omitted scalar by dividing the known selected-entry gap by ±η³. Exact reset and measurement assumptions are stated. No bounded-target claim is attached to this general reconstruction.

7. **Norm and noise statements.** The rectangular SVD proof gives the stated factor-one norm bound. For the concrete pair, the first residual is −Y0 and the second residual contains a term parallel to the first; this term cancels exactly. Hence target bounds, rather than residual bounds, yield the η-independent maximizers stated in the note. An independent symbolic check with Y0=(a,b), Y1=(u,v) gave

   `||F2(Q)−F2(P)||_F² = η⁶(a²+b²)(av−bu)²`.

   Thus the exact maximal gap is |η|³M³, attained by orthogonal targets of norm M. Closed ε-balls intersect at equality, so guaranteed discrimination requires the strict inequality |η|³M³>2ε. The identical-history adversarial argument remains valid for adaptive choices across trials and within depth-two trials. It assumes arbitrary per-observation bounded errors; the note correctly disclaims independent stochastic noise, calibration uncertainty, and longer-horizon impossibility.

8. **Primary-source attribution.** The Zhang–Peyré congruence/predictor/defect pinpoints match the prior inspected primary text. Tao's shift, mobility and width claims are accurately distinguished from the present two-initial-state quantifiers. I additionally re-opened Marcotte–Peyré–Gribonval: Appendix I equations (26)–(27) do give the Kronecker-sum mobility and scalar-identity kernel, and Proposition 3.10 gives the scalar continuous reduction. The finite-step mechanism is not presented as new. No global priority claim is made.

9. **Internal predecessor claims.** The recovered `learning_generated_characterizations.tex` does state and prove arbitrary finite scalar-depth response closure, behavioral classification and finite identification, with its own degeneracy qualifications. Its title/date and those of the two other project manuscripts match the bibliography. I checked the cited high-level characterization, not every theorem in those separate manuscripts.

10. **Verification reporting.** I copied and reran `check_gram_behavior.py` as `audit_replay_check_gram.py` in this audit directory. All stated counts reproduced: 108 closure cases, 108 cubic shifts, 96 reconstructions, 12 scalar cases, 108 Gram/rank cases, the two symbolic witnesses, eight scalar-ambiguity steps, and 30 stationary-target comparisons. Results are in this directory's `check_results.json`. The independent earlier observation-rank and numerical checks are reported faithfully. The recorded static-integrity hash matches the audited file. No compilation or proof-assistant result is claimed.

## Optional wording improvement only

In the Gram realization paragraph, replace “full positivity of G” with “positive semidefiniteness of the full block matrix G.” The current displayed G≽0 and subsequent singular-state statement make the intended meaning clear, but the proposed wording avoids an accidental reading as positive definiteness. This is not a theorem correction or a release blocker.

## Limits of this audit

The source-priority search remains targeted, not exhaustive. The adversarial-noise result is a declared two-hypothesis experiment, not a uniformly robust estimator over all realizable states. The proofs establish exact algebraic results and the stated worst-case boundary, not empirical usefulness. No edits were made to the source manuscript by this auditor.

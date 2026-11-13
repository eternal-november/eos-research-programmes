# Interacting architecture: scope and limits

Purpose and conclusion

This is a scoped research checkpoint, not a completed architecture-discovery
result. The main theorem remains OPEN. A valid discovery result must infer
unknown positive local mechanisms and their interfaces from readouts, require
one mechanism to work through time, and account for observationally equivalent
assemblies. No special operation may reveal component membership.

Scope and evidence table

Topic | Evidence included | Established scope | Boundary
No-reset noisy feedback | Noisy_Feedback_Architecture_Discovery.md; Independent_Mathematical_Review.txt; the feedback check scripts | Restricted finite-field identification, frame checking, ambiguity and interface results; finite checks rerun successfully | Full state is observed through invertible mixing; independent innovations make positive assembly automatic; not main validation or general discovery
Continuous-time branch route | CTMC_branch_audit_and_port_slice.md | Conditional generator-branch and interface tests; simple-spectrum autonomous-quotient invariance | Requires an identified state model and proposed frame/messages; no dedicated independent review in this package; not general discovery
Hidden-mode defect | Hidden_Mode_Defect_Review.md; Defect_Bound_Prior_Art.md | Necessary rank bound for same-state independent emissions; exact equality to a standard matrix-flattening bound | Not sufficient for positive realization; edge/mixed-time extension is false; no novelty claim
Persistent reflection benchmark | Positive_Dilation_Target.md; Persistent_Assembly_Obstruction.md; Persistent_Gap_Independent_Review.md | Stationary full-support process; full infinite Hankel nonnegative rank 3; no observed reset; each marginal <=3 edge states; joint edge minimum q; joint product state count between q and 4q | Mathematical stress test, not component discovery; nonnegative hidden matrices may contain zeros; no efficient robust finite-data method established
Prior-art boundary | Persistent_Gap_Prior_Art.md; Defect_Bound_Prior_Art.md; Compact_Certificate_Prior_Art.md; citations in source notes | Classical positive realization, masking, matrix flattening, automata simulation, structural algebra, sparse initialization and tensor contraction are relevant baselines | No priority or novelty claim; no exhaustive literature search claimed
Compact witness route | Compact_Discovery_Certificate_Route.md; Compact_Certificate_Independent_Review.md; Compact_Certificate_Checker_and_Nonvacuity_Review.md; Compact_Certificate_Prior_Art.md | Sound supplied-witness checking; initialized-rank and tensor-format counterexamples; short circuit proof for the latter; calibrated signed-CP completeness; all-bits-relevant rank-2n family | Strong local-control calibration includes reset maps in signed span; not uncalibrated discovery; sparse initialization need not preserve hidden stationarity; exact checking counts actual doubled contractions, output alphabets and coefficient bits
Existing executable checks | checks/check_noisy_feedback.py; checks/independent_certificate_review.py; checks/check_state_emitting_compact_example.py; checks/check_clock_parity_timing.py; checks/Checks_Run.txt | Ring/Fourier calculations; 168 small frames; 16 ambiguity lifts; interface counts; one 8-state/6-predictive-dimension compact example; clock decoder/noisy-rank checks on 96 hidden states | Finite arithmetic only; no proof of general discovery, reflection theorem, full compact theorem, or statistical performance

Reading conventions

For the reflection family, q is an integer at least 3 and the angle is 2*pi/q.
The irrational-angle statement is an exact-process impossibility result, not
a finite-data test for irrationality. Three observable dimensions, three
nonnegative static factors, three marginal edge states, and q joint edge
states are different resources and must not be conflated. The product-emission
state count is bounded, not proved exactly q. The bound on the full temporal
Hankel does not claim bounded nonnegative rank for every noncontiguous cut.

Checking versus discovery

Checking a supplied decomposition and its witness is not the same task as finding a
witness or deciding whether any decomposition exists. A failure of a compact tensor
witness format is not an impossibility result for every proof language. Any checking
cost must count the witness representation and stated input assumptions.

Review scope

The included independent AI audits review stated mathematical claims under their
explicit hypotheses. The compact checker audit initially reviewed the supplied
hypotheses before the final main draft existed. Its later text-level review
checked the final note and recorded the scope and corrections. The package was
cross-checked against both compact reviews. These are not external human peer
review, Lean or other formal verification,
or discovery-completeness certificates. The source notes retain their primary
literature links and any retrieval limitations. Packaging did not freshly
re-fetch those sources or undertake a new exhaustive priority search.

# Independent adversarial review

**Update:** The final primary experiment adds full-run monitors and fresh validation. Its reviewed certificate is **0.04042731731498145**. The addendum below supersedes the earlier primary-run numbers; the original two-run review remains as development history.

## Plain-language verdict

**Pass within its stated operational scope.** The strongest new run supports every bounded question about the two recorded signals at any three fixed time indices, under four specified controllers. It does this without assuming that the actual process has the predictor's structure. It does not establish complete trajectory accuracy, unknown physical architecture, or applicability to arbitrary controllers. Its lower evidence cost purchases this explicitly narrower guarantee.

This review independently inspected the main theory and both example scripts. Its own checker does not import either author's checker. It reconstructed all saved validation histograms directly from raw episode arrays, verified recorded controller actions, independently recomputed all 336 stronger-run predictive distributions, and checked all reported failed alternatives against observations. No blocking theorem or implementation error was found.

## Proof review

1. The confidence event concerns actual empirical test means or projected laws, not candidate-model residuals. Consequently it holds for every candidate simultaneously: no candidate-count union penalty or realizability premise is needed. This does not remove dependence on the test family or the covered controller family.
2. Test/controller declarations must be independent of their observed deviations, or covered by a prespecified weighted class. Adaptive selection of a candidate or of one already covered test is legitimate. Adaptive creation of new tests with favorable confidence weights is not.
3. The finite-alphabet TV identity uses the maximum positive set discrepancy. There are exactly `2^s-2` nonempty proper subsets, so one-sided Hoeffding suffices. No additional factor of two is needed. The stronger run correctly uses `s=64`, not `s=8`.
4. The uniform event needs IID complete episodes within each controller stratum. Temporal dependence, dependence across different projections, and shared next-state noise do not invalidate it. Four on-policy strata cost four times the per-policy count. Neither this proof nor the software proves that real acquisition/deployment satisfies these assumptions.
5. Approximate completeness with `2r` slack follows by two triangle inequalities. It concerns exhaustive finite program search, whereas the experiment uses BIC and rounding heuristics. The report does not confuse those algorithms.
6. Positive program execution plus finite-horizon exact prediction gives a real predictive representation, not just unrelated fitted moments. The program need not be an online filter executable from each physical subsystem's local observations; that stronger capability is separately flagged.
7. Pullback closure establishes only the declared postprocessing semantics. Action-changing contexts require controller coverage. Separate marginal tests do not justify arbitrary joint composition. The parity counterexample correctly shows the missing higher-order distinctions.
8. Prefix-coded countable tests support a simultaneous confidence statement, not an unrestricted terminating verification algorithm. Any claim of executable exhaustive search must retain the stated finite runtime/resource limitations.

## Independent numerical/source checks

Run `python review/independent_raw_review.py` from the source package (the script resolves its own directory). Results are saved in `review/independent_raw_review_results.json`.

| Check | Three-bit run | Three-time joint run |
|---|---:|---:|
| Raw projection histograms reconstructed | 3,264 | 336 |
| Independent exact DP distributions | 20 dispersed cases | All 336 |
| Uniform TV certificate | 0.038262112578125 | 0.03957171277107715 |
| Exact-rational confidence failure upper bound, displayed decimal | 0.04150435087425041 | 0.04148309532621838 |

The independent recurrence appends selected bits chronologically, rather than using the author's preallocated word positions. It builds positive transition tables directly from the frozen candidate and uses integer masses with a common denominator. Every independently checked law sums to one and matches its saved exact fractions.

All heldout arrays have the expected episode lengths, counts, and controller actions. The warmup readout is used at the first remembered-change action and in the initial two-readout state; it is not accidentally treated as a future observation. It is supplied observational access, not inferred for free. The certificate applies to the integrated initial law, not separately to every possible warmup value.

All three ablation bounds in each experiment were independently recomputed as empirical TV minus the fixed confidence radius. They exceed .05 under the same simultaneous event. These reject the three specified programs, not every implementation lacking a named resource. Candidate-oracle separation alone would not suffice, but is not the sole evidence used here.

The radius uses fixed whole-episode counts, not estimated visit frequencies. Rational Taylor truncation is a lower bound for the positive exponential; division therefore supplies a conservative failure upper bound. Both counts include training. The two experiments together used 300,000 episodes; their separate confidence statements must not be promoted to one simultaneous 95% statement without adjustment.

## Interpretation guards that must survive packaging

* **Fixed indices:** “any three times” means any three fixed indexed times. Selecting one fixed query after looking at the dataset is covered; choosing observation times separately within each episode by a full-history stopping/selection rule is not automatically covered.
* **Fixed acquisition controllers:** within-episode switching or a newly synthesized policy is not covered. An independently chosen episode-start mixture of the four is covered by convexity.
* **Supplied ports, learned dependencies:** two output ports and a finite one-lag input vocabulary are supplied. Unknown masks and tables are learned. This is predictive dependency discovery, not discovery of an unrestricted physical component partition.
* **Search restriction versus soundness:** the proposal vocabulary is engineered for this synthetic generator. It affects probability of finding a useful candidate, not the validity of acceptance for out-of-class processes on the covered queries.
* **Evidence comparison:** 210k versus 10.24m gives 48.76-fold fewer episodes and 12.19-fold fewer transitions. These are different-strength guarantees, not a 49-fold improvement on the old all-controller full-trajectory guarantee. The weaker exploratory run yields the separate 113.78-fold episode ratio.
* **Useful representation still needs justification:** direct empirical answers to these tests use the same concentration machinery. The additional output is an explicit reusable joint recursive predictor. Its scientific/practical usefulness is not proved by the concentration inequality alone.
* **Physical assurance:** a thermal/collision hazard requires an observed covered score or a separately sound relation. No stability, safe experimentation, or physical hazard-grounding theorem follows here.

## Verification status

Independent AI proof/source review plus reproducible Python exact-arithmetic and raw-data checks. Not Lean verification, external human review, or physical validation. The reviewer observed source and saved artifacts, not an externally timestamped preregistration; protocol chronology is supported by script ordering and authors' records, not independently authenticated.


## Final-primary-run addendum (2026-10-29 16:20 UTC)

**PASS.** Reviewed `Final_Operational_Discovery.md`, `check_monitor_service_discovery.py`, and all final `monitor_service_*` artifacts. Independently checked:

* all 336 final three-joint-time histograms against the new raw episode arrays;
* all 336 associated exact candidate laws, with the independent projection recurrence;
* all 16 full-run maximum-run histograms against raw records using contiguous-window occurrence tests;
* all 16 exact full-run laws using a distinct threshold-survival recursion: compute `P(maxrun < k)` by killing paths at the first length-k run, then difference these cumulative probabilities;
* every final controller action, all three final empirical ablation lower bounds, and equality of the frozen final candidate to the second development candidate;
* final seeds `202610301611` through `202610301614` against the executable seed schedule;
* the combined union bound over `4*[84*(2^64-2)+4*(2^10-2)]` categorical subset tests.

The exact final certificate is `41397572930541/1024000000000000`, or **0.04042731731498145**. Its rational failure upper bound displays as **0.04148309532621838**. The extra monitor terms are included even though they do not alter these displayed digits. All quantities are independently checked in the updated `independent_raw_review.py`.

The script produces the same training sample and candidate from the earlier training seed, before generating the fresh final holdout. It does not use final validation for fitting. As before, this is source/artifact review, not independently authenticated historical preregistration. The primary confidence claim now concerns only this final batch. Investigation cost is **500,000 unique episodes**; the reusable one-pass protocol requires **210,000**. These must not be interchanged in cost claims.

The maximum-run laws legitimately cover events whose occurrence time varies across the episode: they are predeclared whole-run functions. This does not confer unrestricted adaptive selection of observation times or unrestricted joint functions of multiple monitor outputs. The fixed-index qualification still applies to the three-time projection component.

The final nonidentification argument is valid. The map from laws on `4^9` readout paths to at most 5,416 context probabilities has a nonzero kernel; normalization is in its row span. A nonzero signed kernel element therefore has positive and negative parts of equal mass. Normalizing those parts gives disjoint-support probability laws with identical context outputs. Drawing the path at initialization and ignoring actions realizes both as causal environments for all four controllers simultaneously. Supply the same independent warmup convention. Full readout TV remains one, and hence so does full transcript TV; no Markov premise is needed.

One interpretation guard remains important: the abstract's statement that a shared source is “needed” should refer to this learned implementation and the specified independent-update ablation, not to a universal resource-minimality result. Alternative state representations or relocation of randomness were not exhaustively excluded. This is already correctly qualified in the body.

## Delivery-report scope audit

Read `Evidence efficient discovery results.txt` in full (reviewed text SHA-256 `4eba469b57d0bffb74d95b1cb1bab0668b34c42f538b9396c1e46fd70cf90db7`, before final wrapping/typographical cleanup). PASS: abstract and body correctly separate the 210,000-episode reusable workflow from 500,000 actual investigation episodes, acknowledge changed guarantee strength, retain fixed-index/controller/individual-monitor restrictions, distinguish heuristic proposal from exhaustive discovery, and account for shared-source implementation and warmup. All displayed controller bounds, learned mixture estimate, full-run maximum, and ablation numbers match the artifacts. No substantive report correction was required. Suggested only using approximate equality for a rounded decimal representation of an exact rational.

A final metadata audit confirmed that `monitor_service_results.json` contains the **combined** triple-plus-monitor exact confidence fraction, not merely the projection-only fraction. The independent checker now asserts equality with that saved fraction, and passed its final rerun. Fresh holdout seeds are explicitly recorded separately from the training seed.

Final delivery text SHA-256 verified: `4b9df5c9509c9d667713a09b94cbded6fd7aa7786da23babd36ca7abf633a60e`. Reviewed the added sample-cost scaling paragraph, expanded candidate-state versus physical-state qualification, development seed lines, reproduction-checker listing, and decimal approximation correction. These changes are sound and preserve the PASS judgment. The added theory section's exogenous episode-start mixture closure is also valid; it correctly excludes within-episode switching and warmup-correlated controller selection.

## Bounded implementation carryover and final text

Reviewed the final bounded-source addition to `check_compiled_predictor.py`, ran it successfully, and independently enumerated all 2^20 possible fair-bit words (saved as `review/independent_bounded_sampler.py`). The implemented map is `floor(200 U / 2^20)`, not remainder modulo 200. Its source TV from Uniform200 is exactly `33/1638400`. Pushforward cannot increase TV; coupling the eight fresh sources bounds complete-transcript discrepancy by `33/204800`, even with feedback, because identical histories produce identical controller actions until a source mismatch. Initial Uniform16 sampling uses four exact fair bits and adds no error. The exact predictor's operational certificate therefore transfers to the bounded sampler with exact bound `41562572930541/1024000000000000`, less than outward `0.040589`. This is deterministic approximation accounting and uses no extra observations or confidence budget. Fairness, fresh independence, correct computation and delivery remain implementation premises.

Verified the final paragraph matches this floor-scaled implementation and distinguishes its bound from the exact predictor's `0.040428`. **Latest final report SHA-256: `8412cfe218ac8ade582b48f624fde01da7a73a24dfdf848914c892ff7a7a5d3e`. PASS.** This supersedes earlier report hashes in the audit chronology above.

# Independent physical-contract challenge

Final review status: the theorem, final TXT report and reference implementation have no outstanding blocker under their explicitly declared model, calibration and timing premises. No physical hardware or real-time scheduling claim is verified. Frozen hashes are recorded in section12. The sections below preserve the review chronology: initial objections and superseded numerical versions are followed by their repairs, not left as unresolved contradictions.

## Plain-language finding

A prediction certificate concerns recorded signals. A stopping guarantee concerns distance traveled by a real body before its brakes take effect. The bridge must account for everything occurring between a sensor sample and the end of braking. A missing-data fallback is not automatically safe: its deadline must have been reserved before motion was authorized. Moreover, if a worst-case braking guard already guarantees safety, the learned decomposition must earn its relevance through a proved improvement in admissible motion or task completion.

## 1. A precise envelope to check against

For a stationary obstacle and a sample-time lower bound d on free distance, a sample-time upper bound v on forward speed, upper acceleration a >= 0 before braking, delay T >= 0 until guaranteed brake onset, and guaranteed deceleration b > 0 thereafter, the sufficient distance is

D(v,a,T,b) = v T + a T^2/2 + (v+aT)^2/(2b).

A positive geometric reserve must be added if contact at equality counts as collision. This is a sufficient contract, not an exact physical law. It presupposes that the bounds remain valid until standstill; no reverse movement/overshoot; a relevant obstacle remains represented; and the robot's swept footprint is represented in d.

T must start at the same timestamp as d and v. It includes message age, clock-error allowance, processing time, command transit and brake response. If motion is authorized until another check, the worst permitted interval until that check or independent timeout is also included. One must not count sensor age twice, nor omit it by treating old telemetry as current.

A moving obstacle with maximum closing speed u requires at least the additional approach distance u[T+(v+aT)/b] through robot stopping time under these simple bounds. Even this gives no post-stop collision immunity: an obstacle may continue moving into the stopped robot. State the obligation as robot stops before contact over a specified interval, or supply a stronger obstacle/escape premise.

## 2. Exact counterexamples

### Ignoring latency

v=1, a=0, b=1, distance d=3/5, brake delay T=1/5. Instantaneous-brake formula says 1/2 < 3/5 and admits motion. Actual stopping travel is 7/10 > 3/5, so collision occurs. A delay-aware formula rejects.

### Timeout after commitment

Same speed and braking strength, d=3/5. A controller expecting a new reading after 1/5 second and braking only when it fails has already consumed 1/5 distance; only 2/5 remains, less than the required 1/2. Calling this action a fail-safe stop does not establish safety. The preceding admission must reserve the timeout interval plus brake response.

### Instrumentation changes the system

A guard proved for T=1/10 admits d=13/20 since required travel is 3/5. If acquiring an additional observer signal adds 1/10 communication delay, actual requirement becomes 7/10 and the admitted trajectory is unsafe. Observer discovery must either preserve validated latency budgets or be included in the action/protocol regime whose law and envelope are certified.

### Hidden physical hazard

Two worlds produce identical recorded range and speed histories. One has guaranteed b=1; the other has b=1/4 due to unobserved brake degradation. At speed1, instantaneous stopping distances are1/2 and2. No transcript-TV statement distinguishes them. A sound brake lower bound, observable health envelope, or an explicit failure allowance is indispensable. Statistical validity within a model family cannot certify this physical premise by itself.

## 3. Assurance bridge (standard transfer, not the new contribution)

Let a genuinely executable controller produce a transcript law P, let Q be one coherent certified predictive law, and let B be a measurable transcript bad event for this exact controller including its timers, guards, and failure branches. If TV(P,Q) <= epsilon, and the actual physical hazard F implies B except on an envelope-failure event E with P(E) <= beta, then

P(F) <= min(1, Q(B) + epsilon + beta).

The physical implication is the substantive bridge. It cannot be inferred from the statistical certificate. If data provide a confidence event of probability >=1-delta, the bound holds conditional on that event in the usual frequentist assurance sense; delta is confidence failure, not automatically another per-execution probability without specifying the joint data/deployment experiment.

Approximate deployed arithmetic, timing, random-bit implementation, or changed sensor schedules must either be included in B/P/Q or contribute separately justified discrepancy bounds. Fixed-point outward rounding can establish deterministic soundness; an unbounded floating-point computation cannot silently be treated as exact.

## 4. Repeated admissions and hidden-world persistence

A controller may adaptively make many admissions. A one-step/window guarantee cannot be restarted at zero cost each time. Either certify the entire mission transcript under the same persistent world and use one path bad event, or prove conditional bounds valid for every reachable admission history and sum a risk budget. Marginal unconditional per-window estimates are not conditional guarantees after selection. Fresh process noise is legitimate; replacing the structural/environmental world at each decision is not.

## 5. Significance gate

Two acceptable routes:

(A) Hard guardian: prove safety for every declared physical uncertainty. Then show the learned joint decomposition supplies better sound envelopes/information and provably admits motion/tasks the stated baseline cannot, while accounting for its sensor/time/memory cost. Merely predicting the guardian's already-safe behavior is not a substantive safety advance.

(B) Risk-qualified admission: admit conditions the worst-case guard rejects using a certified joint risk bound. Retain the adverse physical outcomes in the example and price them in the risk budget. The fallback may mitigate later risk but cannot erase a hazard made unavoidable by an earlier admission.

In either case compare against a meaningful simple alternative (a direct sufficient statistic or full-window guard), not only an intentionally poor marginal model. State whether decomposition lowers evidence, runtime memory, communication, or conservatism, and demonstrate that saving.

## 6. Runtime proof obligations

- The controller reads only available ports and its own memory, never simulator latent state or a ground-truth regime label.
- Sensor and command timestamps have declared clock semantics and skew bounds.
- Scheduling, missed deadline, timeout, queueing and brake precedence are explicit.
- Conservative distance/speed/braking intervals include quantization.
- Startup safe state and the first admissible movement are justified.
- Loss of data while outside a robust stopping region is reported as unresolved/unsafe, not fixed by a stop command.
- Stationary versus dynamic obstacles and the physical hazard horizon are explicit.
- An executable model is not hardware validation or field assurance.


## 7. Review of initial theorem draft (18:48 UTC)

Reviewed `theory/Timed_First_Loss_Assurance.md`, initial 18,473-byte draft.

The physical first-loss induction is valid under the stated segment witness, initial state inclusion, complete terminal-tail accounting and physical event G. The distinction between the live uncertainty set U and the stronger zero-risk backup region V is important and correct: requiring every admitted segment to remain in V would accidentally eliminate the intended risk-qualified permissiveness.

The exposure-weighted transfer is also valid. The coupled mass reaching an equal live prefix is at most the Q marginal mass there; multiplying by the pointwise mismatch allowance and summing yields E_Q sum_live epsilon. Coverage exit need not add a separate statistical penalty when it deterministically becomes either certified physical termination or assurance loss. It does not disappear: the latter case is included in alpha_Q.

Independent rational finite test `check_exposure_transfer.py` checked 104,976 depth-two binary stopped-tree configurations, including branch-specific safe exits and loss exits, with kernel entries 0,1/2,1. All satisfy the Q-weighted inequality. This supports implementation checks only; the general proof is the coupling argument.

Requested author clarifications before final acceptance:

1. Explicit initial inclusion z0 in U(h0) on G, not just collision-freedom of U.
2. The inherited predictor must certify the actual output/action protocol used here. New timing/status ports, missing/crash labels and speed actions do not inherit a previous certificate by renaming. A causal deterministic transducer of already certified outputs is legitimate, but its physical correctness is an additional premise; newly introduced stochastic outputs need their own joint certificate. In particular, merely adding a cemetery label to the sample space does not certify the probability of a crashed execution.
3. A one-manoeuvre physical example may legitimately use H=1 if it consumes one modeled stochastic outcome, although its plant integrator runs many time steps. This is not H=1 for an otherwise unconstrained many-tick physical process. State the embedding and any speed-invariance premise.

Implementation, numerical certificates and final theorem revision remain pending independent review.

## 8. Coarsened-history adapter caveat

A common causal adapter preserves a full-trajectory TV bound, but does not automatically preserve each conditional-kernel bound on the coarsened physical history. Example: source first produces a hidden bit with probability1/10 under P and1/5 under Q, then copies that bit deterministically at the second step. The adapter suppresses the first output and reveals the second. Source second-step conditional kernels agree exactly at equal source histories (epsilon2=0), but the physical second-output laws conditioned on their common first physical output differ by1/10. Thus the inherited second-step pointwise bound is not zero on physical history.

Repair: retain a sufficient source context as part of the certified interface/history, or conduct the coupling and exposure computation on the augmented source process and then project the resulting trajectory guarantee. This does not prevent the theorem; it prevents an invalid pointwise shortcut. Communicated to author before finalization.

## 9. Revised theorem and substantive contextual result

Reviewed revised theorem SHA256 `db991c7ad297758fdbb6fde1587d313ba0fc195ce756d5b0220135165199eec0`. Initial inclusion and certified-protocol requirements are now explicit; the adapter lemma correctly works on augmented source history and explicitly disclaims automatic conditional bounds after coarsening. The exact-support corollary is sound: when the learned response is exact on its stated identification event and the residual support is promised by the model class, checking every possible supported outcome needs no probability-estimation TV penalty. It does not validate the support promise against arbitrary physical mechanisms.

Independent `check_contextual_support.py` verifies:

- At current action all−1, retained run length2 on channel10, all other runs0, speed1100mm/s has worst supported stopping distance1,248,500µm, below the1,260,000µm conservative clearance. Speed1200 is not robustly admissible.
- Over all600 relevant memory contexts with the same current actions, speed800 has worst distance1,208,000µm and speed900 has worst distance1,494,000µm. Thus a history-blind robust observer admits at most800 on this speed grid, whereas the favorable known history admits1100.
- Every tested ten-millisecond tick-distance estimate dominates the independent continuous acceleration/cruise/braking integral. The last fractional braking tick is conservative, not an optimistic integration shortcut.
- In the base context, one supported adverse outcome defeats every grid speed>=1000. Therefore even a randomized policy robust to every supported source law at risk budget0.1 has expected requested speed<=930 (mass on high speeds<=0.1), whereas the distribution-qualified learned rule requests1000 with its stated approximate9.17% bound. This is a requested-speed metric, not expected successful travel or task completion.

Interpretation: the strongest hard guarantee comes from discovered contextual response and recursive memory, not from stochastic correlation. Independent noises with the same support give the same hard result. Correlation is relevant only to the separate soft-risk admission. A direct full joint table can reproduce that soft-risk admission. The favorable action history is an input to this example; no theorem establishes that an actual robot can safely create it. These distinctions should remain visible in the report.

The physical map, stationary obstacle, actuator response, clock behavior and protocol invariance remain stipulated synthetic premises. The zero model-side risk statement is conditional on them and on correct response identification; it is not a physical failure probability of zero.

## 10. Executable review status

Independent rerun of `examples/check_c_controller.py` completed:14,400 context/action/clearance cases match the Python tick model, with undefined-behavior sanitizer enabled. Reviewed C source SHA256 `27720852a9faffebad02da45244a1d7d4a3fd10ccac397f787021dd7600b065f` and Python source `17eadf405726fe1802879e0d7877e7571d4f18212cddb8f4d3ab47d6b14b99fb`.

The controller decision path uses integer count inequalities with outward13247/1,000,000 TV allowance; future telemetry is not an admission input. Its memory update is causal. Actuation tests cover authenticated-source/sequence matching at the reference-program level, local watchdog expiry and a latched brake. This is not a cryptographic source-authentication implementation. The physical actuator-authority/timing contract remains external.

The bounded arithmetic is adequate for the declared ranges: at most131072 probability counts, risk cross-products well below64-bit limits, speeds<=1200, braking>=500, and input timestamp/distance bounds before subtraction. Serialized memory snapshots are a test harness, not an externally trusted physical sensor input. Runtime execution cost and hardware timing have not been measured; the ten-millisecond computation deadline is a contract premise, not established by C compilation.

Conclusion: no outstanding mathematical or reference-code blocker found in the reviewed revisions. The report should preserve all model-class, calibration, protocol and favorable-history qualifications above. No new Lean, external human, or physical verification is claimed.

## 11. Reopened execution-timing review (supersedes previous numerical stopping distances)

The parent identified an important remaining gap between the reference brake-request flag and mechanical engagement. The revised code now adds a positive10ms dispatch/engagement allowance to every braking path. Watchdog eligibility is310ms after the ramp; physical engagement must occur by320ms, with watchdog dispatch lateness included in that allowance. The final contract uses nominal computation10ms plus ONE shared10ms overhead for sample dispatch, acknowledgement dispatch, watchdog scheduling lateness and mechanical engagement. The four overheads must sum to at most10ms; they are not separately allowed10ms each. These are external timing bounds, not proved by the host run.

The sample request is now latched when elapsed time is at least its threshold, avoiding a lost equality-triggered request. Clock input bounds are checked before timestamp subtraction. The clearance packet now requires a separate rest-since-capture predicate; being at rest only at admission is insufficient. Its physical truth remains an external condition, not something validated by setting a Boolean field.

Independent analytic checks were rerun after the extra10ms. Updated warm-context1100 worst distance is1,259,500µm, still below1,260,000. Updated history-blind maxima are1,216,000µm at800 and1,503,000µm at900. Thus the same admission separation survives, but earlier numerical distances in sections9–10 refer to the superseded zero-additional-lag version. Every revised tick distance continues to bound the continuous kinematic integral. The explicit10mm protected reserve is already subtracted from the clearance; the additional mathematical margin is only0.5mm in the favorable1100 case. Additional unbudgeted delay invalidates it.

Final timing-comment synchronization and expanded two-budget C regression were requested before freezing the sources.


Final synchronization: source `controller.c` SHA256 `3d983a69f2bd6e4623e65071f4baedd5d48d8c4948479578f475adeb2210e39c` and `timed_controller.py` SHA256 `5647e97b4835d4fd4446620ad5d72c9d004dc087650eb245239581f5fcd70f3c` include the reopened fixes. The timing checker independently passed24,024 integer allocations of the shared overhead, including5,040 cases with strictly positive lateness at every stage. Its inequality follows generally from min(A+x,B+y)+z <= min(A,B)+x+y+z for nonnegative delays, so integer enumeration is supplementary rather than a proof restricted to integer hardware delays. Executor tests now explicitly skip the exact sample-request timestamp and pass an INT64_MAX invalid timestamp.

Final independent full regression completed at19:03 UTC:28,800 C/Python decision comparisons passed at risk budgets0.1 and0.0001 with undefined-behavior sanitizer; recorded source hashes match the final timing-revised files above. Reopened timing and initial-stationarity issues are resolved at the explicitly conditional mathematical/reference-program level. Hardware satisfaction of these premises remains unverified. For terminology,100ms is the nominal cruise/stop-sampling checkpoint;310ms is the hard watchdog eligibility time, not two contradictory lease expiries.

## 12. Final report and support-guard freeze

Reviewed the final correction separating `unsafe_support` from the empirically weighted bad-event count. A supported but empirically unseen unsafe outcome must not enter the zero-risk branch. The C and Python programs now track these separately; a low risk budget below the TV allowance rejects an unsafe-support outcome even when its empirical mass is zero. This repair was identified by the parent and checked here.

Frozen source identifiers:

- Theory: `db991c7ad297758fdbb6fde1587d313ba0fc195ce756d5b0220135165199eec0`
- C controller: `c51032479d6ce22c389f36ed58b86b494d5e090e2c2fe7864a16b4d2bb36a93c`
- Python simulator: `d24d4a7b51c1ef55c45371c8fe5565e4c36ff360d021b228d426dc9503dccb57`
- Executable specification: `adc2ab66b377ae29ab988043e370c7aeffdb5abcdc262dff85b57440be92ed7a`
- Full TXT report: `078c01cb437054e79dd254875cd26c5b1530a3e3d84ab432302536b1afc50e2d`

The complete report was read against the theory and executable results. It correctly distinguishes contextual hard-support admission from the secondary soft-risk illustration; preserves all hardware/calibration/history qualifications; and identifies C as a reference supervisor/executor with a stdio harness rather than board firmware. One wording error found in report review (describing `live` as absorbing) was corrected. The report's final hash above contains that correction.

Final frozen-source independent regression completed at19:08 UTC:28,800 decision checks passed with the exact C/Python hashes in section12, including the unsafe-support/zero-empirical-mass guard. The entire final TXT was reread against those sources. No unresolved substantive report/proof/reference-code issue remains. This signoff is conditional mathematical and executable-model review, not physical assurance certification.

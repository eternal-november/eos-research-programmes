# Discovering the telemetry interactions needed for stopping assurance

Proof and example candidate, 29 October 2026. This is a quantitative representation-discovery example, not a deployment certificate for a physical robot. Marginal optimization and concentration inequalities are standard tools. The point is to expose the task-dependent interface and evidence obligations without choosing a convenient finite catalogue of complete environments.

## Plain-language abstract

A robot can have acceptable braking measurements and acceptable communication-delay measurements separately, while their bad cases coincide often enough to make a maneuver unsafe. A useful environment description must preserve that coincidence. Merely naming a braking component and a network component is insufficient. This example constructs the risk bound from the telemetry interactions that are actually measured, identifies a missing joint distinction when the bound fails, and specifies a concrete additional logging interface that would resolve that distinction. The uncertainty set contains every joint distribution consistent with the measurements, rather than a finite list of hand-picked mechanisms. A nonlinear stopping envelope connects the signals to the physical task, while a persistent stochastic example shows that arbitrarily much separate local history can still miss a relevant joint interaction. The assumptions connecting telemetry to hazard, sampling to deployment, and sensors to executable interfaces remain explicit.

## 1. A physical envelope rather than a complete mechanism grammar

Fix a controller that enters a passage at speed v>0 and brakes after a reaction interval tau. Let b>0 be an effective lower bound on braking deceleration throughout that stopping maneuver, and d an allowed stopping distance strictly inside the available free distance, leaving a declared positive clearance reserve. Under the stated constant-bound envelope,

    required distance <= v*tau + v^2/(2*b).

Indeed, reaction contributes at most v*tau under the stated speed bound; integrating deceleration at least b from speed v gives distance at most v^2/(2*b). A clearance certificate therefore requires v*tau+v^2/(2*b)<=d. If the inequality fails, this envelope does not certify safety; it does not by itself prove a collision occurred. When the model stipulates constant speed during reaction and exactly constant b during braking, the expression is the actual stopping distance and its exceedance is the modeled hazard event.

Calibration can enter the hazard guard directly. If |tau-measured_tau|<=e_tau, b>=measured_b-e_b>0, and the allowed stopping distance with that positive reserve is at least d_low, define the observable conservative event by v*(measured_tau+e_tau)+v^2/(2*(measured_b-e_b))>d_low. Under the physical envelope and calibration event, an actual collision is contained in this conservative event. If calibration can fail with probability at most eta, the collision bound is the conservative-event risk plus eta. A statistical confidence failure probability delta for estimating that risk is a different quantity and must not be silently treated as eta. None of these calibration promises is inferred from arbitrary readouts alone.

This distinction must be retained in risk claims. A conservative envelope gives an upper bound on collision probability by the probability of envelope violation, provided the speed, braking, geometry and actuation assumptions hold. It cannot certify unrepresented hazards, such as a newly entering pedestrian, nor validate its own physical assumptions from unrelated data.

Latency and braking may have arbitrary dependence caused by temperature, processor load, power availability or other persistent conditions. No independence premise is imposed. For two binary severity levels, take v=2, b in {1,2}, tau in {0,1/2}, and d=5/2, in consistent chosen units. The four stopping distances are 1,2,2,3. The violation occurs exactly when delayed reaction and weak braking coincide. These numbers are a mathematical calibration, not recommended operating parameters.

If each adverse condition has probability 1/10, separate marginals permit joint violation probability anywhere from 0 to 1/10. Assuming independence would produce 1/100 without evidential support. A joint telemetry channel that estimates the same-maneuver coincidence can reduce this uncertainty without reconstructing the thermal or network architecture causing it.

## 2. What is being discovered

The available primitive telemetry streams and their calibration/read permissions are supplied, but the grouping of those streams into task-relevant joint interfaces is not. A proposed interface is an executable logger or finite encoder with a declared scope, synchronization rule, bit cardinality and computation. The discovery question is which scopes and distinctions suffice for a requested risk bound.

A patch observation can record a joint event on a subset S of the streams. Separate records of streams from different maneuvers are not the same interface as a synchronized record from one maneuver. A triple coincidence cannot be inferred by silently joining independent pair records. Time identifiers, persistent operating context and sensor aliases must be shared.

The learned object is consequently not just a partition of variable names. It is a family of local observation functions and a certificate that their jointly retained information supports the required hazard bound. Overlap is allowed and its dependence is retained. Internal causal mechanisms can remain unresolved when they do not affect that bound.

For one operational context, let Omega be the finite set of calibrated telemetry scenarios, or a finite partition at a declared sensor resolution. Let h(omega) in {0,1} indicate the modeled hazard or envelope violation. Measurements constrain expectations of actual executable patch functions phi_k. Write

    U = { p>=0 : sum p=1, l_k <= E_p phi_k <= u_k for every k }.

This is a set of ALL joint laws consistent with the specified evidence, not a list of selected environment models. It can contain strong common-cause dependence and nonunique mechanisms. The robust question is

    R = max_(p in U) E_p h.

An empty U is inconsistent evidence/calibration, not automatic safety. A nonempty U with R<=alpha yields assurance for every law in U, conditional on the physical envelope and the deployment law belonging to U. If R>alpha, it may mean actual risk, insufficient evidence, insufficient interface resolution or an overly conservative envelope. The witnesses below distinguish some of those cases rather than collapsing them to a generic failure.

## 3. Quantitative local certificates and their interpretation

A checkable upper certificate is a pointwise inequality

    h(omega) <= c + sum_k lambda_k phi_k(omega)

for every admitted calibrated scenario. Then

    E_p h <= c + sum_(lambda_k>=0) lambda_k u_k
                 + sum_(lambda_k<0) lambda_k l_k

for every p in U. The proof is linearity and the sign-sensitive interval bounds. The support of lambda identifies which telemetry interactions this certificate needs. Unused patch statistics are unnecessary for this certificate, although another certificate could use a different set.

For finite Omega, linear-programming duality supplies an optimal such certificate with the appropriate normalization constant and both upper/lower multipliers whenever the feasible probability polytope is nonempty. This is a classical marginal optimization theorem, not a new theorem about decomposition. Its use here is constructive: select an implementable family of patch functions, solve for a risk certificate, and expose either its local supporting interactions or an adverse compatible joint law. Searching a minimum-cost family is a separate combinatorial problem; no cheap optimizer is presumed.

A failed certificate search must not be interpreted as proof that the chosen interface is intrinsically inadequate unless the optimization over that interface is complete. When the primal robust maximum exceeds alpha, an explicit maximizing or sufficiently adverse p is an informative countermodel. Two laws with the same retained statistics and different safety verdicts certify that the retained evidence cannot decide the task. They identify the missing joint distinction; they do not assert which law governs the actual environment.

The pointwise inequality can itself be hard to verify. Sparse physical wiring does not bound the interaction width of all telemetry functions and hazard terms. The small examples below have algebraic inequalities that can be checked directly; a general compiler must charge the support width, numeric bit lengths and size of the pointwise proof.

## 4. A three-contribution example where pairs do not suffice

Let X_1,X_2,X_3 be three binary stopping-distance penalties: for example an extra sensing delay, an extra communication delay and a braking-distance penalty. In this explicitly discretized envelope each penalty contributes one unit and the clearance reserve is between one and two units. Thus violation is

    h=1 iff X_1+X_2+X_3>=2.

The units and threshold describe a model envelope, not three independent causes. Let the measured single and pair moments be

    P(X_i=1)=1/10,
    P(X_i=X_j=1)=1/100 for each i<j.

Every compatible joint law is parameterized by q=P(111) in [0,1/100]:

    p111=q,
    p110=p101=p011=1/100-q,
    p100=p010=p001=2/25+q,
    p000=73/100-q.

These nonnegative entries sum to one and yield the displayed moments. Conversely, inclusion-exclusion forces these expressions. Therefore

    P(h=1)=3/100-2q,

so the exact pair-information robust risk is 3/100. For a requested threshold alpha=1/50, pair observations cannot certify safety. The compatible q=0 law has risk 3/100, while q=7/1000 has risk 2/125=0.016. This pair of laws is an explicit informative failure certificate.

A synchronized triple-event interface can estimate q. The identity

    h = X_1 X_2 + X_1 X_3 + X_2 X_3 - 2 X_1 X_2 X_3

holds on all eight scenarios. It is an exact local-potential certificate. If each pair moment is known within epsilon of 1/100 and q within epsilon of 7/1000, the robust upper bound is

    P(h=1) <= 0.016 + 5*epsilon.

At epsilon=1/2000 this is 0.0185, below alpha=0.02. All joint laws in that uncertainty set pass the stated modeled risk test. The certificate does not choose the favorable q-law and discard alternatives; it bounds the entire set.

The interaction required here is not simply positive correlation. Increasing the triple coincidence while keeping pair moments fixed makes the pair events overlap more and REDUCES their union. A decomposition retaining only separate or pairwise risk summaries misses that distinction. The exact polynomial identifies the common triple event that must be represented in this certificate.

Executability is concrete: each logger tags its bit with the same maneuver ID; an allowed fusion node computes the three pair ANDs and the triple AND; the estimator retains their empirical counts. If the available system cannot align all three records, or policy/hardware forbids any node from computing the triple event, this certificate is unavailable. Declaring a mathematical ternary relation does not install that interface. A secure distributed protocol would be a different explicitly costed implementation, not a free substitute.

## 5. Sampling uncertainty is not free

A small nonvacuous validation illustration uses the two-signal stopping case, not the triple-moment precision demand. Suppose an executable same-maneuver AND logger is selected and then evaluated on N=300 independent validation maneuvers in the declared deployment context. A CONSTRUCTED example histogram is 240 records with neither condition, 30 with delayed reaction only, 30 with weak braking only, and zero with both. This is hypothetical validation evidence, not a claim that physical data were collected. The marginals are each 1/10, so unaligned marginal records alone still permit 1/10 violation risk.

For a predeclared family of at most K=7 candidate event statistics, a zero count gives the simultaneous one-sided bound 1-(delta/K)^(1/N), by the exact probability (1-p)^N of zero successes and a union bound. At delta=1/20, this bound is below 0.017 and therefore below the illustrative risk budget 0.02. The exact rational check is (983/1000)^300<1/140. Consequently all laws in the resulting confidence set satisfy the modeled risk budget, on the confidence event. The numerical budget is illustrative, not a recommended safety level. The law must match deployment; data from a different controller or unrepresented operating regime do not qualify.

There are two different input situations. In a REPRESENTATION GAP, aligned raw validation records already exist, but the current view retained only separate marginal counters. A legally available program can recover the same-maneuver AND count from those retained raw records; the construction changes what the representation retains and can certify the bound immediately from the existing evidence. The simultaneous K-function confidence event, or a validation split independent of selection, must cover this choice. In an EVIDENCE GAP, only unaligned marginal records were acquired and no same-maneuver correspondence is available. The two compatible joint laws remain possible. An executable AND logger is then a proposal for additional measurement, not a risk certificate. No fresh uncertainty interval is invented merely because that observer can be written.

The new bound exists only AFTER the synchronized logger actually supplies these validation records. It cannot be computed from the old unaligned marginals. If arbitrary local preprocessing is allowed at a node with both signals, logging the hazard AND directly is a simpler sufficient representation than retaining a whole joint table. Likewise, the three-penalty example can use a direct hazard counter when a node can legally compute it. The claim is that a JOINT TASK DISTINCTION must be observed, not that a particular triple coordinate or full joint distribution must always be stored. Distributed input access and message timing still have to implement that computation.

If N validation maneuvers are independent draws from the same deployment-context law, each phi_k is bounded in [0,1], and K queried statistics were fixed independently of that validation sample, Hoeffding plus a union bound gives simultaneous intervals of radius

    epsilon = sqrt(log(2K/delta)/(2N))

with probability at least 1-delta. Alternatively, simultaneous confidence bounds over a declared finite function family may support adaptive interface selection from that family. Reusing data to select arbitrary patches and then applying unadjusted fixed-query intervals is invalid.

The numerical three-event certificate with epsilon=1/2000 is statistically demanding under this conservative distribution-free bound. With K=7 and delta=1/20 it requires at least 11,269,580 independent validation records. This is an honest cost, not a claim that the example is deployment-ready. Variance-sensitive or sequential methods can improve a justified sampling analysis, but no such improvement is assumed here.

For a recurrent deployment process, independence cannot be silently inferred from repeated logging. One can instead obtain valid context-conditional confidence sequences under an appropriate martingale model, use justified mixing bounds, or use separately validated uncertainty intervals. Each is an additional evidence theorem. Unseen contexts remain uncertified. A finite-horizon union bound from conditional per-step risks is available only when those conditional bounds hold under the controller's actual adaptive histories. Marginal risk measured under one logging policy does not establish this.

## 6. Persistent hidden interaction can defeat all proper-patch histories

Here is a structural control showing that merely collecting more separate local histories need not resolve a missing joint interaction. It is not the main physical model and is deliberately algebraic.

For m>=3, let V_t in {0,1}^m stay in either the even-parity or odd-parity coset. Initialize uniformly in that coset. At each update add modulo two an independent increment that is zero with probability rho and otherwise uniform on the even-parity subgroup, where 0<rho<1. The two candidate processes are stationary and recurrent, with the same update rule but different persistent parity class.

For each FIXED proper coordinate subset, its entire finite-history law is the SAME in the two processes. The acquisition contract here is separate fixed-patch records without cross-patch alignment from the same trajectory. To prove this, projection of either parity coset onto a proper subset is uniform, and projection of the even-parity subgroup is uniform on that subset. The projected transition is therefore rho times identity plus (1-rho) times uniform refresh, independent of the parity class. This equality holds at all horizons, not just for isolated moments.

For m=3 and hazard at least two active penalties, the even-coset process has instantaneous hazard probability 3/4 and the odd-coset process 1/4. All one- and two-stream histories nevertheless agree. A shared rare activation process A_t, independent of V and with the same stationary law in the two candidates, can set the observed penalties X_j(t)=A_t V_j(t). Every proper-patch history law remains equal, while the instantaneous risks become P(A_t=1)*3/4 and P(A_t=1)*1/4. The activation process can itself be persistent. This turns the distinction into a rare-event example without deleting the common cause.

A synchronized full patch distinguishes the two candidate laws. No amount of additional separately sampled FIXED-proper-patch histories can do so. This does not cover every acquisition protocol: aligned overlapping records can reconstruct the full tuple, and for rho>0 changing the observed patch within one trajectory can exploit temporal correlation to reveal parity. Such switching is another potentially cheaper observation interface, not evidence that the old fixed-patch data already contained the distinction. At rho=0, new vectors are independent uniform draws within the persistent parity coset; then even adaptively selecting one proper patch per time fails to reveal the parity class, provided no same-time records can be combined into a full patch. Local temporal autocorrelation is absent in that variant, although the hidden parity mode is persistent. Thus failure reports must name the actual permitted observation protocol. For general m, a hazard selecting a full parity-sensitive event yields an unbounded interaction-order obstruction under that protocol. This does not imply that every realistic environment has such high-order coupling.

## 7. Distinctions within a channel can matter too

Binary good/bad labels are not generally sufficient for the continuous stopping envelope. Let tau and b range over nontrivial intervals with b bounded away from zero. The boundary

    v*tau + v^2/(2*b) = d

is curved. A local latency bin can contain two values that lie on different sides of this boundary for the SAME permitted braking value. If the interface identifies those latency values, another component cannot decide the exact envelope verdict from that message.

The distinction is executable only if the latency sensor's resolution and calibration permit it. With interval-valued calibration, evaluate the worst-case envelope over the measurement cell. A cell entirely below the threshold is certified; a cell crossing it contributes uncertainty or conservative violation mass. Refinement should target cells whose possible mass prevents the desired risk certificate, rather than reconstructing unrelated physical variables.

There is no general finite exact independent quantization for every point on a continuum of such crossing thresholds. A support margin gamma>0 away from the boundary changes the problem. The score is Lipschitz on b>=b_min with constants v in tau and v^2/(2*b_min^2) in b. A grid whose total worst-case score variation is below gamma classifies every supported cell. This states exactly which margin and sensor precision make finite representation sufficient. Statistical evidence for the margin and support remains separate.

## 8. What this example establishes and leaves open

This class replaces a finite catalogue of complete mechanisms with a nonparametric family of telemetry couplings and explicit physical/task envelopes. It makes representation discovery concrete: choose joint observation scopes and within-channel distinctions that support a robust quantitative certificate, or return compatible countermodels and the interface distinction they disagree on. It includes recurrent common causes, executable logging requirements, sensor precision and statistical costs.

The elementary optimization mechanisms are classical. The example alone does not prove the programme's general categorical integration, efficient minimal-interface synthesis, arbitrary physical model validation or a safe exploration policy. Its purpose is to require any new decomposition theorem to handle evidence-relative necessity, shared interactions and robust assurance together, rather than accepting one convenient model or merely checking that a proposed decomposition exists.

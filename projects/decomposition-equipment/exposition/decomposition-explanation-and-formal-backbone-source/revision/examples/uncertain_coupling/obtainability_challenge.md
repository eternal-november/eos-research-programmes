# Unknown linear coupling from permitted experiments

2026-10-30. Constructive challenge note. The results below are elementary finite-field linear algebra, learning of subspace support, and experiment indistinguishability. No novelty claim is made. They challenge a fixed source-grouping premise, but retain a declared uniform affine/linear noise class and physically justified experiment/production transport.

## 1. Unknown overlap rather than a supplied partition

Fix a known finite-dimensional port space X over F_q. On each natural event the plant emits a vector uniformly distributed on an UNKNOWN subspace U<=X, or more generally an UNKNOWN affine subspace u0+U. Equivalently, some unknown matrix maps independent uniform latent field elements to the port values. The latent dimension, incidence and basis are not supplied; different latent bases are observationally equivalent. This allows overlapping shared sources and higher-order parity relations that pairwise covariance cannot detect.

The premise is still substantial: one knows the relevant global port scope, uniform finite-field source class, natural fresh-event semantics, and the relation between calibrated and operational port values. Safe gate/drain and noninvasive sensing need independent physical justification. This is not architecture learning without any model class.

A permitted probe i observes A_i x for a known linear map A_i:X->Y_i. Coordinate projections are a special case; physically available parity/readout circuits may give other maps. The map is fixed before the fresh event. If several reads may revisit the SAME event, their complete cumulative stacked map is one probe for adequacy and impossibility purposes. Replacing those cumulative experiments by separate fresh marginals is invalid.

## 2. Positive maximal extension from projected supports

Suppose the exact observed support is U_i=A_i(U). In the linear case define

    V = intersection_i A_i^{-1}(U_i).

Then U<=V and A_i(V)<=U_i by construction. The reverse inclusion follows from U<=V, so A_i(V)=U_i for every i. Uniform measure on V therefore has EXACTLY the measured probe laws: every fiber of a surjective linear map has equal cardinality. A basis of V gives a positive normalized realization by sampling dim(V) independent uniform field elements and applying the basis matrix.

This is a realization choice, not a claim that V is the true physical support. The true U may be a proper subspace of V. No hidden source basis needs to be identified. With affine supports B_i, define the maximal affine extension B=intersection_i A_i^{-1}(B_i). Nonempty B projects to every B_i if the data have a common generating affine support; the same uniform-fiber proof applies.

For arbitrary proposed data, check nonemptiness and A_i(V)=U_i explicitly. Merely intersecting independently estimated supports can erase a claimed marginal. When the check passes, uniform V is a jointly positive realization of all supplied support laws. For inherited exact data it passes automatically.

## 3. Exact new linear-context criterion

Assume V is nonzero and all learned projection maps pi_i=A_i|V:V->U_i are surjective. Let

    C = {S<=V : pi_i(S)=U_i for every i}.

These are precisely the supported linear source laws after the exact probe supports, with uniform distribution on each S. Let Q:V->Z be a requested new linear interface/query. Write R_i=im(pi_i^*)<=V* and R_Q=im(Q^*)<=V*.

**Theorem.** Every S in C has Q(S)=Q(V) if and only if

    R_Q subset UNION_i R_i.                            (1)

This is a SET UNION, not the linear span of all observed row spaces. The zero functional belongs to every row space; the criterion can equivalently quantify over nonzero chi in R_Q. Empty probe families use the separate trivial case R_Q={0}.

**Proof, necessity.** Suppose a nonzero chi in R_Q lies outside every R_i. Put H=ker(chi)<=V. For a surjection pi:V->W, pi(H)=W iff chi does not factor through pi. Indeed, if chi is nonzero on ker(pi), every v can be adjusted by a kernel vector to lie in H without changing pi(v); if chi vanishes on ker(pi), it factors through pi and pi(H) is a proper hyperplane of W. Thus H preserves every probe projection. Since chi factors through Q, Q(H) is a proper subspace of Q(V). Therefore H and V are positive, probe-indistinguishable witnesses with different Q laws.

**Proof, sufficiency.** Suppose S in C has Q(S) proper in Q(V). Choose a nonzero functional lambda on Q(V) annihilating Q(S), and let chi=lambda Q. Then chi is nonzero and vanishes on S. By (1), chi factors through some pi_i. Surjectivity pi_i(S)=U_i would force that factor to vanish on all U_i, hence chi=0, a contradiction.

Since uniform linear measures push forward uniformly, equality of supports here is equality of the entire requested joint distribution. The theorem is therefore a positive stochastic interface criterion, not merely agreement of one expected reward. It can be checked by enumerating the q^rank(Q) row-space elements and testing membership in the learned R_i. No efficiency superiority is claimed.

### Affine version

For nonempty maximal affine B=b0+V, use its direction space V and the linear parts pi_i, Q. The same condition is necessary and sufficient for all supported affine subspaces S of B with the same probe images to have the same Q image as B. An uncovered nonzero chi gives an affine hyperplane chi(x-b0)=c; its image under every pi_i is unchanged, while its Q image is a proper affine hyperplane. In particular distinct c can be indistinguishable yet demand incompatible mission decisions.

### Adaptive contexts and a required qualification

If a finite causal program may choose maps based on earlier public outputs, preserving the full joint law for every complete cumulative map along its syntactic paths is sufficient to preserve the program's transcript law, using ordinary induction. Stacked maps must include all semantically relevant timing/resource/hazard outputs, not only visible controller values.

The set-union criterion is exact for a full linear-query API in which each listed cumulative Q can be observed over all its outcomes. It need NOT be necessary for a particular value-guarded adaptive program: a matrix appearing only after a specific prior-value guard can demand less than its unrestricted Q law. Exact mission-relative treatment then works with the actual guarded cylinder tests or conditional affine slices. Do not silently turn whole-API adequacy into necessary mission compatibility.

## 4. Finite observation cost

A fresh sample of A_i x is uniform on the r_i-dimensional subspace U_i. After m_i independent fresh events let Uhat_i be the span of the observed values. It is always contained in U_i. Failure to span U_i implies all samples lie in some hyperplane, so

 Pr[Uhat_i != U_i] <= ((q^r_i-1)/(q-1)) q^(-m_i)
                     <= q^(r_i-m_i)/(q-1).            (2)

This union bound can be conservative but is exact enough for finite guarantees. With K probes, using

 m_i >= dim(Y_i) + ceil(log_q(K/delta))

is sufficient for simultaneous correctness with probability at least 1-delta, for q>=2. Each m_i count is charged to fresh physical activations, setup, logging, drain and arithmetic. In the affine case choose one observed anchor and span m_i-1 differences; the same bound uses m_i-1. Conditional on the first anchor those differences are independent uniform direction-space samples.

The learned maximal support Vhat must pass the projection check from Section 2. On the simultaneous full-span event it equals the exact V and passes. Off that event, no exactness claim is made even if the check passes. A finite-sample certificate therefore carries the explicit delta error allowance.

For data-dependent probe schedules, a fixed pre-event choice is compatible with conditional freshness, but optional stopping needs simultaneous-in-count bounds or an explicit fixed design. The displayed fixed-count theorem is sufficient and does not rely on adaptive estimation.

## 5. Useful completion rather than accepted-run safety

For a declared finite production context class, use (1) to verify all required linear API queries. Compile uniform Vhat into an actual positive stochastic model, while the real controller continues to act on the true plant. If on exact learned data the same capability-matched program succeeds uniformly for the required unknown supports, and all calibration/checking/production/tail costs fit the budget, then on the full-span event that certificate is available and correct. With a separate valid production risk alpha and calibration risk rho, total missed-or-unsafe probability is at most delta+alpha+rho, PROVIDED acceptance/completion on the full-span event is proved. Refusal outside that event counts as missed completion; without that positive acceptance premise add the no-certificate probability explicitly.

This clause alone is a composition of established facts, not a substitute for a concrete mission and its capability/physical proof. The main research construction must instantiate it rather than assume the desired safe mission exists.

## 6. Genuine policy impossibility, not merely different interface laws

A different Q distribution by itself does not prove mission incompatibility. The following witnesses do.

**Affine binary witness.** Let nonzero chi be outside the row space of EVERY legally available complete cumulative probe map, not merely those already executed or learned. If an unperformed legal probe covers chi, the conclusion is only that more experimentation is needed; it is not impossibility. The two source laws uniform on H0={chi=0} and H1={chi=1} give the same law under every permitted probe. Fresh adaptive experiments cannot distinguish them: their next-outcome kernels agree after every history. Let the production mission require choosing b in {0,1} before its source event, and succeed exactly when chi(x)=b. Each informed world has a sure-success action. Any allowed history-based randomized policy has the SAME distribution of b in both worlds, so its worst-world failure probability is at least 1/2, attained by a fair choice. This is a concrete compatibility limit for the stated observation and mission regime, not a failed checker.

**Linear-only binary witness.** Suppose two independent functionals chi1,chi2 are each uncovered by EVERY legally available complete cumulative probe map. Worlds uniform on ker(chi1) and ker(chi2) are probe-indistinguishable. Action j succeeds when chij(x)=0. In its own world it succeeds surely; in the other it fails with probability 1/2. Every policy's worst-world failure is at least 1/4, attained by a fair choice between actions. This assumes the allowed cumulative probe language does not add a query containing either missing contrast.

Safety of the experiments is unaffected by the algebra only when the declared physical probe guard really masks these loads uniformly across both worlds. If that guard itself is uncertain, this example does not validate it; it is a remaining acquisition premise.

## 7. Budgeted adversary with parity-only probes

A simple structural lower bound illustrates how a small source mechanism can be hard to identify in a limited observation regime. Let X=F2^d, and allow only scalar parity probes a(x) on fresh events. Consider source U=X versus U=ker(ell) for an unknown nonzero ell. Every nonzero scalar probe except ell is fair under BOTH laws; probe ell is fair under X and identically zero under ker(ell). Therefore, until the algorithm queries the hidden ell, its transcript distribution is identical to the full-space source.

A deterministic fixed set of fewer than 2^d-1 distinct parity directions cannot rule out all hidden hyperplane couplings. For adaptive/randomized algorithms with a bounded number k of queried directions, choose ell uniformly among the 2^d-1 directions, independently of the algorithm's private coins and a full-space reference execution. In that reference execution every nonzero parity outcome is a fresh fair bit. The reference set of queried directions has size at most k and is independent of ell. Couple the actual ker(ell) execution to the reference, using identical private coins and outcomes until the first query of ell. Every earlier query has the same fair outcome law in both worlds, so the executions and their next queries agree up to that first hit. Consequently the event of a first hit is exactly that ell belongs to the reference queried-direction set, and its average probability is at most k/(2^d-1). This is an unconditional coupling statement; it does NOT claim that adaptively selected transcript laws remain identical after conditioning on no hit. Sampling the same direction more often can resolve stochastic zero-versus-fair ambiguity after a hit but cannot improve this coverage limit. This is a standard indistinguishability/query-cover argument, not a new cryptographic result.

This lower bound concerns certification of the entire possible parity interface. A mission needing only one known parity may require only that one probe; universal coupling identification is not a mandatory admission test for a narrower mission.

## 8. What this removes and what remains

The source partition/linear overlap is not given: the experiment supports derive a basis-free positive realization and an exact boundary for new linear contexts. Higher-order unknown couplings are explicitly retained, and new contexts can fail despite all pairwise evidence.

Still supplied are the finite-field uniform/affine source class, known observable probe maps and port scope, natural event freshness, noninvasiveness, calibration/production transport, and physical probe/gate/drain safety. The criterion is finite linear tomography/coding geometry; its research significance is a precise operational test and obstruction, not established novelty. General nonuniform sources, unknown nonlinear coupling, unknown event boundaries, arbitrary memory and transport change remain outside this theorem. No claim is made that these assumptions are experimentally proved by the support-learning procedure.

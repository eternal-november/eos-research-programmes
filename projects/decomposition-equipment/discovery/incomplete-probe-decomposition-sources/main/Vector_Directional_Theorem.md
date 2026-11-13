# Main theorem, vector form: quotient discovery from response subspaces

This is the natural generalization of Directional_Quotient_Discovery.md, covering the matrix-gauge stress family. Its causal, sensor-calibration, context-coverage, positivity, and finite-data qualifications are inherited explicitly; they do not disappear in the notation below.

## 1. Shared vector effect, unresolved law
For each instrumented finite patch i, flatten local context/output coordinates (c,y) into R_i rows. The conditional response is

  K_i(y|c,z)=B_i(y|c)+F_i[(c,y),:] z,

with F_i an R_i by r matrix, sum_y F_i[(c,y),:]=0, and nonnegative K_i on the admitted source support. All F_i are unknown. Local B_i and F_i may depend nonlinearly on old patch state and observed input histories. The only linearity is in the retained shared effect z. Conditional on full past/source state and challenge regime, the current shared z has mean zero and covariance I_r (or a known positive scalar multiple of I_r absorbed into the residual). Patch fresh innovations are conditionally independent given z and contexts. One common z is drawn per whole update, not once per factor.

A hidden persistent process H may control the higher conditional moments of z, as long as these first two conditional moments hold POINTWISE given every full past/history and H. Thus the source need not be IID or identified. This condition is stronger than marginal mean/covariance and must be in the universe.

Paired simultaneous readouts identify

  D_ij = F_i F_j^T.

For each affected i, assume some observed neighbor j has rank(F_j)=r and rank(F_i)=r. Then range(D_ij)=range(F_i). The response subspace V_i is therefore discovered directly from observations. More generally rank-deficient nodes can be covered if the vertically concatenated partner response maps span all effect directions acting on i; the simple theorem uses full rank.

This is not completeness of a regime-to-effect operator. Regimes may all have exactly the same first two source moments and fail to identify the source. It IS a local response-rank/relevance assumption and can fail if an effect influences only an unpaired patch. Unobserved hidden directions outside the declared affine family are not certified absent.

## 2. Main discovery theorem: conditional components first, autonomy second
A partition P of X_i is a valid conditional component if it preserves the task and, whenever x~P x', for every input u and next block B,

  B_i(B|x,u)=B_i(B|x',u),
  (L_(x,u,B)-L_(x',u,B))(V_i)=0.

The second equation says that the response contrast rows agree for EVERY unresolved shared effect, without choosing a gauge or identifying source amplitudes. It is invariant under F_i->F_i T for every invertible T.

Algorithm: start from the task partition P0. At each step split old-state blocks by the complete vectors of (a) B_i next-block response probabilities and (b) the corresponding aggregated rows of ANY basis U_i of V_i, over all input histories and current next-state blocks. Repeat to stability.

**Theorem 1 (conditional discovery).** The algorithm terminates after at most |X_i|-|P0| strict refinements and returns the unique coarsest task-preserving deterministic quotient whose conditional response is well defined for every admitted effect z. It is the same quotient for every compatible invertible gauge and positive source realization.

**Proof.** At termination the two equality conditions hold, so each quotient row is well defined conditional on z. Let R be another valid task-preserving quotient. Inductively R refines Pj. Equality of R-block baseline and contrast responses for R-equivalent old states implies equality of Pj-block responses, because each Pj block is a union of R blocks. Hence R-equivalent old states are never separated by the new split. R refines every Pj and therefore P*. The quotient is valid, so it is coarsest. Finitely many states bound the number of strict splits. QED.

The shared effect is a RETAINED LATENT INTERFACE in this conditional theorem. Its source realization, coordinate gauges, temporal process, and alignment across all components remain in the positive assembly witness. Conditional closure is not autonomy, observed access to z, or a physically implemented sensor wire.

**Corollary 2 (autonomy decision).** The discovered P* is exterior independent iff every block-sum functional L_(x,u,B) annihilates V_i. If this fails, no finer task-preserving deterministic exterior-independent quotient exists: each P* block is a union of blocks of any valid conditional quotient, and sums of zero contrast rows cannot give a nonzero contrast. Thus the same procedure distinguishes a certified autonomous component from a useful conditional component that necessarily retains hidden influence within the declared deterministic quotient class.

**Observed boundary.** With P* fixed, group input histories when BOTH baseline quotient rows and contrast-basis quotient rows agree for every quotient state. Refine this input equivalence to a congruence under the actual history shift update. The result is the coarsest recursively maintainable observed-input summary supporting this conditional component. If contrasts vanish, it reduces to the autonomous boundary. Source information is NOT included for free in the observed input register: it remains an explicit latent source boundary. Input symbols, state access, initialization, and source alignment all retain their own costs.

A basis U_i for V_i is sufficient for every test; no full effect inverse or hidden-state enumeration is required. A certificate exposes measured D_ij, recovered basis with rank witness, response-equality equations, a refinement trace, and the separate autonomy flag. Finite numerical certificates require error and rank margins, not exact float zero assertions.

## 3. Matrix compatibility across a connected cover
Write F_i=U_i A_i with U_i a fixed discovered full-column-rank basis and A_i invertible. Pair laws determine

  C_ij=U_i^+ D_ij (U_j^+)^T=A_i A_j^T.

All local candidate A_i must solve these SAME edge equations. If A and A' solve them, put A'_i=A_i T_i. Each edge implies T_i T_j^T=I, hence T_j=T_i^-T. On a connected bipartite graph, all T_i equal one common T on one side and T^-T on the other. An odd cycle forces T=T^-T, i.e. T is orthogonal. This classifies residual coordinate/amplitude gauges before response positivity is imposed. Positivity can cut this gauge family substantially. Orthogonal ambiguity is a source-coordinate relabeling only if the source-law universe is closed under the same transformation; do not discard it without checking.

Cycle inconsistency is an explicit obstruction to global assembly even when every edge admits positive local explanations separately. A spanning-tree propagation of A_i followed by non-tree edge checks is a constructive consistency procedure conditional on a root factor; testing whether an admissible positive root exists remains a separate feasibility problem. No claim is made that positivity reduces to unconstrained matrix factorization or is polynomial in all variable parameters.

## 4. Persistent higher-order uncertainty
Suppose the source has a hidden process H_t and, given full pre-update history and H_t, z_t is sampled from a distribution mu_(H_t) with common mean0 and covarianceI. Its support can be fixed and finite; the laws may differ in third/fourth moments. H may be persistent or refreshed and need not be inferred from singles/pairs.

For a fixed set of one or two patches whose own contexts are closed under their observed histories and specified external inputs, conditional one-step marginal laws depend only on the common first two moments. Consequently their entire path laws, under the same initialized local history and same adapted input policy, are identical across source processes by induction. THIS conclusion requires that those retained contexts are sufficient for the projected histories. If a retained patch's next kernel depends on an unobserved neighboring state whose law differs across source worlds, one-step moment identities alone do not prove pair-history equivalence. The growing family must either provide the required context closure, retain the input histories explicitly, or state only local conditional-law equivalence.

Higher simultaneously observed sets can depend on higher moments: the product of k affine response factors has degree k in z. Thus four-way tests can resolve different fourth moments even where every isolated pair history agrees. Persistent source memory can likewise appear in cross-time products of such higher-order records. This is genuine residual process ambiguity, not independent parameter intervals at each time.

## 5. Scope of the decomposition
A learned task component is a quotient of an instrumented patch; physical module ownership is not automatically inferred. Its observed input boundary is discovered from Q response equality and recursive history closure as in the scalar note. It is a conditional inward component retaining the shared hidden effect; it is exterior independent only when the separate autonomy flag passes, and then only on the declared effect support. A positive whole implementation retains one common source process and dependent residual fibers. Neither a supplied sensor patch nor a source-factorization matrix is itself a discovered physical subsystem.

The theorem identifies useful autonomous factors even while the larger mechanism remains nonidentified. It does not claim all useful decomposition types are identifiable, nor that the inferred quotient has minimal physical memory across arbitrary architecture/timing changes. Alternative conditional components may be retained with their common source/gauge witnesses, but cannot be certified autonomous just from their averaged response.

## 6. Conditional numerical stability (not a finite-data implementation)
Let a witnessing true residual matrix D have rank r and smallest nonzero singular value at least s>0. Suppose the estimated residual has operator error ||Dhat-D||<=epsilon<s/4. Let P and Phat project onto the true column space and the leading r-dimensional estimated column space. Then

  ||Phat-P|| <= 2 epsilon/s.

Indeed, the (r+1)st estimated singular value is at most epsilon, so ||(I-Phat)D||<=2epsilon. Multiply by the true rank-r pseudoinverse to obtain ||(I-Phat)P||<=2epsilon/s. For equal-rank orthogonal projections this is the sine of the largest principal angle and equals their operator-norm difference.

For any tested aggregate linear functional ell, the error in its subspace-annihilation score is therefore

  | ||ell Phat|| - ||ell P|| | <= ||ell|| 2epsilon/s.

A next-block sum over b outcomes has ||ell||=sqrt(b); a difference of two distinct context/block sums has sqrt(2b). If every nonzero tested score is at least gamma, choosing a threshold gamma/2 is valid when the displayed error is <gamma/2. This is a basis-invariant margin; raw coefficient equality in an arbitrarily conditioned basis is not.

Similarly an entrywise baseline row error eta gives at most b eta error in a block sum and 2b eta in a difference. A nonzero baseline-separation gap and these subspace gaps jointly stabilize every partition split and the separate autonomy flag. Exact zero is not uniformly decidable with finite noisy data in the absence of such gaps.

Obtaining epsilon and eta from readouts requires calibrated observation-law inverse bounds, context probability floors, independent windows or a declared mixing/concentration argument, and enough samples to distinguish sensor ranks. The earlier three-view calibration theorem can supply these bounds under its unchanged assumptions; this note has not implemented that finite-data pipeline. Arbitrarily persistent higher-moment sources do not imply a mixing rate, even when their first two moments are fixed.

For a finite list of independent bounded outcome experiments, entrywise multinomial concentration and a union bound give simultaneous table bounds, and Frobenius norm bounds operator error. The resulting sample cost depends on the number and size of those tables and all conditioning gaps. No general polynomial inference claim follows for unbounded patch sizes, unknown arbitrary input history, or vanishing response rank.

## 7. Persistent-source dynamic closure and charged residual information
Pointwise well-defined conditional rows Q_i(.|q_i,u_i,z) are NOT alone a closed Markov model on (q,H). If the persistent source transition H_{t+1} depends on discarded local microstate, then two microstates with the same q can induce different future source laws, even though their present quotient response rows agree. To claim closure of a retained (q,H) system, require the source transition itself to factor through the retained q, declared inputs, and H. That is an additional outward-sufficiency condition, not a consequence of Theorem 1.

Without that condition, exact whole-process realization retains the discarded dependent fibers in the shared remainder/source process and preserves whatever fine-state outgoing information its transition requires. The information, state storage, communication, and initialization are charged. Conditional disintegration then preserves the original joint execution but does not establish a physically isolated quotient-source subsystem. The fresh-IID-source matrix-gauge family avoids this particular source-feedback obstacle: with a declared local-context update and retained initial law, its positive product transition gives the full closed whole model directly.

The boundary minimization theorem likewise starts with a SPECIFIED FINITE history register U and its deterministic update tau(u,a). It finds the coarsest congruence of that register preserving response signatures. It does not infer an arbitrary unbounded history process or claim the chosen finite register is sufficient without the universe promise.

## 8. Finite-observation pipeline lemma, conditional on calibration and sampling
This lemma imports the earlier local three-view calibration theorem rather than claiming to re-prove it. Let the model lie in its compact identifiable parameter class: full-column-rank sensor matrices with singular values bounded below, positive latent-state frequencies, fixed latent alphabet bounds, and a finite inverse-Lipschitz constant C_cal modulo latent label permutations. The same learned sensor channels apply to all aligned histories/patch pairs, with conditional sensor-noise independence as required for tensor-product deconvolution. Rank-selection gaps and consistent label alignment are included in this event.

Let each required raw experiment table have at most J cells, and let there be Q tables, including calibration, single-transition, and paired-transition/context tables. Suppose each table has N INDEPENDENT sampled windows. No claim that arbitrary persistent sources provide these windows or any mixing rate is made. For confidence 1-alpha, Hoeffding and a union bound imply raw table one-norm error at most delta simultaneously whenever

  N >= J^2 log(2 Q J / alpha) / (2 delta^2).

Indeed each cell error is at most delta/J on that event. A dependent-data implementation must replace this concentration step with a proved concentration/effective-sample bound.

Fit a valid sensor model in the compact class. If its table discrepancy from the empirical calibration table is no greater than that of the true model, the fit-to-true calibration table error is at most 2delta. The imported inverse bound gives sensor parameter error at most 2 C_cal delta, modulo the aligned labels. Let every used inverse observation channel have norm at most L and at most k channel factors occur in a deconvolved table. On a fixed-conditioning neighborhood, pseudoinverse perturbation supplies a constant C_inv such that each inverse-factor error is at most 2 C_inv C_cal delta. A telescoping product gives a deconvolved table error bound of the form

  zeta <= L^k delta + 2 k (L+1)^(k-1) C_inv C_cal delta,

provided inverse-factor errors are at most1. Norm conventions must be held fixed; finite-dimensional norm-conversion constants can be absorbed in L,C_inv. A valid simplex projection/minimum-distance fit increases the true table error by at most a further factor2 when its empirical-fit discrepancy is no worse than the true table's. This is a norm bound, not a computational guarantee for finding that fit efficiently.

Suppose every conditioned context cell has true probability at least rho, and the resulting joint-table one-norm error is <=rho/2. Normalizing the fitted context rows then gives conditional response one-norm error nu <= 4 zeta/rho, with the projection factor included in zeta. This applies separately to baseline and pair rows, using the correct common context conditioning. If the pair's marginal depends on the partner's context, that is not repaired by normalization; it violates the local-response universe or reveals omitted context.

The residual is D_ij=J_ij-B_i B_j. If baseline and joint conditional rows each have one-norm error <=nu, the corresponding pair residual row error is <=3nu: the product difference is bounded by the sum of the two marginal errors. Convert the finite collection of rows to an operator-norm bound epsilon, for example using its Frobenius bound. For an R_i by R_j residual matrix, the conservative entrywise bound gives epsilon <=3nu sqrt(R_i R_j). Use eta=nu for baseline coordinate error in section6.

Choose delta so that the resulting epsilon is below the rank threshold and all projector-score errors, baseline block-sum errors, and input-refinement errors are smaller than half their declared nonzero gaps. Then, on the simultaneous sampling/calibration event, the recovered conditional quotient, autonomy flag, and finite-register input congruence equal their population-law values, up to latent state labels. This is a conditional finite-sample statement for fixed table size and conditioning constants. It does not certify the affine-source, replica-independence, source-support, partner-rank, context-coverage, or physical deployment promises from data alone. It also does not supply a production finite-data implementation or an explicit numerical value of C_cal.

# Shared uncertainty under typed assembly: exact contextual closure

## Plain-language abstract

An incomplete experiment can make two candidate mechanisms look the same when tested alone. Connecting either mechanism to another component can expose the difference: both components may be responding to the same hidden disturbance. Thus a collection of locally acceptable mechanisms is not automatically an acceptable assembled system. The common disturbance must have one law and one evolution, and every component must use that same explanation.

This note proves an exact obstruction and a finite repair in a finite hidden-effect universe. The repair does not identify the entire exterior. It identifies which distinctions between exterior effects matter to the particular mechanisms being assembled. If available experiments do not resolve those distinctions, the correct answer remains a coupled family of explanations, not independent error bars for each component. The theorem does not promise that the missing experiments are physically available.

## 1. Setup and timing

Let Z be a finite set of admitted exterior effect modes at a fixed causal time slice. All conditioning variables c (old local states, received boundary messages, chosen current actions, and permitted history) are fixed BEFORE the fresh hidden mode and fresh component outputs are sampled. The statements below apply separately at each c; unconditional probe rank cannot replace conditional rank.

Let M(e,z) be the conditional distribution of Z under admitted experiment e. M is stochastic. At least one row m_* is strictly positive on the admitted support Z. This positivity is a support assumption, not identification of M from data. If M is unknown, all claims apply worldwise to candidate (M, mechanisms), and the admissible family must retain M as an unknown.

A component output event has response f:Z->[0,1]. If fresh component randomness is conditionally independent given the shared mode Z and c, an assembly event has response fg. More generally, any shared fresh randomness must be INCLUDED in Z; independence is not obtained by decree. The observed response is Mf.

Let A be a unital subalgebra of R^Z containing all admitted component response functions. It is the linear span of finite products of these functions, including 1. Linear combinations below are equality tests on measured probabilities; they need not themselves be physically implementable stochastic events.

## 2. Exact obstruction to quotient assembly

**Theorem 1 (descent obstruction).** Let K=ker(M|A). Define f~g iff Mf=Mg. Multiplication of response classes [f][g]=[fg] is well-defined if and only if K is an ideal of A. Under the full-support-row assumption this is equivalent to K={0}.

**Proof.** Well-defined multiplication implies [k][a]=[0] for k in K,a in A, hence ka in K. Conversely the ideal property gives fg-f'g'=(f-f')g+f'(g-g') in K whenever f~f',g~g'. If K is an ideal and k in K, k^2 is in K. Therefore 0=(Mk^2)(e_*)=sum_z m_*(z)k(z)^2, which forces k=0. The converse is immediate. QED.

**Probability-level force, not merely signed algebra.** If k is a nonzero bounded real response difference in A with Mk=0, let f=1/2+epsilon k and f'=1/2 for small epsilon>0. Both are strictly between 0 and 1, with Mf=Mf'. Use an independent fresh Bernoulli component with response g=1/2+epsilon k. Then
M(fg)-M(f'g)=epsilon^2 M(k^2),
which is nonzero in the full-support row. Thus two positive local mechanisms with identical probe outputs become distinguishable after positive assembly. This construction requires that these response functions and a shared-mode context belong to the admitted mechanism language. The algebraic theorem does not assert every physical system permits those extra mechanisms.

**Interpretation.** A genuinely incomplete averaging map cannot support arbitrary independent substitution of locally indistinguishable responses in a response-rich assembly language. This is NOT a claim that every incomplete experiment destroys every decomposition. If M is injective on the SMALL algebra A relevant to the chosen components, composition is safe without identifying the rest of the exterior.

## 3. Exact contextual equivalence and minimal effect quotient

Define f≡ctx g when M(h(f-g))=0 for every h in A. Then f≡ctx g iff f=g as functions on Z, for f,g in A: take h=f-g and use the positive row. Consequently the compositional congruence refining observational equivalence is equality on A, not equality on all exterior descriptions.

Let z≈z' iff every generator response takes the same value at z,z'. Let Q=Z/≈ and d=|Q|. Then A is exactly the algebra of functions constant on Q-blocks.

Proof of the nontrivial inclusion: for each pair of distinct Q-blocks choose a generator separating them. For a fixed block q and another block r, a rescaled separating generator yields a function equal to 1 on q and 0 on r. The product over r!=q is the indicator of q (its values on other blocks are killed by their own factor). Hence every block indicator belongs to A. This is a finite interpolation proof; no claim of stable numerical interpolation follows without separation bounds.

Thus Q is the coarsest effect description preserving ALL local mechanism likelihoods and their finite assemblies. It need not be a physical partition of the environment. Different physical modes with exactly the same relevant effects remain merged.

## 4. Finite closure and the additional evidence actually needed

Start with a basis of V0=span{1, admitted generator responses}. Repeatedly form V_{j+1}=span(V_j union {g v: g a generator, v in a basis of V_j}). Stop at equality. All spaces lie in R^Z, dimensions increase strictly until stabilization, and stabilization is a unital algebra containing the generators. Therefore the result is A, after at most d-dim(V0) strict increases (and one final equality test).

This is an exact finite symbolic procedure PROVIDED candidate response tables are available. It is not an algorithm for recovering unknown response tables directly from arbitrary readouts. In a discovery proof it belongs in the candidate verifier: a proposal supplies the response tables and a common positive hidden process, then this procedure exposes assembly distinctions that the experimental record does not constrain.

For unknown source probability p on Q, suppose available observations identify its integrals on a linear space V⊂A containing 1. All assembly event probabilities are identified iff the integrals on A are identified. If the admitted source fiber includes a strictly positive interior point and imposes only those linear observation constraints, this happens iff V=A. Otherwise pick nonzero signed delta orthogonal to V, with delta·a!=0 for some a in A; p±epsilon delta are positive normalized sources agreeing on every observed test and differing on an assembly. Since A is spanned by products, at least one product test separates them.

A basis completion uses at most d-dim(V) additional linearly independent product statistics. This is a count of scalar statistical constraints, NOT a bound on physical experiments, sample complexity, word length, or interventions. Some products may require simultaneously observing channels that cannot be jointly read, or repeatability of a hidden mode not available in the physical setup. Such tests must be labeled unavailable rather than assumed.

With prior nonlinear restrictions on source processes, V=A is sufficient but not necessary; the exact test is constancy over the constrained source fiber. Do not replace that fiber by its rectangular hull.

## 5. Positive shared-process gluing, with causal records

Let theta be one fixed member of a candidate set Θ selected before a run. It supplies:
- one initial positive law μ_theta on (Z_0, local states, boundary memories);
- one causal hidden transition Q_theta(z'|z, permitted past/interface variables);
- local positive kernels F_{i,theta}(s_i',out_i|s_i, in_i,z,action_i);
- deterministic typed wire/decoder rules and causal boundary-memory updates.

Every fresh output is sampled after its inputs are fixed. A cycle must contain an explicit delay or a supplied joint simultaneous kernel; multiplying kernels around an instantaneous loop is invalid. Shared noise is represented once, not resampled independently in each component.

**Theorem 2 (worldwise witness gluing).** If all local records use the SAME theta, initial law, hidden trajectory, and gauge alignment on shared variables, their synchronous fiber product is a positive causal joint process. Its finite-record probabilities are obtained by multiplying the one-time conditional kernels in causal order and summing internal variables. Marginalization to any local record recovers its specified process, and regrouping/refining the SAME full record commutes with this marginalization.

**Proof.** Each causal kernel is normalized. Repeated summation in reverse causal order gives total mass one and consistent finite-horizon distributions. The finite-alphabet extension theorem gives a path measure. Projection merely sums unused record coordinates. Iterated summation and function composition are associative, so any two refinement orders retaining the same records give the same projected law. QED.

This is standard causal-kernel composition, not by itself a new decomposition-discovery theorem. Its substantive use here is its premises: an independently fitted local explanation is not accepted unless it extends to this SAME shared witness.

**Gauge rule.** If a local learner labels shared hidden modes privately, a bijection must transport BOTH all emission/response tables and the hidden transition/initial law. On overlaps the maps must compose consistently (identity around a closed chain). Equal observed marginal distributions do not establish such a map. If states are nonidentifiable beyond bijections, retain general shared latent extensions rather than arbitrarily asserting a gauge alignment exists.

**Refinement of evidence.** New evidence restricts Θ to Θ'⊂Θ. For each theta∈Θ', the same record projections and refinement diagrams still commute. This is restriction of one indexed family, NOT a single path measure representing every theta, and NOT permission to change theta along a run.

## 6. Explicit failures of independent uncertainty sets

### 6.1 Two locally identical responses with different joint assembly

Z is a persistent fair bit. Two Bernoulli outputs are conditionally independent given Z. A has P(A=1|Z)=.2+.6Z. B is either aligned (.2+.6Z) or reversed (.8-.6Z). Every single component has fair output, under the sole available probe. But P(A=B)=.68 in the aligned world and .32 in the reversed world. The hidden labels are irrelevant only if the response AND every shared use are transported together. Reversing B alone changes the physical joint explanation.

### 6.2 Pairwise locally positive laws with no common triple

Three fair bits have proposed pair laws P(A!=B)=.05, P(B!=C)=.05, P(A!=C)=.95. Each pair table is strictly positive. No joint law exists, since pointwise 1[A!=C]≤1[A!=B]+1[B!=C], giving .95≤.10, a contradiction. This is a standard marginal compatibility obstruction; it is included as a regression test, not the claimed new theorem.

### 6.3 A nonrectangular positive dynamical fiber

A hidden stationary fair sign Z_t evolves with E[Z_{t+1}|Z_t]=lambda Z_t, 0<lambda<1. An observed sign Y_t has E[Y_t|Z_t]=a Z_t with independent emission noise, 0<a<1. Hence E[Y_tY_{t+1}]=a^2 lambda and E[Y_tY_{t+2}]=a^2 lambda^2.

If data consist only of stationary singletons and adjacent pairs with measured correlation c=.1, then a∈[.4,.8], lambda=.1/a^2 is an exact family of positive dynamical explanations. It is a curved, nonrectangular family. Choosing a=.4 from one admissible fit and lambda=.15625 from another gives lag-one correlation .025, contradicting the data. The world (a=.4,lambda=.625) predicts lag-two correlation .0625; (a=.8,lambda=.15625) predicts .015625. A lag-two query can separate them if available. This example is about this explicitly limited observation protocol; full readout histories already contain lag-two information and cannot be called equally ambiguous.

For several local channels sharing Z, every channel must use the same lambda and consistent source trajectory. Their parameters obey c_i=a_i^2 lambda, and same-time cross correlations equal a_i a_j. Retaining each channel's marginal parameter range and choosing values independently discards these constraints. No reconstruction of an unrelated exterior is needed to state them.

### 6.4 Fixed world versus time-switching uncertainty

A world theta∈{.1,.9} generates IID Bernoulli(theta) outputs. In either fixed world P(Y0=0,Y1=1)=.09. A rectangular adversary selecting theta0=.1 and theta1=.9 obtains .81. The latter is NOT a compatible fixed world. It can be an intentional conservative upper bound, but loses completeness and may reject a useful decomposition for an impossible reason.

## 7. Quantitative local obstruction

For response difference k∈A, if |M(kh)(e_*)|≤epsilon for every h in an admissible context span containing k, then E_{m_*}k^2≤epsilon. Consequently max_z |k(z)|≤sqrt(epsilon/min_z m_*(z)). More generally representing k=sum_j alpha_j h_j from individually tested contexts with error epsilon_j yields E k^2≤sum_j |alpha_j|epsilon_j. Ill-conditioned context interpolation causes large coefficients; a finite exact algebra basis does not guarantee good statistical scaling.

## 8. Scope and baseline

The algebraic ideal criterion, finite function-algebra partition description, positive kernel composition, marginal compatibility and HMM moment calculations are standard mathematical mechanisms. This note isolates an exact failure mode for incomplete-experiment typed assembly and supplies a finite candidate-verification closure. It DOES NOT by itself establish readout-to-component discovery, unknown calibration recovery, physical probe adequacy, or efficient global witness search. The main discovery theorem must supply those missing burdens in a declared model class, with an example not engineered to reveal membership directly.

## 9. Persistent-source qualification: a one-step local quotient is not enough

Pointwise hidden-mode invariance of a local response must not be confused with autonomy of the hidden mode process after discarding local microstate.

Concrete positive example: state (S,R,Z) consists of bits, with conditionally independent fresh updates
P(S'=1|S,R,Z)=.2+.6Z,
P(Z'=1|S,R,Z)=.2+.6R,
P(R'=1|S,R,Z)=.1+.8R.
All probabilities are strictly between zero and one. The one-step S response ignores R completely once Z is fixed. Nevertheless two states with the same (S,Z) and different R give different Z' distributions, so (S,Z) is not a controlled Markov quotient. Starting with Z=0, S1 has probability .2 in both states, whereas P(S2=1) is .32 when R=0 and .68 when R=1.

A persistent quotient therefore needs one of:
1. a proof that the source transition itself descends through the retained summary and permitted interfaces;
2. an explicitly retained hidden residual process containing R, with its original coupling and feedback; or
3. a charged outgoing message sufficient for the residual/source to update.

Option 2 is valid partial identification and exact joint realization, but is not a closed autonomous local Markov model. The theorem must state which claim is delivered. A local response Gram test does not certify option 1 merely because it certifies pointwise equality of the S response.

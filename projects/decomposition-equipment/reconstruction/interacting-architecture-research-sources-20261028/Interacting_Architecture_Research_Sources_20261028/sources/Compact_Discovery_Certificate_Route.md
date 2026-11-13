# Compact witnesses for unknown interacting realizations

Research support note dated 2026-10-28 UTC.

## Result and scope

This note distinguishes **checking an unknown proposed decomposition**, **checking that decomposition with a supplied witness**, and **guaranteeing that a useful witness is small**. A hard equivalence problem does not rule out cheap verification of particular proof-carrying proposals.

There are three rigorous results here.

1. Low initialized observable rank and a narrow interaction graph do not even guarantee an all-hidden-state quotient into the learned predictor. A path shift register with an iid initialized output gives an elementary counterexample.
2. Even after the initialized-rank problem is repaired, low observable rank and constant static interaction width do not bound tensor-train or canonical-polyadic witness size polynomially. A polynomial-size reversible clocked circuit has polynomial observable rank but requires exponential tensor-train bond dimension, **for every ordering of its component indices**. The obstruction is specific to that witness language: the same family has a polynomial-size circuit-and-cancellation proof.
3. A strong local-actuation hypothesis does imply a signed canonical-polyadic quotient of rank exactly the observable rank, and an observationally equivalent initializer supported on at most that many hidden configurations. This is a restricted certificate-completeness theorem, not the requested unrestricted discovery theorem. Its local calibration assumption is substantial, and in many informative models its observable rank is already the full product-state dimension. An explicit exception has rank \(2n\) while all \(2^n\) hidden point states remain predictively distinguishable.

Thus the promising conclusion is **not** that checking with witnesses fails. It is that the witness language and its completeness/resource theorem are part of the mathematical problem. Tensor trains are one sufficient language, not a universal default.

Status: the algebraic theorem, clock/parity obstruction, circuit-proof construction, and nonvacuity example received independent mathematical review; a final text-consistency pass checked this note against the audited hypotheses. The cited audit files record the scope and qualifications. No priority claim. The general unknown-architecture discovery problem remains open. All state-space dimensions below are mathematical objects; the proposed checker does not materialize their product.

## 1 Observable target and the exact certificate interface

Let a learned controlled linear predictor be

\[
 p(y_1\cdots y_t\Vert u_1\cdots u_t)
 =\ell T_{u_t,y_t}\cdots T_{u_1,y_1}\alpha,
 \qquad \alpha\in\mathbb R^r.
\]

Inputs are interventions/exogenous controls, not observations that have silently been conditioned on. A generative proposer supplies an **unknown** product state space

\[
 X=\prod_{i=1}^n[d_i],\qquad N=\prod_i d_i,
\]

local component mechanisms, interface variables, their wiring, and a local stochastic circuit implementing nonnegative symbol matrices \(H_{u,y}\) on \(X\). Their unconditional sum must be column stochastic. Ordered stochastic circuits/generative DAGs make this normalization local. A collection of individually normalized factors in a cyclic undirected factor graph does not, by itself, do so.

A sufficient simulation witness consists of a map \(F:\mathbb R^N\to\mathbb R^r\) and a nonnegative normalized initial law \(\nu\) satisfying

\[
 \boxed{\quad \ell F=\mathbf1^T,\qquad
 F H_{u,y}=T_{u,y}F\quad\text{for every }u,y,\qquad
 F\nu=\alpha.\quad}
\]

Induction gives equality of every controlled trajectory probability. This remains true under every adaptive randomized policy whose next action depends on the observed past and external randomness: multiply each open-loop word probability by the same causal policy factors and sum. No separate reset assumption is involved.

The positivity lies in the proposed physical kernels and initializer. **The quotient \(F\) may be signed.** It is not a stochastic aggregation, a nonnegative factorization, or a physical decomposition into \(r\) modes.

These are classical weighted-automata simulation equations, not a new equivalence principle. See [Ésik and Maletti, Simulation vs Equivalence](https://arxiv.org/abs/1004.2426). The resource question here is how to certify them without expanding \(N\).

### What the calibrated finite table actually establishes

Given a globally valid rank-\(r\) promise, complete prefix/suffix bases \(P,S\), and an invertible calibrated block \(H_{S,P}\), the usual Hankel construction gives

\[
 T_a=H^a_{S,P}H_{S,P}^{-1},\quad
 \alpha=H_{S,\epsilon},\quad
 \ell=H_{\epsilon,P}H_{S,P}^{-1},
\]

where \(H^a_{s,p}=p(pas)\) and \(a=(u,y)\). This is established controlled predictive-realization theory; see [Singh, James and Rudary, Predictive State Representations, Theorem 6](https://faculty.cc.gatech.edu/~isbell/reading/papers/uai2004psr.pdf).

A nonsingular empirical table alone does **not** establish a global rank promise, absence of a late unseen mode, or exact equality to the true process. Finite-sample use additionally needs a conditioning margin, coverage/exogeneity assumptions, error accounting, and a specified prediction horizon or stability condition. The exact certificate below checks a candidate against the supplied predictor, not against unobserved truth by fiat.

## 2 A cheap checker when a contraction witness is supplied

Suppose \(F\) is supplied as a signed tensor train or a signed canonical-polyadic decomposition, and \(\nu\) is either explicitly sparse or has an independently certified nonnegative generative representation. For each label pair, form

\[
 R_{u,y}=FH_{u,y}-T_{u,y}F.
\]

Exact real/rational identity is equivalent to \(\|R_{u,y}\|_F^2=0\). Expanding this square produces a doubled one-step tensor network. The proposer can supply a contraction/elimination schedule. The checker verifies the schedule and executes it; there is no need to trust the claimed width.

If every intermediate tensor has at most \(B\) entries, the cost is polynomial in the explicit input/certificate size and \(B\), with ordinary rational bit-cost charged separately. In a bounded-domain notation it is

\[
 \operatorname{poly}(\text{local tables},r,\text{witness size},|U||Y|)
 \ d^{O(\kappa)},
\]

where \(\kappa\) is the width of the **actual doubled residual network**, not merely the static graph connecting component names. This is standard tensor contraction, as in [Markov and Shi](https://arxiv.org/abs/quant-ph/0511069), used as a trusted verification backend.

If the target lists every \(T_{u,y}\), the cost includes that entire list. A product readout alphabet can itself be exponential. Avoiding a hidden-state expansion is not permission to hide an output-alphabet expansion: either charge for it or give a factored target and include its output indices in the verified contraction.

For a signed CP decomposition

\[
 F(x)=\sum_{a=1}^{q}c_a\prod_i g_{ia}(x_i),\qquad c_a\in\mathbb R^r,
\]

the squared residual expands into polynomially many, in particular \(O(q^2)\) pairs of product-boundary contractions, with polynomial coefficient arithmetic in \(r\). Boundary factors do not require a product-state array. This is **sound** for every accepted proposal. It is not yet a theorem that every correct proposal has small \(q\), small bond dimension, or small contraction width.

Exact rational checking is different from declaring a floating-point residual small. A finite-precision version needs explicit certified interval/error bounds; long-horizon error does not follow automatically from a one-step tolerance.

## 3 First completeness obstruction initialized rank is not statewise rank

Take \(n\) hidden fair bits arranged on a path. At each step emit the oldest bit, shift the remaining bits left, and append a fresh fair bit. Start from the uniform product law. The observed process is iid fair, so its minimal initialized predictor has

\[
 r=1,\qquad T_0=T_1=1/2,\qquad\ell=\alpha=1.
\]

The transition is a normalized nearest-neighbor stochastic mechanism, and the initial law is as simple as possible. Nevertheless no normalized all-state quotient \(F\) to that one-dimensional predictor exists. Normalization forces \(F=\mathbf1^T\), while

\[
 (FH_y)(x)=\Pr(Y_1=y\mid X_0=x)=\mathbf1\{x_1=y\}
 \ne 1/2=(T_yF)(x).
\]

So bounded spatial width and small initialized rank do not imply even existence, let alone a compact tensor representation, of this particular kind of witness. Conditional predictions from arbitrary hidden states are richer than predictions obtainable from the initialized process.

This does not invalidate other witnesses. In this example the opposite-direction invariant-distribution embedding is tiny: after emitting and shifting, the new hidden buffer is again uniform and independent of the observed bit. More generally one may need a relation restricted to reachable beliefs, a span of simulations, or a proof involving an invariant subspace rather than an all-state quotient.

## 4 A stronger obstruction polynomial rank can require exponential tensor witnesses

The next construction removes the preceding rank mismatch. It has the same initialized and all-state predictive rank. It nevertheless has no polynomial-size CP or tensor-train representation of its normalized all-state quotient. A circuit proof remains small.

### 4.1 A Boolean feature with large rank across every balanced cut

For a graph \(G\) on \(n\) binary variables, define

\[
 q_G(x)=\bigoplus_{\{i,j\}\in E(G)}x_ix_j.
\]

There exist graphs for which every partition \(A\sqcup B=[n]\) with \(n/3\le |A|\le2n/3\) has binary cross-adjacency rank at least \(\lfloor n/12\rfloor\), up to an immaterial constant adjustment for small \(n\).

Here is a direct existence proof. For a random graph, a fixed \(|A|\times|B|\) cross-adjacency matrix is uniformly random. The number of matrices of rank at most \(k\) is at most \(2^{k(|A|+|B|)}\), by writing them as the product of an \(|A|\times k\) and a \(k\times|B|\) matrix. Taking \(k=\lfloor n/12\rfloor\) gives probability at most

\[
 2^{kn-|A||B|}\le 2^{-5n^2/36}.
\]

A union bound over at most \(2^n\) cuts is less than one for all sufficiently large \(n\). These graphs have polynomial-size descriptions; no efficient deterministic graph-selection claim is needed for this existence counterexample.

Across any such cut, the matrix \(S_{a,b}=(-1)^{q_G(a,b)}\), after multiplying rows/columns by signs, is \((-1)^{a^T\Gamma_{AB}b}\). Its distinct rows are independent binary characters, so

\[
 \operatorname{rank}_{\mathbb R}S=2^{\operatorname{rank}_{\mathbb F_2}\Gamma_{AB}}.
\]

Since the zero-one matrix of \(q_G\) equals \((\mathbf1\mathbf1^T-S)/2\), its real rank is at least

\[
 2^{\lfloor n/12\rfloor}-1.
\]

### 4.2 A local reversible realization with only polynomial predictive rank

Add one work bit \(b\). A polynomial-size reversible circuit \(C\), using adjacent SWAPs and three-bit Toffoli gates on a path, implements

\[
 C(x,b)=(x,b\oplus q_G(x)).
\]

One can route each edge's two data bits and the work bit together, apply a Toffoli, and undo the routing. This gives \(O(n^3)\) gates; optimize nothing. Concatenate its gate list with the reverse inverse list. Let the total length be \(L\), and add a clock component \(t\in\mathbb Z_L\). The time-homogeneous hidden transition is

\[
 D(t,z)=(t+1,G_tz).
\]

Because the full gate cycle is \(C^{-1}C=I\), \(D^L=I\) on **every** hidden configuration. Emit before the transition:

\[
 e(t,z)=\mathbf1\{t=0\}\,b(z).
\]

Every hidden configuration produces exactly one of \(L+1\) deterministic future streams: the all-zero stream, or a period-\(L\) stream with one 1 at one of the \(L\) phases. Every class is nonempty. Length-\(L\) output tests distinguish all these classes, so the all-state predictive dimension is exactly \(L+1\).

Start from the uniform product distribution on clock and bits. It is stationary because \(D\) is a permutation. The zero class has probability \(1/2\); each pulse-phase class has probability \(1/(2L)\). A length-\(L\) prefix isolates each class, so the initialized Hankel rank is also

\[
 r=L+1=\operatorname{poly}(n).
\]

This is a model with genuine deterministic interaction gates and nonnegative normalized local mechanisms. It is not a claim about entrywise strictly positive kernels.

**Optional noisy readout removes revealing words.** Pass each emitted bit through independent binary symmetric noise with parameter \(0<\epsilon<1/2\). Every finite observed word then has strictly positive probability. The length-\(L\) output laws of the \(L+1\) hidden classes remain linearly independent: relative to the all-zero-class product law \(P_0\), they have likelihoods \(1\) and \(1+h_j(y_j)\), where the \(h_j\) are nonconstant mean-zero one-position contrasts. This also gives initialized rank \(L+1\), because after \(L\) transitions the hidden classes return to their starting phases and all initial class weights are positive. In class coordinates, each symbol matrix is a phase permutation times a strictly positive diagonal matrix, hence is invertible. Thus every observable word map is invertible and no finite observed word is an exact predictive reset. The quotient, its tensor lower bound and its circuit proof are unchanged. This does not make the hidden permutation drift mixing or entrywise positive.

### 4.3 The static graph is narrow

At a particular clock value exactly one adjacent gate acts. Each next data/work bit is therefore a deterministic function of the clock and a constant-size neighboring window. The clock increments independently. The one-step factor description has a path, constant-range path edges, and one clock apex: its static primal width is bounded by a constant. There are \(n+2\) persistent components; bit alphabets have size 2 and the single clock alphabet has polynomial size \(L\). The explicit conditional tables therefore have polynomial size.

The lower bound is consequently against a claimed polynomial bound in component count, observable rank, local alphabet sizes, local-table size and constant static width. This version does not assert that every persistent component has a constant-size alphabet.

### 4.4 Every normalized all-state quotient has exponential TT and CP size

Use the minimal \(L+1\)-state target whose coordinates are the zero class and the pulse phases. The normalized all-state quotient is uniquely the vector of class indicators: length-\(L\) future tests recover each coordinate, so no different signed quotient can avoid these functions.

At the halfway clock phase, returning to phase 0 applies \(C^{-1}\). The appropriate pulse-class indicator is thus \(b\oplus q_G(x)\). Fix \(b=0\); this coordinate becomes \(q_G(x)\).

Now choose **any** ordering of the physical tensor indices, allowing the clock, work bit and predictor-coordinate index anywhere. There is a TT cut with between one third and two thirds of the data-bit indices on each side. Fixing the other indices to the values above yields the matrix of \(q_G\) as a submatrix of that cut flattening. Therefore the bond at that cut is at least

\[
 2^{\lfloor n/12\rfloor}-1.
\]

Every ordering has this obstruction. CP rank is at least every flattening rank, so it is exponentially large as well. Invertible changes of the predictor coordinates do not evade the conclusion: taking the required linear combination of coordinates recovers the same scalar function.

This rules out a polynomial CP/TT-witness bound from small observable rank and narrow static graph, even when initialized and all-state predictive dimensions agree. It does **not** rule out small circuits, proof traces, other tensor topologies, or compact certificates for an observationally equivalent alternative architecture.

## 5 The same example has a short circuit proof

The preceding construction is deliberately a counterexample to a witness language, not to the proposal/check distinction.

For each clock phase \(t\), let \(B_t(z)\) be the work bit after following the remaining gate suffix to phase 0. The decoder says:

* if \(B_t(z)=0\), the predictive class is the all-zero class;
* otherwise it is the pulse class whose next 1 occurs after \(-t\bmod L\) steps.

Each \(B_t\) is a circuit with at most \(L\) gates, so all decoders have total size \(O(L^2)\). The certificate includes the gate list and its reverse inverse list. For phases other than the phase-zero convention boundary, the identity

\[
 B_{t+1}(G_tz)=B_t(z)
\]

is verified by literal suffix composition. For the phase-zero boundary identity, cancellation of adjacent gate/inverse pairs proves the full cycle is identity. Each local gate inverse is checked on a constant-size truth table. No arbitrary circuit-equivalence oracle is used.

The emission identity is checked directly at clock phase 0. The initial class masses follow because each phase-to-zero circuit is a bijection: under uniform work bits its output bit is fair, and the clock is uniform. Thus initialization also has a short counting-free proof.

Together these checks prove the same intertwining equations in polynomial time. The verifier uses the **supplied derivation**, not exhaustive evaluation of the decoder on all hidden configurations. In this family, replacing TT witnesses by circuit decoders plus local rewrite proofs changes an exponential representation cost into a polynomial one.

This is a concrete reason to design a proof-carrying architecture format rather than assume that a single tensor format captures all useful realizations. It remains a benchmark: the visible pulse process has much simpler alternative realizations, and this construction does not identify a unique physical architecture from its readouts. The noiseless presentation uses revealing words only to simplify the rank proof; the noisy-readout version above has no exact observable resets. Neither version is an architecture-discovery theorem.

## 6 A restricted theorem that derives small CP witnesses from control hypotheses

There is also a positive, but strongly calibrated, completeness theorem.

### Assumptions

For the proposed unknown product decomposition, assume:

1. The no-actuation unconditional transition is an invertible stochastic matrix \(D\), given by a local stochastic circuit. Invertibility can be certified by a factorization into invertible local stochastic gates; inverses need not be positive.
2. Actions actuate at most one component at a time. For action \((i,k)\),
   \[
   \sum_yH_{(i,k),y}=D K_{i,k},
   \]
   where \(K_{i,k}\) acts only on component \(i\). Assume a finite \(O(d_i^2)\)-sized family at each site, so the alphabet has size \(1+\sum_i O(d_i^2)\), not an exponential Cartesian product. If more actions are supplied, charge for and verify all of them; selecting a spanning subfamily for this proof does not certify the omitted instruments.
3. The real linear span of \(I\) and the proposed local actuator matrices is
   \[
   \mathcal S_i=\{A:\mathbf1_i^TA=\lambda\mathbf1_i^T
                    \text{ for some }\lambda\in\mathbb R\}.
   \]
   Its dimension is \(d_i(d_i-1)+1\). The condition is a finite local rank check.
4. The initialized observable process agrees with a minimal rank-\(r\) target. The initial hidden law \(\pi\) may be arbitrarily correlated.

The actual nonidentity controls can be strictly positive and invertible. For example start with a strictly positive invertible stochastic matrix and add sufficiently small independent zero-column-sum perturbations. Their span, together with the base matrix, is \(\mathcal S_i\). Thus no physical reset action is required. However, **point-reset matrices are in their signed linear span**. This is a powerful hidden calibration assumption, not a claim to have eliminated calibration.

### Step 1 The initialized rank equals the full predictive rank

Define

\[
 R=\operatorname{span}\{H_w\pi:w\},\qquad
 W=\operatorname{span}\{\mathbf1^TH_w:w\}.
\]

Both spaces are invariant under the relevant symbol operators, hence under unconditional \(D\). In finite dimensions, invariance under an invertible map implies invariance under its inverse. Consequently

\[
 D^{-1}R=R,\qquad WD^{-1}=W.
\]

Since \(DK_{i,k}R\subseteq R\), one obtains \(K_{i,k}R\subseteq R\). Likewise \(WD=W\) and \(WDK_{i,k}\subseteq W\) give \(WK_{i,k}\subseteq W\).

Each local span contains every point-reset matrix \(e_a\mathbf1_i^T\). Products of these maps send any normalized \(\pi\) to each product point vector \(e_x\). Hence \(R=\mathbb R^N\). The Hankel rank is therefore \(\dim W=r\). This explicitly supplies the missing argument that failed in the shift-register example.

### Step 2 The predictive rowspace has a product-function basis

Choose a rational local basis consisting of the constant function and \(d_i-1\) contrasts:

\[
 \mathbb R^{[d_i]}=\operatorname{span}\{1\}\oplus U_i.
\]

The local algebra \(\mathcal S_i\) fixes the constant line and permits arbitrary maps from contrasts to contrasts and constants. It contains the projections onto the two summands. Applying all local projections decomposes an invariant space into the blocks

\[
 V_S=\bigotimes_{i\in S}U_i\otimes
     \bigotimes_{i\notin S}\operatorname{span}\{1\}.
\]

Arbitrary endomorphisms within each contrast factor force any nonzero invariant portion of \(V_S\) to be all of \(V_S\). Maps from a contrast to a constant force all lower blocks. Therefore

\[
 W=\bigoplus_{S\in\mathcal I}V_S,
 \qquad \mathcal I\text{ downward closed}.
\]

This is a specialization of the classical structural-matrix-algebra invariant-subspace theorem; see [Akkurt, Barker and Wild, Theorems 1–4](https://doi.org/10.1016/j.laa.2004.05.009), not a new module classification.

In particular, \(W\) has a basis of exactly \(r\) product functions \(g_1,\ldots,g_r\). The quotient to the learned minimal predictor has

\[
 F(x)=\sum_{a=1}^r c_a g_a(x).
\]

Its signed canonical-polyadic rank is at most \(r\), and in fact exactly \(r\) because its flattening between predictor coordinates and hidden configurations has rank \(r\). All TT ranks are at most \(r\) as well. This is a derived witness bound; the existence of a compact intertwiner was not assumed.

### Step 3 The compatible initializer has at most r atoms

Normalization gives \(\ell F(x)=1\) for every \(x\), so the vectors \(F(x)\) lie in an affine hyperplane of dimension at most \(r-1\). Since

\[
 \alpha=\sum_x\pi(x)F(x),
\]

Caratheodory's theorem yields a nonnegative law \(\nu\), supported on at most \(r\) hidden configurations, with \(F\nu=\alpha\). It stores \(O(nr)\) state labels rather than an arbitrary correlated table. Equivalently apply [Caratheodory–Tchakaloff subsampling](https://drna.padovauniversitypress.it/system/files/papers/PiazzonSommarivaVianello_2017_CTS.pdf) to the predictive function space including constants.

This replaces the initial law **observationally**. It does not recover its physical correlations, prove that it can be prepared by allowed controls, or preserve hidden stationarity. If the original joint initial law itself must be retained or certified stationary, an additional witness is required; arbitrary correlated laws have no generic succinct encoding.

### Resulting certificate theorem

Every matching candidate satisfying these hypotheses has a signed rank-\(r\) CP simulation certificate and an at-most-\(r\)-atom observational initializer. Given an actual doubled-network contraction schedule of polynomial cost, the trusted checker verifies the unknown local tables, wiring, normalization, initial compatibility and all one-step identities in polynomial time in their explicit sizes and \(r\), without expanding \(N\).

For rational local tables and a rational target, polynomial-bit witnesses can also be chosen. One route selects \(r\) independent target future tests of length at most \(r-1\), writes \(F\) using the inverse of their target evaluation matrix, and expands in the fixed rational product basis. Common denominator lengths grow with the number of gates in these tests and the explicit table bitlength, not with an enumerated hidden-state table. The sparse weights solve at most \(r\) rational linear constraints. In a real/arbitrary-precision formulation, instead state an arithmetic-operation bound and charge for the supplied number representations.

### Why this is not the desired general discovery theorem

The local-algebra premise presupposes independently addressable controls spanning all hidden local directions, albeit with the component assignment and matrices proposed rather than supplied. It is a calibration substitute and may be unavailable in passive readouts.

It can also erase the supposed compression. If one predictive function has any nonzero full-order contrast component, downward closure forces every block and \(r=N\). For standard diagonal state emissions, separately informative readouts at every component plus this rich local actuation likewise generate all product functions. Thus polynomial in \(r\) can still mean exponential in the number of genuinely relevant components. This is a generic-risk caveat, not a theorem that compression can only discard irrelevant components. The following independently reviewed family supplies a nontrivial exception.

This restriction is not being offered as a validation of unknown interacting architecture discovery. It is a precise sufficient certificate theorem and a checkable account of what the additional assumption buys.

### A nonvacuous state-emitting family with rank 2n

The following family shows that the restricted theorem can be genuinely compact while every hidden bit remains predictively relevant. This example and its exact small-instance check are detailed in `Compact_Certificate_Checker_and_Nonvacuity_Review.md`.

Let \(n\ge2\), use binary components indexed \(0,\ldots,n-1\), and write \(\chi_S(x)=(-1)^{\sum_{i\in S}x_i}\). Put

\[
 \mathcal C=\{\{0\}\}\cup\{\{j\},\{0,j\}:1\le j<n\},\qquad
 q=2n-1,
\]

and let \(\sigma\) be a single cycle on \(\mathcal C\). Define the parity-transfer channel

\[
 M_{S,T}(x'\mid x)=2^{-n}\bigl[1+\chi_S(x')\chi_T(x)\bigr],
\]

which samples uniformly subject to output parity \(\chi_S(x')=\chi_T(x)\). Let \(J\) be uniform resampling and set

\[
 D=\tfrac12 I+\tfrac14 J+
     \tfrac1{4q}\sum_{S\in\mathcal C}M_{S,\sigma(S)}.
\]

All weights are positive and sum to one; every entry of \(D\) is at least \(1/(4\cdot2^n)\). Walsh orthogonality gives

\[
 \chi_SD=\tfrac12\chi_S+\tfrac1{4q}\chi_{\sigma(S)}
       \quad(S\in\mathcal C),
\]

while every other nonconstant Walsh row is multiplied by \(1/2\). Hence \(D\) is invertible. Observe only bit 0 after transition:

\[
 H_{u,y}=E_yDK_u,\qquad E_y=\operatorname{diag}\mathbf1\{x_0=y\},
\]

with the rich one-site controls of the theorem. The space

\[
 W=\operatorname{span}\{1,\chi_S:S\in\mathcal C\}
\]

is invariant under the local algebras, \(D\), and multiplication by the observed-bit indicators. Conversely the observed central contrast, its \(D\)-iterates and inverse-invariance generate the entire cycle \(\mathcal C\). Thus \(W\) is exactly the predictive rowspace and, by full linear reachability,

\[
 r=2n\ll 2^n=N.
\]

Every singleton contrast is in \(W\). Therefore any two distinct hidden point configurations have different controlled future laws: this compression does not merely delete irrelevant coordinates. It does not say all mixed hidden distributions are distinguishable, or establish the minimum size of every alternative positive realization.

The physical implementation uses an explicitly charged shared selector with \(q+2=2n+1\) branches: identity, uniform resampling, and the parity channels. Each parity branch uses only a constant-size input parity and output constraint after its branch is selected, because \(|S|,|T|\le2\). The selector and its broadcast are real interface resources, not free independent noise.

There is also an explicit polynomial checker. Since

\[
 M_{S,T}=J+2^{-n}\chi_S^T\chi_T,
\]

and each character factors across sites, the transition has \(O(n)\) product-matrix terms after collecting the common \(J\) term. Multiplying by a unary output indicator and a one-site actuator preserves this format. A squared residual for a rank-\(s\) CP quotient expands into \(O(s^2n^2)\) product pairs, each contracted site by site in polynomial time. No hidden-state enumeration or unsupported graph-width claim is needed. Uniform product initialization is already a compact stationary idle initializer; sparse replacement is unnecessary in this example.

This provides a concrete interacting, all-bits-relevant benchmark for the restricted certificate theorem. The strong calibration hypothesis and shared-selector resource remain explicit, and no physical-architecture identifiability or priority claim follows from it.

## 7 What is established and what remains genuinely open

**Established:** a proposed positive local realization can be certified against a learned compact observable model by a finite simulation proof; a supplied small contraction proof makes that check cheap; initialized rank alone does not guarantee such a quotient; static graph width and observable rank do not guarantee small CP/TT witnesses; a circuit-and-rewrite witness can succeed where TT witnesses are exponentially large; strong local calibration gives a complete CP witness class.

**Not established:** a polynomial-time proposer; a uniformly small witness for every observationally correct interacting architecture; identification of the physically true components or wiring; a general finite-data theorem; minimal architectural resources; uniqueness modulo a fully characterized equivalence; or a new positive-realization theorem.

An accepted certificate proves a compatible positive joint realization **within the proposed interface/resource class**. It does not exclude a common-driver model or another observationally equivalent assembly. Those alternatives must be retained unless intervention assumptions distinguish them.

The next executable mathematical target is therefore not a generic claim that decomposition checking is easy. It is a chosen **proof-carrying realization language**, with a sound local proof checker and a completeness/resource theorem for a meaningful interacting family. The clocked-circuit example supplies a concrete test: a language restricted to TT quotients fails; a language that admits decoder circuits with locally checkable cancellation proofs succeeds. Extending that success to stochastic interacting mechanisms without assuming full hidden calibration remains the substantive open step.

## Related audits

The separate files `Compact_Certificate_Prior_Art.md`, `Compact_Certificate_Independent_Review.md`, and `Compact_Certificate_Checker_and_Nonvacuity_Review.md` record independent review where available. The structural algebra, sparse initialization, weighted-automata simulation and tensor-contraction ingredients all have established antecedents; absence of the exact combined statement from a search is not evidence of novelty.

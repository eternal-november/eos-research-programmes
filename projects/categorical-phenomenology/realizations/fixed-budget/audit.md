# Audit: fixed-budget polynomial residuals and open-gradient functoriality

Audit date: 3 November 2026. Budget means the number of available hidden-state slots, not the number of optimization iterations.

## 1. Verified source theorem and exact scope

Hanks, Fairbanks and Klawonn, *Generalized Gradient Descent is a Hypergraph Functor*, EPTCS 429 (2025), 217–233, DOI [10.4204/EPTCS.429.12](https://doi.org/10.4204/EPTCS.429.12), [arXiv:2403.19845v2](https://arxiv.org/html/2403.19845v2), Theorem 3.5 and Corollary 3.5.1:

An optimization domain `(C,R)` consists of a Cartesian reverse derivative category, additive inverses, commutative-ring structure on points, and an ordered scalar ring. The map

\[
 f\longmapsto-\mathrm R[f]\circ\langle\mathrm{id},1\rangle
\]

is a monoidal natural transformation from objective decorations to dynamics decorations. If `Lin(C)` additionally has finite limits, it induces an identity-on-objects hypergraph functor on decorated spans. Span legs are linear. Objective pullback is precomposition; dynamics pullback uses the dagger. The proved result concerns negative-gradient fields. It preserves composition, tensor, identities and Frobenius wiring structure. It does not state that minima, feasible witnesses, convergence or computational complexity are preserved. The paper's stated novelty extends earlier Euclidean objective-composition results to general reverse-derivative settings.

This is the relevant source summary. The specialized statements, constructions, counterexamples and proofs below are independent deductions for the proposed fixed-budget encoding.

## 2. Exact polynomial fixed-budget objective

Fix an integer K and finite problem data. The derivation uses K labelled hidden-state slots. Let `x` collect all real variables

\[
 x=(d_{vh},\eta_v,a_{jv},\rho_{jv},\sigma_{jv},b_{vs},\tau_{vs}).
\]

Here `d` selects a compatible tuple of local states, `e_v=Σ_h d_vh` indicates an active slot, `a` gives root-to-slot weights, and `b` gives slot-to-retained-state weights. Constants such as local factors `A_i,B_i`, retained marginal `w`, observable map `Q`, and target `R` are data coefficients, not optimization variables. The residuals in the exact encoding are:

\[
\begin{aligned}
&d_{vh}^2-d_{vh},\\
&1-e_v-\eta_v^2,\\
&a_{jv}-\rho_{jv}^2,\quad e_v-a_{jv}-\sigma_{jv}^2,\\
&b_{vs}-\tau_{vs}^2,\quad\sum_s b_{vs}-e_v,\\
&\sum_{s:\pi_i(s)=t}b_{vs}-\sum_h d_{vh}B_i(h_i,t),\\
&\sum_v a_{jv}\sum_{h:h_i=u}d_{vh}-A_i(j,u),\\
&\sum_{j,v}a_{jv}b_{vs}-w_s,\\
&\sum_{v,s}a_{jv}b_{vs}Q_{su}-R_{ju}.
\end{aligned}
\]

The displayed list uses the exact definitions of indices and stochastic conventions in `report.tex`. Every displayed residual has degree at most two. No additional hidden factorization assumptions are supplied by the gradient theorem.

At a common real zero, `d_vh` is binary and `e_v≤1`; hence `e_v∈{0,1}`. The inequalities encoded by square slack variables yield `0≤a_jv≤e_v≤1`, `b_vs≥0`, and `Σ_s b_vs=e_v≤1`. Therefore all listed base variables satisfy `|x_l|≤1` at a common zero.

Define the actual objective, without additional companions, by

\[
 \Phi_K(x)=\sum_{\alpha\in\mathcal R_K}r_\alpha(x)^2.
\]

It is a real polynomial of degree at most four, with negative gradient of degree at most three. Because every term is a square, its real zero set is exactly the common zero set of the residuals.

**The actual displayed gated objective is already coercive.** This was independently checked against the proof in `report.tex`. On a sublevel `Φ_K≤M`, put `ε=√M`. Every residual has absolute value at most `ε`. The selector residuals bound `d`; their sum bounds `e`. The cap bounds `η`. Adding the two root-slack identities gives `ρ²+σ²=e−P−G`, which bounds both square slacks; `a=ρ²+P` then bounds `a`. Similarly `Σ_s τ_vs²=e_v+N_v−Σ_s T_vs` bounds every `τ`; `b=τ²+T` bounds every `b`. All coordinates are thus bounded on every sublevel. Closed sublevels are compact, proving coercivity and global attainment.

Consequently **minimum zero, infimum zero, and existence of a common real residual zero are equivalent for this particular objective**. If the fixed-budget residual system is infeasible, its attained minimum is strictly positive. This conclusion uses the selector/gate/normalization equations, not a generic property of sum-of-squares polynomials.

An optional redundant completion introduces `z_l` and adds `c_l=x_l²+z_l²−1`. All exact solutions have `|x_l|≤1`, so this preserves zero feasibility. The completed quartic

\[
 \widetilde\Phi_K(x,z)=\Phi_K(x)+\sum_{l=1}^{n_K}(x_l^2+z_l^2-1)^2
\]

has the short Cauchy–Schwarz bound

\[
 \widetilde\Phi_K(x,z)\ge\frac{1}{n_K}\bigl(\|(x,z)\|^2-n_K\bigr)^2.
\]

This completion is not needed for attainment of the original objective. It doubles the variables and changes the gradient field, so it must be named as a different, optional objective rather than silently substituted. The bound assumes `n_K>0`; zero-dimensional instances consist of constant residuals.

Neither coercivity proof gives an algorithm guaranteed to find the global optimum.

## 3. Euclidean and polynomial CRDC applicability

Two valid choices are available:

- `C=Euc`, objects finite-dimensional Euclidean spaces and morphisms smooth functions; scalar object is the real line.
- `C=Poly_R`, where the coefficient ring is specifically the real numbers, objects are natural-number dimensions, and morphisms are real polynomial tuples; scalar object is dimension one.

In either choice the linear maps are real matrices, the dagger is transpose, and finite limits exist in the linear subcategory: a pullback is the kernel of a suitable block matrix, expressed in finite-dimensional coordinates. Reverse differentiation is the usual Jacobian-transpose operation. The polynomial choice remains closed under polynomial composition, differentiation, addition and linear precomposition. Therefore the fixed-K polynomial objective satisfies the algebraic hypotheses without a relaxation.

Do not replace the real coefficient field by an arbitrary commutative ring and silently assume finite limits of finite free modules: kernels need not be finite free there. Do not infer an ordered optimization domain for an arbitrary finite field. Neither generalization is needed here.

## 4. Decorated-span realization and proof of the composition law

Allocate each residual to exactly one factor box. A box `i` has parameter space `N_i=R^{n_i}`, left/right boundary spaces `L_i,R_i`, and coordinate projections

\[
 L_i\xleftarrow{\ell_i}N_i\xrightarrow{r_i}R_i.
\]

Decorate it with the sum of squares of its owned residuals, `f_i:N_i→R`. Slot-local gate, selector, row and circle residuals can be owned by their slot boxes. A root equation, retained-state equation or observable equation involving a sum over slots is a global factor and must occur once. It can expose all the slot coordinates it needs through linear projection legs.

For two boxes

\[
 X\xleftarrow{\ell}N\xrightarrow{r}Y,\qquad
 Y\xleftarrow{s}M\xrightarrow{t}Z,
\]

take the linear pullback

\[
 P=\{(n,m):rn=sm\},\qquad b_N:P\to N,\quad b_M:P\to M.
\]

After choosing Euclidean coordinates on `P`, the composite decoration and negative-gradient field are

\[
 F(p)=f(b_Np)+g(b_Mp),
\]

\[
 -\nabla F(p)=b_N^T[-\nabla f(b_Np)]
                    +b_M^T[-\nabla g(b_Mp)].
\]

Proof: differentiate the two summands with the ordinary chain rule and use linearity of differentiation. This proves precisely the required compatibility for this fixed-budget construction. Tensoring independent boxes uses a product of parameter spaces and adds their losses. The empty decoration is the zero polynomial. Copying a parameter creates several uses of the same coordinate; the transpose collects the associated derivative contributions by addition.

For many boxes let `A_i:R^n→N_i` extract their local parameters from a global vector. The complete formula is

\[
 \Phi_K(\theta)=\sum_i f_i(A_i\theta),\qquad
 -\nabla\Phi_K(\theta)=\sum_i A_i^T[-\nabla f_i(A_i\theta)].
\]

Thus distributed gradient evaluation and centralized gradient evaluation agree exactly in real arithmetic when every local gradient is evaluated at projections of the same current global state. This is a representation theorem for the field. It does not say that separately optimizing every box and gluing the answers solves the joint problem.

### Affine data are not affine span legs

Constants in affine constraints cause no difficulty inside polynomial residuals. But a nonzero-translation affine map is not a morphism of `Lin(Euc)`. For a desired constraint `B_iθ_i+c_i=z`, introduce a shared boundary coordinate `z` and place the affine residual `B_iθ_i+c_i−z` in an owned box; share the actual coordinates using linear projections. Alternatively parameterize an affine solution set after proving it nonempty and keep its offsets in objective coefficients. Simply declaring affine legs to be linear does not satisfy the cited theorem.

### Metric qualification

Choose the global coordinates and Euclidean inner product explicitly. For a general invertible matrix `A`, the gradient-pullback formula is `Aᵀv(Ax)`, not the trajectory-conjugacy formula `A⁻¹v(Ax)`. These coincide for orthogonal coordinate changes, not all invertible changes. In particular, identifying a diagonal subspace with one shared coordinate and equipping it with the standard metric is not the same as automatically using its inherited product-space metric. Algebraic preservation of decorated-span structure must not be described as arbitrary-coordinate invariance of ordinary gradient trajectories.

## 5. Overlaps: additive objectives do not deduplicate constraints

Suppose a global residual `r_e` is present in `m_e` local boxes. Sharing its variables identifies those variables but leaves the composite objective contribution equal to `m_e r_e²`. The hypergraph construction has no automatic inclusion–exclusion or duplicate-removal operation.

Three correct conventions are:

1. Assign every global residual one owner.
2. Use fixed nonnegative weights `ω_ie` with `Σ_i ω_ie=1` over its occurrences, so the composite contribution is exactly `r_e²`.
3. Intentionally accept a positive multiplicity weight, while acknowledging that the objective landscape, gradient and conditioning have changed.

Positive multiplicities preserve the common zero set but not the optimizer dynamics. Negative inclusion–exclusion coefficients can destroy nonnegativity and the zero-loss certificate. Global budget or aggregate equations cannot be split into local equations without a separate equivalence proof. If a global sum must be distributed, expose its required variables or introduce explicit aggregate constraints, rather than quietly summing several copies of the same global constraint.

## 6. Flow, Euler steps, and what preservation does not imply

The field gives the ODE `θdot=−∇Φ_K(θ)`. A synchronized discrete step is `θ_next=θ−η∇Φ_K(θ)`. For a one-step compositional statement the discrete dynamics decoration must collect increments, not entire next states:

\[
 D_{\mathrm{disc}}(A)(u)=\mathrm{id}+A^T(u-\mathrm{id})A.
\]

Then `Euler_η(v)=id+ηv` is natural, as direct substitution verifies. Using the continuous decorator `D(A)(u)=AᵀuA` for next-state maps is wrong in general: its identity term is `AᵀA`, rather than `id`. This distinction is already explicit in the prior sources below, and is a qualification of which target category to use, not a challenge to the negative-gradient theorem.

Even with that correct one-step target, performing T local steps independently and then composing their endpoint maps is not generally equivalent to T synchronized global steps. For `f(x)=g(x)=x²/2`, two global steps multiply `x` by `(1−2η)²`. Composing the two local two-step increments multiplies it by `2(1−η)²−1`, differing by `2η²`.

The following assertions require separate arguments and do not follow from functoriality:

- Convergence of a chosen numerical method or step-size rule.
- Global optimality of a stationary point or local optimum.
- Vanishing loss for a feasible instance from an arbitrary initialization.
- A positive numerical loss as a certificate of infeasibility.
- Polynomial runtime, a spectral-gap bound, or tractability of optimizing a quartic.
- Preservation of independently selected minimizers under composition.
- Identification of the smallest feasible hidden-state budget without a separate budget search and exact feasibility method.

For the actual fixed-budget encoding there is already an explicit stationary obstruction: set every `d,a,b,ρ,σ,τ` to zero and every `η_v=1`. All local residuals vanish. The remaining global target residuals are the fixed negatives of `A_i,w,R`, while their variable-dependent terms are bilinear, whose derivatives vanish at this point. Therefore the gradient is zero and the loss is strictly positive under normalized nonzero target mass, even on an instance that has a zero elsewhere. A gradient method initialized there cannot move.

A concrete counterexample to local optimization as certification is

\[
 h(t)=(t^3-3t+3)^2.
\]

It is a nonnegative polynomial with an attained global minimum zero because the cubic has a real root. Nevertheless `t=1` is a strict local minimum with `h(1)=1` and `h''(1)=12`. A gradient method initialized exactly there stays at positive loss. Coercivity of the gated model establishes attainment, but does not establish a benign optimization landscape.

For comparison, without an attainment argument, even infimum zero need not certify feasibility: `x²+(xy−1)²` has infimum zero, approached by `(x,y)=(1/n,n)`, and has no zero. The sublevel proof for the actual gated objective correctly avoids this specific gap.

## 7. Direct antecedents and safe novelty wording

### Strongest direct antecedent

Tyler Hanks, Matthew Klawonn, Evan Patterson, Matthew Hale and James Fairbanks, *A Compositional Framework for First-Order Optimization*, [arXiv:2403.05711](https://arxiv.org/html/2403.05711), submitted 8 March 2024. Theorem 3.3 establishes Euclidean gradient flow as an algebra morphism; Corollary 3.3.1 gives discrete gradient descent. It also treats Uzawa and subgradient variants. Example 2.12 explicitly distinguishes continuous wiring from discrete increment-based wiring. Consequently a claim that the present construction newly proves compositional Euclidean gradient descent would not be supportable.

### Discretization antecedent

Sophie Libkind, Andrew Baas, Evan Patterson and James Fairbanks, *Operadic Modeling of Dynamical Systems: Mathematics and Computation*, EPTCS 372 (2022), 192–206, DOI [10.4204/EPTCS.372.14](https://doi.org/10.4204/EPTCS.372.14), [arXiv:2105.12282v3](https://arxiv.org/html/2105.12282v3). Proposition 3.1 defines undirected composition of discrete systems using increments; Proposition 3.3 proves naturality of Euler discretization. This supports the corrected discrete target above.

### Categorical infrastructure and optimization antecedents

- Brendan Fong, *Decorated Cospans*, TAC 30 (2015), 1096–1120, [arXiv:1502.00872](https://arxiv.org/abs/1502.00872). The decorated-(co)span construction and passage from monoidal natural transformations to structure-preserving functors predate the optimization application.
- Robin Cockett et al., *Reverse Derivative Categories*, CSL 2020, DOI [10.4230/LIPIcs.CSL.2020.18](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CSL.2020.18). This supplies the reverse-derivative axioms and dagger structure on linear maps.
- Dan Shiebler, *Generalized Optimization: A First Step Towards Category Theoretic Learning Theory*, [arXiv:2109.10262](https://arxiv.org/abs/2109.10262). It supplies generalized optimization in this setting and explicitly distinguishes orthogonal invariance of gradient descent from general invertible-linear invariance of Newton's method.
- G. S. H. Cruttwell, Bruno Gavranović, Neil Ghani, Paul Wilson and Fabio Zanasi, *Categorical Foundations of Gradient-Based Learning*, [arXiv:2103.01931](https://arxiv.org/abs/2103.01931), ESOP 2022. Its lenses, parameterized maps and reverse derivatives concern compositional models and training structure; it is another substantial antecedent, not the same fixed-budget feasibility construction.

Safe claim: **The fixed-budget real polynomial encoding gives a particular family of objectives to which existing open-objective gradient-functor machinery applies. Its additive decomposition and gradient identity are an application of that machinery. Any contribution lies in proving the exact bounded-state feasibility encoding, handling inactive slots, gluing, residual ownership and attainment, not in claiming a new general gradient functor or a new convergence theorem.**

This audit does not establish that the fixed-budget encoding itself is globally novel. Such a claim would require a wider literature comparison in the specific hidden-factorization problem, including its exact compatibility and marginal constraints.

## 8. Optional separate analytic conclusion for this coercive polynomial

One may prove more about the **particular** gated objective using analysis, without attributing it to the hypergraph theorem. Along its exact Euclidean gradient flow,

\[
 \frac{d}{dt}\Phi_K(\theta(t))=-\|\nabla\Phi_K(\theta(t))\|^2\le0.
\]

Coercivity keeps the trajectory in a compact sublevel set; the polynomial vector field is locally Lipschitz there, so the forward trajectory exists for all time. The Łojasiewicz convergence theorem for bounded real-analytic gradient trajectories then gives convergence to a single critical point. This point need not be a zero or a global minimizer. Arbitrary fixed-step discrete gradient descent is not covered by this flow argument; numerical descent convergence requires suitable step/descent hypotheses.

Reference: P.-A. Absil, R. Mahony and B. Andrews, *Convergence of the Iterates of Descent Methods for Analytic Cost Functions*, SIAM Journal on Optimization 16(2) (2005), 531–547, DOI [10.1137/040605266](https://doi.org/10.1137/040605266), [author-hosted article](https://sites.uclouvain.be/absil/Publi/Convergence_SIOPT/13-60526.pdf). Its analytic convergence theory is logically separate from the categorical compositionality theorem.

## 9. Verification of optional real-algebraic certificates

Two author-hosted primary sources were checked:

- Pablo A. Parrilo, *Semidefinite programming relaxations for semialgebraic problems*, Mathematical Programming 96 (2003), 293–320, DOI [10.1007/s10107-003-0387-5](https://doi.org/10.1007/s10107-003-0387-5), [article](https://www.mit.edu/~parrilo/pubs/files/SDPrelaxations.pdf), §4.2, Theorem 4.6, printed p. 305. With no inequalities or disequalities, the generated cone is the sum-of-squares cone and the generated monoid contains only 1. The theorem therefore specializes exactly to: a polynomial equality system `F_i=0` has no real solution iff there is an identity `−1=Σ_i q_i F_i+Σ_l r_l²` with real polynomial coefficients. Its direct sufficiency follows by evaluating at a purported zero. The cited theorem supplies necessity; neither bounded degree nor a short certificate follows here.
- Saugata Basu, *Algorithms in Real Algebraic Geometry: A Survey*, [author manuscript](https://www.math.purdue.edu/~sbasu/raag_survey2011_final-sep4-2014.pdf), §1.1, printed p. 2, and Theorem 2.1, printed p. 5. The former identifies both the real numbers and real algebraic numbers as real closed fields; the latter gives quantifier elimination. The rational-coefficient existence sentence consequently has the same truth value over these two fields. Thus a nonempty rational polynomial zero set has an algebraic-real witness. For an infeasibility identity, fix the finite degrees, supports and number of square terms of one real certificate; its coefficient-matching equations form another rational existential sentence. Transfer then provides real-algebraic certificate coefficients. This does not assert rational witnesses, rational certificate coefficients, or polynomial certificate size.

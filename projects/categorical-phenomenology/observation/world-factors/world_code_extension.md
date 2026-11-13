# Affine response factors: certifying relations is not identifying their probability law

**Status.** Checked derivation for comparison and review, not a novelty claim. The extension makes the structural distinction in `world.md` sharper. Its testing mathematics is closely related to standard locally testable linear codes, not an independent new coding theorem.

## 1. Model and two different unknowns

Use binary coordinates `F₂^m`, m≥1. Let the proposed affine response code be

`A=c+V`, where `V≤F₂^m` has dimension r.

The code is supplied or fixed using independent training. Its discovery and selection costs are not included in the certification theorem. H is a finite family of allowed contexts J. Each query returns `X_J` from a fresh independent X with one arbitrary unknown law μ. The same-unit coupling and no-extra-probes restrictions from the main report apply. The context is selected before observing the current unit, and all context samples have marginals of the same stationary law. Empty contexts can be discarded because they reveal nothing. All logarithms below are natural; `kl(p,q)=p log(p/q)+(1−p)log((1−p)/(1−q))` denotes binary relative entropy, with the usual endpoint conventions.

There are two different questions:

1. **Structural certification:** Is μ supported on A, or at least close to some law supported on A?
2. **Internal-law identification:** Assuming support in A is established, do the available context marginals determine the probability law over the r effective bits?

These questions have different exact answers. The first uses a **linear span of local dual constraints**. The second uses **set coverage of character classes**, not the linear span of those classes.

The object A is a candidate small response factor, not necessarily a set of latent causal coordinates. No intervention on an effective bit is supplied by this representation alone.

## 2. Which local experiments can certify the support?

For context J, let

`D_J={a∈V⊥ : supp(a)⊆J}`.

The local membership test accepts x exactly when `x_J∈c_J+π_J(V)`. Elementary duality gives

`x_J∈c_J+π_J(V) ⇔ a·(x−c)=0 for every a∈D_J`.

Let `D=span(∪_(J∈H)D_J)`. The responses satisfying every local membership test form precisely

`A_H=c+D⊥`.

Thus local tests characterize A if and only if `D=V⊥`. If D is smaller, an entire coset outside A passes every local membership test. The uniform law on a suitable such coset has exactly the same available context marginals as Uniform(A), so even raw local outcomes cannot distinguish those two laws.

**Proof of local duality.** A vector a supported on J annihilates V exactly when its J-restriction annihilates π_J(V). In a finite vector space, a subspace equals its double annihilator. Intersecting the local annihilator conditions gives D⊥. ∎

The span is justified here because these are equations holding on the response support. If `a·x=b` and `a'·x=b'`, then adding them is a valid pointwise consequence. This is not an inference that separate expectations determine their products.

## 3. The exact context-design LP

Let Q=`F₂^m/V`. For a nonzero class `[z]∈Q`, define

`d(J,[z])=1{z_J∉π_J(V)}`.

This is well-defined on the coset. Define

`τ_A(H)= min Σ_J w_J`

subject to `w_J≥0` and `Σ_J d(J,[z])w_J≥1` for every nonzero coset.

If a nonzero coset is undetectable, τ=∞. Otherwise τ is finite and at least 1, provided A is a proper subset of the cube. The special case A=`F₂^m` has no bad cosets: set τ=0 and certify support with zero samples. Do not substitute τ=0 into a sampling formula containing division by τ.

It follows from Section 2 that

`τ_A(H)<∞ ⇔ span(∪_J D_J)=V⊥`,

with the full-space case included on the left by τ=0.

### Theorem A. Certification upper bound

Suppose A is proper and `1≤τ<∞`. Sample contexts independently with probabilities `λ_J=w_J/τ` for optimal weights, and reject on a local membership violation. For every μ,

`P(one trial rejects) ≥ μ(Aᶜ)/τ`.

Consequently, for `0<ε<1` and `0<δ<1/2`,

`N=ceil[log(δ)/log(1−ε/τ)] ≤ ceil[(τ/ε)log(1/δ)]`

trials distinguish support in A from `μ(Aᶜ)≥ε` with false acceptance at most δ and perfect completeness. A confidence upper limit is `U_N=min{1,τ(1−δ^(1/N))}` after no violation, and U_N=1 otherwise. For a prespecified integer N≥1, its precise guarantee is `P_μ[μ(Aᶜ)>U_N]≤δ` for every μ. This is not conditional coverage given acceptance, not an anytime-valid bound under arbitrary optional stopping, and not tolerant estimation. The zero-sample full-space case is handled separately by U_0=0.

**Proof.** Each x outside A belongs to a nonzero coset `[x−c]`. Its probability of triggering a sampled local test is at least 1/τ. Average over μ, then use independent zero-violation probabilities. ∎

### Theorem B. Adaptive lower bound for raw context observations

Assume A is proper, `1≤τ_A(H)<∞`, `0<ε<1`, and `0<δ<1/2`. Let `q_0=Uniform(A)`. Consider an adaptive, possibly sequential tester that stops almost surely under the compared laws, has finite expected query count under q_0, accepts q_0 with probability at least 1−δ, and accepts every μ with `μ(Aᶜ)≥ε` with probability at most δ. Then

`E_(q_0)N ≥ τ_A(H) kl(1−δ,δ)/[−log(1−ε)]`.

**Proof.** For each nonzero coset [z], put

`q_z=Uniform(c+z+V)`, and `μ_z=(1−ε)q_0+εq_z`.

These affine cosets are disjoint. Thus `μ_z(Aᶜ)=ε` and `TV(μ_z,q_0)=ε`.

A uniform law on a linear subspace projects uniformly onto its image: every nonempty projection fiber has equal cardinality. Therefore q_0 and q_z project either to exactly the same uniform local law, when `d(J,[z])=0`, or to uniform laws on disjoint affine cosets, when `d(J,[z])=1`. In particular,

`KL(q_(0,J) || μ_(z,J))=d(J,[z])[-log(1−ε)]`.

Let K_z count queries with d(J,[z])=1. On any finite stopped transcript with positive q_0 probability, the null-to-alternative likelihood ratio is exactly `(1−ε)^(−K_z)`: the context-selection and stopping kernels cancel, while each observed-outcome ratio is either 1 or `1/(1−ε)`. Almost-sure stopping and finite `E_(q_0)N` therefore give transcript relative entropy `E_(q_0)K_z[−log(1−ε)]`. Only null-to-alternative absolute continuity is used; the reverse direction fails when an informative context is queried. Data processing at the acceptance event then gives

`Σ_J E_(q_0)N_J d(J,[z])[-log(1−ε)] ≥ kl(1−δ,δ)`.

Rescale the expected counts to a feasible LP solution. The result follows. ∎

As before, a certificate with only strict bad alternatives `μ(Aᶜ)>ε` gets the displayed lower bound by using contamination η>ε and taking η↓ε. Null completeness is necessary. The lower bound is at the uniform code law, not at every distribution within A. For `ε≤1/2, δ≤1/4`, upper and lower bounds give order `τ ε^(−1)log(1/δ)` in this restricted interface.

If τ=∞, uniform A and a locally invisible uniform coset have identical available marginal laws and TV distance 1. Adaptivity across fresh units cannot help.

## 4. Best-fit TV and an actual factor representation

For any nonempty finite subset A and any μ,

`inf_(ν:ν(A)=1) TV(μ,ν)=μ(Aᶜ)`.

Any retraction R onto A, meaning `R(a)=a` for a∈A, attains this bound through `q=R_#μ`. On A the pushforward adds only nonnegative mass, and outside A it is zero.

For an affine code, choose an information set I of r coordinates for which `π_I:V→F₂^r` is bijective. Let `φ:F₂^r→A` be the corresponding affine inverse of projection. Then

`R(x)=φ(x_I)` and `q=φ_#μ_I`.

The structural certificate gives `TV(μ,q)≤ε`, but it does not automatically provide μ_I. If I can be jointly observed, this r-bit law can be estimated separately. For `0<η<1` and `0<δ_r<1`, with K=`2^r` possible values, the elementary union-of-subsets Hoeffding bound gives

`n≥[K log2+log(1/δ_r)]/(2η²)`

for empirical TV error at most η. The integer sample count is the ceiling of this expression. Structural error ε and internal-law estimation error η then add, and their failure probabilities add by a union bound. This is a bound on the probability of issuing an inaccurate output, not a conditional guarantee given that validation accepts. For r=0 the internal law is known without samples; the displayed sufficient bound is unnecessary. Thus a small number of relations or a sparse check matrix does not by itself make the factor-law estimation inexpensive.

If an information-set context is unavailable, other contexts can still identify the internal law, but only under the character-coverage criterion below. If it fails, a structural support certificate can remain useful for particular targets without identifying all factor probabilities. Theorem C assumes exact support in A. Using a reconstruction from other contexts when support is only approximate requires a separate error-propagation bound for that reconstruction; exact identifiability alone supplies neither stability nor efficient sampling.

## 5. Which distributions inside the factor are identifiable?

Assume for this section that support in A is known, and consider the entire model class `Δ(A)`. For a binary vector a, the character `χ_a(x)=(-1)^(a·x)` restricted to V depends only on the class

`[a]∈F₂^m/V⊥`.

On the affine translate A the restrictions differ by a known sign determined by c. A canonical way to remove that sign ambiguity is to use `ψ_[a](c+v)=(-1)^(a·v)`, which is independent of the representative because every element of V⊥ annihilates v. There are `2^r` distinct character classes, forming a basis of real functions on A. Observed raw characters give their expectations after multiplication by the known factor `(-1)^(a·c)`.

Define the accessible class set

`K_H={ [a] mod V⊥ : supp(a)⊆J for at least one J∈H }`,

and include the constant class even if H is empty.

### Theorem C. Internal-law boundary

With exact population context marginals (an ideal identifiability statement, not exact recovery from finitely many samples), the space of expectation functions determined uniformly over `Δ(A)` is the span of the character classes in K_H. Therefore:

- the measurement map on laws supported in A has rank `|K_H|`;
- the full internal law is identifiable if and only if `K_H=F₂^m/V⊥`;
- at any data fiber containing a law strictly positive on A, its affine dimension is `2^r−|K_H|`;
- a specific target is identified if and only if all its nonzero Fourier classes lie in K_H.

**Proof.** A function depending on coordinates J is a linear combination of characters a supported on J. Restricting to A identifies characters precisely modulo V⊥, up to known affine signs. Distinct classes are linearly independent on A. Apply the row-space identifiability argument from the main report. For necessity, a missing nonconstant class [a] gives the probability masses `p_±(c+v)=2^(−r)(1±t ψ_[a](c+v))`, with `0<t≤1`. The nonconstant character has zero sum on V, so these masses are normalized and nonnegative. Its orthogonality to every accessible class makes all observed context marginals agree, while its own expectation is ±t. ∎

**Do not replace class coverage by its linear span.** Knowing `Eχ_a` and `Eχ_b` generally does not determine `Eχ_(a+b)`. Their product character is the very unknown interaction. This differs from Section 2, where adding equations known to hold pointwise is valid.

At a boundary fiber with additional zeros, feasible support can be smaller than A and the identifiability rank can improve. The theorem's uniform statement and full-support-fiber qualification are intentional.

## 6. Two opposite finite examples and edge cases

### A. The factor can be certified, but its internal coupling is unknown

Let

`V={(u,u,v,v):u,v∈F₂}`, and `H={{1,2},{3,4}}`.

Each pair tests an equality constraint. These two constraints span V⊥, and τ=2. Thus support in this two-bit response factor is certifiable.

Inside V, however, the observations reveal only the separate marginals of u and v. Accessible character classes are `1,(-1)^u,(-1)^v`; the fourth class `(-1)^(u+v)` is absent. The internal-law rank is 3 rather than 4, and a generic fiber has one free coupling parameter.

Add the cross-context `{1,3}`. It contains no new local support constraint, so τ remains 2. But it directly observes `(u,v)`, raises internal-law rank to 4, and identifies the whole factor law. An experiment can improve distribution identification without improving support certification at all.

### B. The internal law would be identified if the factor were true, but the factor cannot be certified

Let

`V={x∈F₂^3:x_1+x_2+x_3=0}`, and take all three singleton contexts, any one pair context, or all three pair contexts.

Any pair is an information set for V, so its marginal determines a law supported on V. Even the three singleton marginals identify that law: on V the three coordinate characters are the three distinct nonconstant characters of the two-dimensional factor. But V⊥ is generated by `(1,1,1)`, which is supported in no pair. Every pair projection is the full two-bit cube, so all local membership tests are vacuous and τ=∞.

Uniform even parity and uniform odd parity have the same available pair marginals. Thus identifying parameters **conditional on a model class** is not the same as experimentally warranting that model class. A full three-response context supplies the missing support test.

### C. Edge cases

- If r=m, A is the whole cube. Support certification is vacuous, τ=0, while internal-law identification can remain very incomplete.
- If r=0, A is a singleton. Its internal law is already known, but support certification needs contexts covering every coordinate. The LP reduces to fractional coordinate coverage; singleton contexts give τ=m.
- The signed repetition factor in the main report is the affine r=1 case. Its singleton contexts cannot detect disagreement because its singleton projections are full.

## 7. Direct comparison with established local-code testing

Let `T_local=(∪_J D_J)\{0}`. Define a parity-test design LP whose tests are a∈T_local and whose constraint at y∉V requires total weight at least 1 on tests with `a·y=1`. Call its value σ.

Then

`τ_A(H) ≤ σ ≤ 2τ_A(H)`.

For the first inequality, assign each parity test to a context containing its support. A failed parity implies local membership failure. For the second, replace each context check J by a uniformly random element of D_J. When a context rejects y, exactly half of D_J has odd dot product with y. Doubling the context weight therefore gives a feasible parity design; the zero vector can be removed afterward.

This constant-factor equivalence is **already an explicit result in the local-testing literature**, not a new reduction. Ben-Sasson, Guruswami, Kaufman, Sudan, and Viderman, in _Locally Testable Codes Require Redundant Testers_ (December 2009 manuscript, Section 2, “Remarks on definitions of testers,” PDF pages 4–5), explain the conversion of the most general local linear-code test to a distribution on supported dual words with at most factor-two soundness loss in the binary case. Their results also show why having a spanning basis of checks and having a quantitatively good local tester are different requirements. Their usual soundness notion scales with the Hamming distance of a fixed word; here the objective is the worst nonzero defect coset and the TV mass of a distribution of fresh words. The conversion is the same, but those metrics and interfaces must not be conflated. [Primary paper, definitions and tester-equivalence discussion](https://people.eecs.berkeley.edu/~venkatg/pubs/papers/LTCs-journal.pdf)

Ben-Sasson–Sudan's robust local-testability work concerns local consistency tests and composition for tensor-code constructions. That is stronger and more specialized coding structure than is assumed here; no tensor product of the physical world is inferred by the current response-code formulation. [Primary paper](https://doi.org/10.1002/rsa.20120)

The sequential KL optimization is the same classical controlled-testing principle already credited in the main report. The distinctive synthesis is the separation between (i) validating response relations and (ii) learning a state on the resulting quotient algebra. Neither the linear-code algebra nor local testing is claimed new.

No theorem here learns an unknown code. Candidate discovery may require many samples, a minimum-mass assumption, structural restrictions, or difficult search. A code chosen to interpolate all validation records trivially invalidates the fixed-candidate confidence claim. Independent training, a predetermined candidate family with a complexity correction, or another valid selection-aware procedure is required.

## 8. Algorithmic and categorical consequences

For an explicit generator/parity-check matrix and explicit H, computing each D_J and testing whether their union spans V⊥ is polynomial-time Gaussian elimination. Testing whether one context rejects a response is also linear algebra. The full sampling-design LP can have `2^(m−r)−1` coset constraints. Internal-law coverage can require handling `2^r` character classes. No blanket polynomial-time claim in m follows from the succinct code representation.

These are two dual-size bottlenecks: codimension governs possible structural defect classes; dimension governs possible factor-distribution characters. The existence criterion for structural certification is nevertheless efficient even when optimizing its quantitative design is not known to be so in the chosen representation.

The algebraic picture is concrete. Certified pointwise parity relations define a quotient of the Boolean response-function algebra. A probability law on that quotient is a further object. Partial observations may determine the relations without determining the state, or determine a state conditional on relations that they cannot verify. This is a useful two-way warning for any program that moves directly from observations to an explanatory algebra and treats its stochastic interpretation as automatic.

## 9. Reproduction

Run `python world_code_checks.py`. It writes `world_code_checks_results.json` and checks the two opposite examples, all three rank edge cases, 180 randomized finite code/context instances, 12,724 projected-coset KL identities, and 180 retraction TV identities. It also verifies the two distinct algebraic criteria and `τ≤σ≤2τ` whenever finite. Run `python world_code_exhaustive.py` for every affine subspace and every family of nonempty contexts in dimensions 1, 2, and 3, including the empty family. It checks 6,622 affine code/context-family ranks and 2,092 linear-code/context-family LP classifications, with exact rational primal/dual certificates for every finite nonvacuous optimization. It also checks 1,134 exact projected-coset likelihood ratios, 97 information-set retractions, 463 invisible-coset cases, and 463 missing-character witnesses. Empty contexts have no effect, so omitting them loses no distinct observation model. Run `python world_code_review_checks.py` for independent rational checks of stopped adaptive transcript likelihoods and the two opposite examples. These finite diagnostics supplement the proofs.

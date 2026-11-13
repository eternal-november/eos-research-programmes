# Final review of partial experiment and affine response factor theorems

Reviewed on 3 November 2026.

## Verdict

The repetition-code certification theorem and its affine-code extension are mathematically sound under the stated fresh-unit context interface. No blocking defect remains. The affine extension proves two different boundaries: local dual equations must span the full dual space to certify support uniformly, while accessible character classes must cover the entire quotient to identify an arbitrary law within that support. Linear generation of those character classes is not enough.

The result is a checked synthesis of established linear algebra, Fourier analysis, local testing, and sequential information bounds. It is not a novelty clearance, a general latent-causal discovery theorem, or a physical validation of the observation contract.

## Scope and observation contract

The review covers `world.md`, `world_theorem_frozen.md`, and `world_code_extension.md`, including their computational checks. The earlier review in `world_review.md` remains the detailed audit of the repetition-code theorem. This review independently checks the extension and its consistency with that theorem.

A query chooses one context before seeing a fresh independently prepared unit and returns that context's entire raw response vector. All contexts must be marginals of the same stationary response law. The tester cannot request another context on that same unit. Shared seeds, replay, or physical reset are substantive coupling assumptions, not consequences of collecting unpaired intervention data. The code is fixed independently of validation data. Context trials and individual coordinate evaluations are different costs.

Adaptivity means choosing later contexts or stopping from earlier units' observations. It does not permit within-unit adaptive probing. That stronger interface can invalidate the stated lower bound.

## Support certification criterion

For `A=c+V`, the dual space of the projected code is exactly the restriction of those vectors in `V⊥` whose support lies in the queried context J. Therefore local membership in the projection of A means satisfying precisely those affine parity equations.

Let D be their combined linear span. Intersecting every local acceptance condition gives `c+D⊥`, so it equals A exactly when `D=V⊥`. If D is smaller, choose `z∈D⊥\V`. Every context projection of z lies in the projected code. Uniform(A) and Uniform(c+z+V) then have identical available marginal laws even though their supports are disjoint. The uniformity matters: the claim is not that every distribution on one coset looks like every distribution on the other.

The context-design LP is a finite covering LP indexed by nonzero cosets of V. It is feasible exactly when every such coset is detected. A finite menu with that property has the feasible assignment of unit weight to every context. If A is proper, any one nonzero-coset constraint forces total weight at least one. Affine translation c does not affect the LP.

These arguments justify the algebraic existence criterion and the infinite-cost impossibility statement without relying on numerical tests.

## Statistical upper and adaptive lower bounds

For finite positive τ, normalized optimal weights detect each non-codeword with probability at least `1/τ`. Thus a trial's rejection probability is at least `μ(Aᶜ)/τ`. The independent zero-violation probability is at most `(1−μ(Aᶜ)/τ)^N`, yielding the stated exact ceiling and exponential sample bounds.

The confidence limit applies to a prespecified N. Its unconditional coverage is valid, including strict inequalities at the boundary. It is not a probability statement conditional on validation accepting and is not automatically valid at an arbitrary data-dependent stopping time. Independent training or a valid selection correction is necessary if the candidate was discovered from observations.

For the lower bound, take the null to be Uniform(A), and contaminate it by an ε fraction of a different uniform affine coset. The projection of a uniform affine code is uniform on its image. Two projected affine cosets are either identical or disjoint. The null-to-alternative observation likelihood ratio is consequently 1 on an uninformative context and `1/(1−ε)` on an informative one.

For a stopped null-compatible transcript, the likelihood ratio is exactly `(1−ε)^(−K_z)`, where K_z counts informative queries for the selected coset. Action and stopping kernels cancel. Taking the null expectation yields the transcript relative entropy `E[K_z][−log(1−ε)]`; the finite expected query count ensures integrability. Binary data processing at the acceptance event gives the required `kl(1−δ,δ)` lower bound. Scaling expected context counts gives a feasible covering-LP solution and hence the stated bound on `E_(Uniform(A))N`.

Only null-to-alternative absolute continuity is used. Invoking a mutual-absolute-continuity lemma directly would be invalid. The expanded proof supplies the needed one-direction argument instead. Almost-sure stopping under the compared laws, null completeness, and `0<δ<1/2` are explicit. The lower bound is not a pointwise statement at every distribution supported in A. A tester that never accepts illustrates why soundness alone is insufficient.

For certificates whose bad alternatives have mass strictly greater than ε, use contamination η>ε and let η decrease to ε. For `0<ε≤1/2` and `0<δ≤1/4`, the upper and lower bounds have the same order `τ ε^(−1)log(1/δ)`. They do not have matching exact constants or describe the same fixed-sample optimization objective.

## Internal probability law criterion

On A, the normalized character `ψ_[a](c+v)=(-1)^(a·v)` is well-defined modulo V⊥. Distinct quotient classes are orthogonal under Uniform(A), so they give a real basis of size `2^r`. Restricting context cylinder functions to A spans exactly the accessible character classes. The marginalization rank is therefore the number of distinct covered classes, not the dimension of their binary linear span.

If a nonconstant class is missing, the two laws with masses `2^(−r)(1±tψ_[a])`, `0<t≤1`, are normalized and nonnegative. Orthogonality makes their available marginals identical, while that character's expectations differ by 2t. This supplies a direct necessity witness, including on affine translates with nonzero c.

The rank and target criteria hold uniformly over all laws supported in A. The affine dimension assertion applies to fibers containing a strictly positive law on A. Additional observed zeros can shrink the feasible support and improve identification. Exact population identification does not mean exact recovery from finitely many samples.

The two examples are correct. Disjoint duplicated pairs certify equality support with τ=2 but leave the coupling of the two effective bits unidentified. Adding a cross-pair observes that coupling without improving τ. For the three-bit even-parity code, even the singleton characters cover all three nonconstant factor characters. They identify a law conditional on even parity, although no proper context can test that parity relation against odd parity.

## Retractions and edge cases

Every retraction onto a nonempty finite A produces a pushforward q with `TV(μ,q)=μ(Aᶜ)`, attaining the minimum distance to the class of A-supported laws. An information-set projection gives a specific retraction and a usable representation if that information set can be jointly observed.

The union-over-subsets Hoeffding bound for an empirical K-state law is correct: TV is the maximum signed mass error over all subsets, and all `2^K` subsets are included. Take the ceiling for an integer sample count. Independent structural validation and factor-law estimation yield additive error and a union bound on the probability of issuing an inaccurate output. The statement is not conditional on acceptance.

Important degenerate cases are handled:

- Full code, `r=m`: there are no bad cosets, τ=0, and support is certified without observations. Sampling formulas that divide by τ do not apply. The probability law can still be unidentified.
- Singleton code, `r=0`: the internal law is known without observations, but support certification requires context coverage of every coordinate. Its LP is fractional coordinate coverage, giving τ=m for singleton contexts.
- Empty context family: it reveals only normalization. Every proper code is uncertifiable in the uniform worst-case sense. A singleton still has an identified internal law, and the full code still has vacuously certified support.
- Empty individual contexts reveal nothing and can be removed.
- Missing-character ambiguity and infinite τ are uniform model-class obstructions. Special data at a deterministic boundary can have additional identifying power.

When support is only approximate and the information set cannot be observed, character coverage alone does not bound the error amplification of a reconstruction from other contexts. A separate stability bound is needed. This limitation is now explicit.

## Prior art and claim limits

The local-membership-to-dual-parity conversion was verified in Section 2 of [Locally Testable Codes Require Redundant Testers](https://people.eecs.berkeley.edu/~venkatg/pubs/papers/LTCs-journal.pdf). The attribution is correct. The manuscript does not claim that conversion as new.

The sequential comparator's mutual absolute continuity hypothesis was checked directly in Lemma 1 of [Kaufmann, Cappé, and Garivier](https://jmlr.org/papers/volume17/kaufman16a/kaufman16a.pdf). The one-direction proof here is the appropriate specialization. [Controlled Sensing for Multihypothesis Testing](https://arxiv.org/abs/1205.0858) supplies the broader experiment-design context.

The factor-two parity comparison does not turn this report into a new local-code theorem. Hamming distance of a fixed string, TV mass outside a code, and the permitted probing interface remain distinct. [Testing Distributions of Huge Objects](https://theoretics.episciences.org/12765) is an important adjacent model with a Hamming-based earth-mover metric. The report's claims remain limited to its declared oracle and distance.

The efficient support-existence test uses Gaussian elimination on explicit matrices and contexts. The optimal design can still involve exponentially many defect cosets, and law identification can involve exponentially many character classes. Unknown-code discovery, stability of arbitrary reconstruction, general tolerant testing, latent causal interventions, and blanket polynomial-time learning are not established.

## Reproduced checks

All four scripts completed successfully in Python 3.12.14 with NumPy 2.3.5 and SciPy 1.17.0 where needed.

1. `world_checks.py`: the existing repetition-code and marginal checks passed, including 28 complete-context LP instances, 2,547 raw-context KL calculations, 54 singleton-bias cases, 600 retraction diagnostics, and the reported sample counts.
2. `world_code_checks.py`: 180 randomized finite code/context cases, 12,724 projected-coset KL checks, and 180 retraction checks passed. The largest floating-point residuals were below `7×10^(−16)`.
3. `world_code_exhaustive.py`: all affine codes and context families for m=1,2,3 passed. There were 6,622 exact affine rank checks, 2,092 linear-code/context-family LP classifications, 1,134 projected-coset likelihood checks, 97 information-set retraction checks, 463 invisible-coset cases, and 463 missing-character witnesses. The LP count includes trivial and infeasible cases; every finite nonvacuous numerical optimum is checked by exact rational primal feasibility, dual feasibility, and equality. SciPy locates candidates but does not certify them by tolerance.
4. `world_code_review_checks.py`: an independent pure-Python rational enumeration passed for 870 adaptive query-and-stopping policies and 5,185 terminal likelihood ratios, together with independent versions of the two opposite examples. Its horizon is at most four; the general unbounded-stopping theorem rests on the proof, not this enumeration.

These diagnostics are finite mathematical checks, not a machine-checked formal proof or a physical experiment. The packaged JSON results preserve their scope and counts.

## Changes made during final review

The review made no substantive correction to the theorem's rate or algebraic criteria. It made the parameter ranges and stopping hypotheses explicit, expanded the stopped-transcript proof, normalized affine characters explicitly, clarified the uniform invisible-coset witness, separated fixed-N from anytime coverage, added sample-count rounding and the rank-zero no-estimation case, and warned that exact identifiability alone does not supply stability under approximate support.

The main report now includes the affine extension rather than leaving it as an unlinked continuation. The package includes all four check scripts and their results, the original frozen theorem and prior review, this final review, primary-source links, reproduction instructions, and a SHA-256 manifest.

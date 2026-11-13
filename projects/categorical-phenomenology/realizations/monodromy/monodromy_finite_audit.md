# Focused audit of moment and finite-data claims

**Initial audited revision (superseded; final verification below):** `monodromy_native_report.tex`, SHA256 `4cb0e2a3dadcf102cf2a0c6dab1c1638b699f7d4489c12bfdafddb2be367922d`.
**Scope:** finite moment reconstruction, uniform finite-horizon robustness, primitive-transition corollary, and moving-seam query impossibility.

## Verdict

No substantive error found in these results. The moment criterion correctly constructs a compatible held-mixture law; it does not identify an unrestricted true all-word process. The report explicitly preserves this distinction. The compactness gap and primitive perturbation arguments are sound. The arbitrary-monodromy seam works and retains uniform conditioning because it reparameterizes the original family rather than interpolating to a degenerate default.

## Proof checks

- H-self-adjoint commuting positive operators D_y with sum I have positive probability-vector joint eigenvalues. The relation D_y 1=e_y makes 1 cyclic. Each joint eigenspace is therefore one-dimensional and has nonzero projection of 1, giving three distinct atoms with positive weights. The stated single-, double-, and triple-word moments follow exactly.
- The finite Hankel factorization has full rank p. Equality of inserted-symbol blocks through length 2p-1 gives simultaneous similarity of every outcome matrix. Their sum is I. Nonnegativity forces each outcome matrix diagonal, so the exact p-state parameter fiber consists precisely of the p! relabelled held mixtures. This validates the discrete-fiber premise in the compactness argument.
- The p-state stochastic parameter space is compact. The exact fibers vary continuously as an unordered finite set with uniform separation. Removing fixed-radius neighborhoods yields a compact set with strictly positive finite-word error. A competitor uniformly below that error would give a continuous choice of exact branch, contradicting monodromy.
- A refresh coupling bounds a length-l word discrepancy by l epsilon. Thus a small fixed primitive perturbation remains within the hold family's exclusion gap. Full finite Hankel rank persists by the uniform singular-value margin, and the displayed p-state local model gives the upper rank bound.
- The seam can be formalized on a fundamental interval [a,a+1] with seam [a+1-h,a+1]. Take s=0 before the seam and let it rise smoothly to 1, flat at both ends. Then g(t)=t-s(t) satisfies g(a)=g(a+1)=a and matching endpoint derivatives of every order. V(g(t)) is globally labelled and smooth. The law equals the target outside the seam and is an original family member at every point inside.
- Uniformly random seam location covers each fixed circle parameter with probability h. Couple target randomness and output sampling, and condition on the target query path. A high-probability finite query cap followed by a union bound gives average disagreement at most zeta, so a single fixed seam alternative achieves this bound. This proves the stated total-variation conclusion for usual measurable algorithms. Fixed parameter within each experiment is essential.

## Precision edits recommended

1. Explicitly specify the fundamental interval and seam as above. This avoids any ambiguity about the real-valued periodic map g.
2. Pad the target query sequence after stopping, or use its first min(T,N) points. Include observation randomness in the target random seed for sampled-output protocols.
3. In the analytic-oracle paragraph, replace an unqualified “one random exact equality query” with “the full separating finite word-probability vector at one random parameter” or “a finite batch of all words through length 2p-1 at one random parameter.” An arbitrary selected single word can agree identically under different analytic laws. Some component of the separating finite vector must differ for every fixed globally p-state analytic alternative, and its analytic zero set has measure zero.
4. In the finite-net bound, define e as including both fit discrepancy and a valid simultaneous measurement-error bound. Otherwise write fit + measurement error + omega(h) + omega'(h). The uncomputed existence of kappa is not itself a usable numerical certificate; the report properly asks for a certified lower bound.

## Valid optional strengthenings

- The moving-seam argument also applies to the primitive family with the same fixed A_epsilon and V(g(t)). It preserves strict local positivity, primitivity, atom separation, and finite-Hankel conditioning. The displayed proposition restricts itself to held mixtures, so this is an optional extension rather than a correction.
- For the algebraic rotating-triangle presentation, the positive compact minimum defining kappa is semialgebraically certifiable in principle. Parameterize the atoms using unit-circle coordinates; finite-word probabilities and stochastic constraints are polynomial with algebraic coefficients. Distances from the finitely many exact parameter fibers are finite polynomial inequalities. Enumerating positive rational candidate bounds and using exact real quantifier elimination must eventually certify some positive bound. This supplies theoretical effectiveness, not a practical computed constant.
- The earlier rank-one seam construction in `topology_finite.md` also retains a uniform candidate gap: its convexly blended vector z satisfies ||z||²>=1/2, hence its sole centered singular value is at least beta/2. A spectral-gap promise alone cannot replace a quantitative parameter modulus.

No novelty conclusion is inferred from these audits.

## Recheck of revised source

Inspected the revised source with exact SHA256 `069b02aa54d0763bf5c1298d11078ef36a584bd1011d72b400eb2983a331590b`. The fundamental-interval seam, padded stopping sequence, and analytic separating-vector corrections are present and correct. The focused audit passes this revision. The measurement-error clarification remains a small optional wording improvement; e must be understood as an upper bound on true finite-word discrepancy after accounting for measurement uncertainty.

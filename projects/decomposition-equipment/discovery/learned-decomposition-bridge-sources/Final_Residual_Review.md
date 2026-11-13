# Independent final residual audit

28 October 2026. Reviewed `Residual_Transport_Rigidity.md` and `Source_Clarification_Initialization_and_Residual_Preorder.md` against the locally archived S22 published text/PDF and S26 v2 source theorem extraction. Also checked the path family in `Residual_Fibre_Interface_Candidate.md`, §6.1. No authors' files were edited.

## Verdict

**No fatal mathematical gap found in the reviewed residual strengthening.** The deductions genuinely improve the sources' displayed graphical sufficient criterion while retaining the other relevant population/model/variability/sparsity assumptions. They are additional consequences of the sources' staged conclusions, not statements quoted from those sources and not established novelty claims.

The safe headline is: **distinct residual signatures suffice in the singleton S26 case and in the scalar affine-statistic S22 case; nonparametric multidimensional blocks additionally become independent of their strict representation bases when the corresponding S26 incoming-influence hypothesis supplies full score-difference rank.** This does not make mechanisms temporally autonomous or identify finite-resource implementations.

## 1. Primary-source checks

### Initialization

S26 Assumption 2 explicitly includes the product law at time 1 given `a^0`. Definition 7, equation (6), covers every time and every admissible history; Proposition 8 derives this relation from observational equivalence. Therefore one may use an actually transported full-support product initial law without adding an initialization premise.

S22 §2.1, equations (1)–(2), imposes the same factorization from time 1. Its proof equations (25)–(28) transport the complete trajectory measures, and (30)–(36) include and recover the first prefix. No hidden pre-time-1 conditioning variable appears. Taking coordinatewise sufficient statistics preserves initial independence. The finite-natural-parameter exponential-family tilt preserves null sets of the fixed base measure. Minimality, continuity of the diffeomorphic scalar statistic, and its support therefore ensure genuine scalar nondegeneracy at initialization; no covariance assumption is needed.

### Orientation and support

S26 Proposition 17 says `C_ij` must vanish unless row `G_i` is included in row `G_j`. Thus output i may depend on coordinates with **larger** signatures. Intersecting the masks for action parents, temporal parents, and temporal children gives exactly the stated inclusion preorder. Equal signatures, not arbitrary comparable signatures, are its SCCs. The source graphical singleton-intersection criterion removes all distinct comparabilities and is strictly stronger than singleton SCCs.

S22 Lemma 19 equations (109)–(110) provide the stronger support inclusions before invoking its final graphical criterion. With `P e_i=e_sigma(i)`, `L_i,sigma(i) != 0`, and `M=LP`, the matched diagonal of M is nonzero. Using these diagonals in (109)–(110) gives the claimed parent/child inclusion conditions on every nonzero `M_ik`. This establishes the triangular envelope; graph equality alone would not establish it.

The S22 map convention differs from S26, but the notes use the unambiguous relation `s(Z)=L s(Zhat)+b`. For S26 score arguments, applying transport to the inverse of the aligned learned-to-true map correctly makes the symmetry act on the **true** conditional laws. This orientation is essential and is handled correctly.

## 2. Checked mathematical deductions

1. **Fibre bijectivity:** a diffeomorphism and its inverse respecting the preorder induce mutually inverse maps on every upper-closed coordinate set. Fixing a base then gives a globally invertible fibre, not merely a nonsingular local map.
2. **Product transport:** conditioning on the upper output is equivalent to conditioning on the upper input. Product laws therefore identify each fibre pushforward almost everywhere. Joint continuity plus source-base full support upgrades this to every base. The converse follows by triangular induction.
3. **Scalar rigidity:** a continuous family of scalar diffeomorphisms over a connected Euclidean base has fixed orientation. Relative transports are increasing symmetries of a full-support scalar law. Its strictly increasing CDF forces every relative transport to be identity. Atoms cause no problem. One transported product initialization is enough.
4. **Common symmetry criterion:** relative fibre transports preserve all source block laws simultaneously; conversely any such common symmetry family gives exactly the prescribed product-law transports. This converse is not a free pass to a dynamic model: transformed histories, emissions and masks still need verification, as the notes say.
5. **Ratio rank:** continuous density change-of-variables identities hold everywhere after their almost-everywhere derivation. On common positivity domains their Jacobian terms cancel. Full local likelihood-ratio gradient rank makes the identity point isolated in the relevant level set. A connected evaluation orbit containing it cannot leave it. Density of regular points then proves identity globally. This establishes trivial connected identity component, not triviality of all disconnected symmetries.
6. **Affine rigidity:** conditional laws are translates of a fixed lower-block law. A probability measure has no nonzero real translation period, as follows from its characteristic function near zero. Thus the upper shift is almost surely constant. Independence of the upper blocks and affine nondegeneracy force every strict off-block coefficient to vanish. This argument is valid without finite moments, Gaussian exclusion, or connected support.

## 3. Precise source corollaries approved

### S22

Retain the assumptions of Theorem 4 and Theorem 5 through its sparsity stage: scalar diffeomorphic statistics, sufficient natural-parameter variability, temporal/action variability as applicable, exact matching and the stated graph sparsity bound. **Do not assume the final graphical criterion.** Then after a matched permutation the constant affine statistic map is block diagonal across equal `(Pa^a, Pa^z, Ch^z)` signatures. If all signatures are distinct, recovery is componentwise after permutation even when there are strict inclusions. Fixed mixing within an equal-signature class can remain, including Gaussian orthogonal mixing.

### S26

Retain the applicable theorem's assumptions establishing action, temporal, or combined consistency and its aligned residual preorder. Every singleton SCC has no strict-base dependence, using initialization alone.

For larger SCC B, use the inverse residual map and all true conditional contexts. If B has a common action parent and Assumption 6 or 7 holds, project the appropriate score-derivative or finite score-difference witnesses to B. Their span is all of `R^B`. Under Assumption 6, admissible interior difference quotients and regular-closed boundary approximation place these vectors in the closed span of actual score differences. If B has a common temporal parent and Assumption 8 holds, selecting that column and B's rows of the spanning Hessians gives the same full span. Differentiating nearby past contexts does not have to preserve the selected witness's `z^tau=z` constraint: the common stabilizer already preserves every context.

Projection of the full-measure good-current-state set is dense in block space. Witness log densities must be defined, hence positive locally; the proof needs no global positivity lower bound. The local ratio-rank theorem therefore removes strict-base dependence into these influenced blocks.

The qualification is important: an uninfluenced multidimensional block can retain nonconstant base-dependent rotations. The supplied `(X_1,X_2)~N(0,I_2)`, `U|a~N(a,1)` example satisfies the continuous auxiliary influence assumption and preserves every conditional product law under rotation of X by U. It rules out an unconditional all-block-diagonal S26 claim.

## 4. Growing families

### Path family: approved for S26 temporal consistency

For `n>=3`, symmetric path adjacency with self-loops has `3n-2` directed edges and distinct closed neighborhoods. Endpoint neighborhoods are strictly contained in their neighbors' neighborhoods, so singleton SCCs coexist with failure of the graphical antichain criterion.

Distinct positive auxiliary values applied to the edge powers `a^1,...,a^(3n-2)` give an invertible Vandermonde evaluation matrix. The Gaussian mixed current/past Hessian is exactly A(a), independent of current and past state. Hence the source diagonal-witness restriction is satisfied at any chosen current state. This establishes S26 Assumption 8, not just a generic claim of variability. The nonlinear cyclic readout is globally invertible by contraction and has nonsingular Jacobian for `0<epsilon<1`; its image is all Euclidean space and is closed. At any finite horizon the process is normalized, smooth and full support. Stability is unnecessary for the stated finite-horizon result.

The existing exact-arithmetic checker was run read-only and passed for n=3,...,8. The symbolic Vandermonde and neighborhood arguments establish all n, rather than extrapolating from those tests.

### Dense S22 family: approved

In §9 of the rigidity note, powers `s^(i+1)` give natural-parameter rank n. Differentiating with one past coordinate nonzero yields one isolated Jacobian column with entries `(i+1)s^i`; Vandermonde evaluations span that column, and all columns together span all n-by-n matrices. Action changes similarly span each allowed child set. The initial standard Gaussian product is explicit. Thus this is a source-valid interacting S22 family with nested distinct signatures beyond the antichain criterion. It has quadratic temporal wiring, not bounded local wiring.

### Action-only family: approved with its stated narrower role

The clarification note's T=1 nested-action polynomial family verifies full natural-parameter variability and finite/continuous action influence by triangular and Vandermonde arguments. Temporal variability is vacuous for its empty graph. It is a valid growing separation of graphical criteria, but is not a persistently interacting temporal family; the two notes correctly distinguish these roles.

## 5. Publication/integration cautions

- State each source corollary with the complete applicable model, exact-fit, variability and sparsity premises. “Same assumptions” means retaining these while replacing the final antichain criterion by the weaker signature condition; it does not mean arbitrary learned maps are identifiable.
- Do not apply the scalar Euclidean argument to finite states, circle fibres, or disconnected domains. The XOR and circle examples correctly show why.
- Do not describe rigidity as removing temporal interactions, proving finite-sample learning, or certifying finite-bit ports. The positive raw-port construction belongs to its separately frozen, source-compatible analog model class.
- The score-family refinement is a proved deduction here; a scientific-priority claim remains unchecked against the wider transport/ICA literature.

**Final disposition:** approved for integration as scoped population residual-rigidity deductions. No blocking correction required in the two reviewed notes.

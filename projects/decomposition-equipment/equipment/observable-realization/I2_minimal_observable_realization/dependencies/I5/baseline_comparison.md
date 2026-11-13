# I5: baseline comparison and the remaining mathematical burden

**Research status, 31 October 2026.** This is a target-selection note, not a proof of I5 or a novelty claim. The original obligation asks for simultaneous optimal observational refinement for substitution, admissible cuts and permitted interface transport, including effective unbounded-context certification, structural commutation, necessity bounds, and local-to-global optimality. Existing commutation of free completion with presentation equations is a different statement.

## 1. Fix the order and the kind of completeness

Recommended convention: `P ≤ Q` means that P is finer/more informative than Q. A repair S therefore satisfies S(P) ≤ P. A least-information repair is the **greatest** admissible element below P, not the least element in this order. If an increasing-information order is preferred, reverse every displayed inequality; do not call the same map an extensive closure in the finer-is-smaller convention.

For a concrete lattice C and an upper closure ρ:C→C, separate:

- backward completeness: `ρ f = ρ f ρ`;
- forward completeness: `f ρ = ρ f ρ`.

For typed operations, replace the input/output occurrences of ρ with the relevant sort closures. For multiple arguments, close all input coordinates. Neither equation alone says that a chosen quotient preserves occurrence witnesses, boundary compatibility or reconstruction of decompositions. Those must first be encoded in the concrete operations and observations.

## 2. Primary-source facts already available

### A. Complete abstract-interpretation shells and cores

Giacobazzi–Ranzato–Scozzari, *Making Abstract Interpretations Complete*, JACM 47(2), 2000:

- Theorem 5.3 assumes complete lattices C,D and continuous operations F⊆[Cⁿ→D]. It gives the relative input shell `ρ ∧ R_F(η)` and relative output core `η ∨ L_F(ρ)`.
- Theorem 5.10 gives the absolute shell `gfp(λφ.ρ ∧ R_F(φ))` and core `lfp(λφ.ρ ∨ L_F(φ))` for continuous F⊆[Cⁿ→C]. Here ∧,∨ are in the pointwise-ordered closure lattice, not set intersection/union of represented values.
- Definition 4.6 constructs R_F from Moore closure of maximal inverse images of principal downsets, including coordinate sections; Theorem 4.3 supplies its completeness characterization. Continuity cannot simply be dropped (Example 4.4).
- Lemma 5.13 and its following paragraph already give reduced-product modularity of absolute shells: `S_F(φ₁∧φ₂)=S_F(φ₁)∧S_F(φ₂)`.
- Fixpoint completeness is different: §5.3 gives failures of shell existence; Theorem 5.18 supplies cores for monotone maps.

[Primary author-hosted published PDF, §§4–5, especially pp. 381–391](https://www.sci.unich.it/~scozzari/paper/JACM00.pdf).

### B. Forward shells and generalized Paige–Tarjan

Ranzato–Tapparo, *Generalizing the Paige–Tarjan Algorithm by Abstract Interpretation*, arXiv:cs/0612120v2:

- §2.2.2 distinguishes the two completeness equations above and shows they are orthogonal. §2.3 constructs forward shells by closing represented values under F and meets; operations may have varying finite arities, including constants.
- Theorem 4.4 assumes DCC on the representation lattice A, plus either backward completeness for the higher-order operator F^M or closure of represented models under S_F. It then gives `GPT(a)=α(S_F(γ(a)))`; Corollary 4.5 gives optimal stability.
- Corollary 4.7 permits restricted refiners only when absence of restricted refiners is equivalent to absence of all refiners.
- §4.4 bounds strict partition refinement by carrier size; Corollary 4.8 treats languages with conjunction and negation. Disjunctive domains are not synonymous with partition domains: arbitrary unions need not supply complements.

[Primary full paper, §§2.2–2.3 and Theorem 4.4–Corollary 4.8](https://www.math.unipd.it/~ranzato/papers/ArXiV0612120.pdf).

### C. Coalgebraic and multisorted partition refinement

Wißmann–Dorsch–Milius–Schröder, *Efficient and Modular Coalgebraic Partition Refinement*, LMCS 16(1), 2020:

- Theorem 4.20: a progressing select routine and finitely many coalgebra quotients suffice for termination and the simple quotient.
- Corollary 5.21 adds zippability and respect for compound blocks for the optimized finite algorithm.
- Theorem 7.16 requires a zippable Set-functor and a refinement interface with linear-time initialization/update to obtain `O((m+n) log n)`.
- Remark 4.15 accommodates an initial observation partition by adding it as an output component of the functor. One must not merely start with an arbitrary partition and retain the unchanged behavioural-equivalence claim.
- Section 8 treats modular construction via multisorted coalgebras. Zippability is not closed under arbitrary composition: Example 5.10 uses the double finite-powerset functor.

[Primary published paper, Theorems 4.20 and 7.16, Remark 4.15, §8](https://lmcs.episciences.org/6064/pdf).

**Boundary:** coalgebraic minimization is a serious candidate implementation baseline, not an automatic proof of compatibility with the substitution algebra. A cut structure must be specified as an actual functor/coalgebra, with the intended witness distinctions retained by that functor.

### D. Algebra–coalgebra compatibility is itself an established baseline

Turi–Plotkin, *Towards a Mathematical Operational Semantics*, LICS 1997, §7 assumes a syntax monad T and behaviour comonad D (in the operational presentation, freely/cofreely generated by Σ/B). Theorem 7.1 identifies distributive laws `λ:TD⇒DT` with the respective liftings. A bialgebra satisfies `k h = D(h) λ_X T(k)`. Under preservation of weak pullbacks by B, Corollary 7.4 gives full abstraction for B-bisimulation and Corollary 7.5 gives a final bicongruence. These statements are not unconditional claims that every behavioural quotient is a substitution congruence. [Primary author-hosted paper, §7](https://homepages.inf.ed.ac.uk/gdp/publications/Math_Op_Sem.pdf).

**I5 application gate:** construct the intended typed syntax/behaviour objects and the mixed law, prove that admissibility and decorated witnesses survive it, and check all hypotheses. Calling the cut operation a coalgebra does not supply that law. A law sufficient for congruence also need not prove commutation of the *least repair operators* from an arbitrary starting observation.

## 3. What is standard, and what still needs an I5-specific argument?

| Requested output | Baseline contribution | Remaining obligation in this target |
|---|---|---|
| Simultaneous optimum | Once all three operation families are correctly encoded and the relevant hypotheses hold, apply a shell to their union. | Prove that this encoded completeness is equivalent to the intended typed witnessed-decomposition judgments; justify the chosen representation class. |
| Effective extra information | Complete-domain construction or splitter refinement identifies additional predicates/blocks. | Interpret these as occurrence, retained-boundary, matching or decoration information and show a changed cut/substitution/transport judgment. |
| Repair commutation | Abstract fixed-point/closure algebra supplies generic criteria. | Derive a checkable criterion from actual mixed witness operations; a rephrasing as `S_i S_j=S_j S_i` does not satisfy the minimum floor. |
| Unbounded family | Generic noncommuting closures are easy to construct. | Realize order dependence or repeated propagation inside the declared decomposition calculus, with growing parameter and no accidental collapse of profiles. |
| Stabilization | Finite-height arguments bound strict refinement steps. | Account for finding a splitter, all generated operations, and an actual necessity/lower-bound family. A round bound is not automatically a running-time bound. |
| Local-to-global optimum | Reduced-product shell modularity already exists. | Show that actual I1 restrictions/gluing identify the desired global domain, preserve admissibility and witnesses, and reflect global refiners. Local agreement is not itself global optimality. |

These residuals are research obligations identified by comparison, not assertions that they are absent from all literature.

## 4. Finite instances versus unbounded contexts

A finite collection of represented states does not provide an algorithm for an unspecified infinite operation signature. In particular, unbounded arities, profiles and generated contexts can remain outside an enumerated test set.

An acceptable effectiveness certificate should supply one of:

1. a finite complete operation basis and an induction reducing every well-typed generated substitution, cut and transport to it;
2. an effective schema plus a terminating decision procedure for whether **any** schema instance is a splitter;
3. a proved finite quotient of operation behaviours, together with a computable enumeration and completeness proof.

For a typed finite family with n_s states and b_s initial blocks in sort s, at most `Σ_s(n_s−b_s)` strict block-increasing steps are possible. This elementary counting observation does **not** certify that the stopping test covers all contexts, that there are finitely many relevant sorts, or that an unbounded syntax stays inside the finite carrier. Those are separate hypotheses to prove.

Likewise, monotone maps on genuinely finite lattices have the continuity needed for the backward-shell theorem. This does not establish that a restricted class of presentations is closed under the required shell, or that finite calculations are complete for a larger infinite semantics.

## 5. Recommended first theorem gate

Before claiming simultaneous completion, freeze:

- the full-profile sorts and concrete carrier in each sort;
- the observation partition and admissibility of partial operations;
- precise substitution, cut and transport operations, including witness outputs;
- whether the target is algebra congruence, coalgebra behavioural equivalence, forward predicate completeness, backward completeness, or a proved combination;
- the represented-domain lattice and the order;
- a basis/schema theorem and a refiner-completeness test;
- the exact comparison between local gluing and the global optimum.

Then import the strongest applicable baseline explicitly. If the entire result reduces to an ordinary typed algebra/coalgebra with standard refinement, that is a useful implementation theorem, but not yet the decomposition-specific commutation/necessity package required by I5.

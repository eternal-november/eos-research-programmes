# I2: minimal observable realization — baseline comparison

**Scope and status (31 October 2026).** This note compares the original I2 obligation with established results. It is not a novelty claim and does not itself discharge I2. The original contract requires full-profile sorts, specified graft/cut/interface probes, a realizability criterion, effective construction, minimality/uniqueness, independently checked decoding, and quantitative necessity. It explicitly excludes passing by ordinary tree-automaton minimization alone. The completed I5 repair theorem is an input, not a second I2 deliverable: computing the stable equivalence does not by itself construct a witness calculus or prove its decoder exact.

## 1. Primary literature and exact import boundaries

### 1.1 Tree Myhill–Nerode and deterministic bottom-up minimization

Comon et al., *Tree Automata Techniques and Applications*, October 2007, §1.5, pp. 33–35, proves equivalence of recognizable tree language, saturation by a finite-index congruence, and finite index of the all-context syntactic congruence. Its quotient transition is `[f(t₁,…,tₙ)]`; Corollary 1.5.1 identifies the minimum deterministic bottom-up automaton uniquely up to state renaming. Algorithm MIN takes a **complete and reduced** DFTA; reduced means every state is accessible. The setting is finite ordered ranked trees over the ranked alphabet of Chapter 1. This is not a minimality theorem for arbitrary nondeterministic, stochastic, or top-down realizations. [Full primary text, §1.5, institutional repository copy](https://citeseerx.ist.psu.edu/document?doi=6a94bc1c6e4e89aacc2ac9c15d0388300bc91961&repid=rep1&type=pdf).

**I2 boundary:** deterministic algebra operations and an observable decoder are covered in spirit by this baseline. Relational cut witnesses, their joint correlations, and occurrence-sensitive graft interaction still need their own representation and proof. A quotient of syntax states alone does not decode concrete decompositions.

### 1.2 Many-sorted recognizability, including infinitely many sorts

Iosif–Zuleger, *Characterizations of Monadic Second Order Definable Context-Free Sets of Graphs*, LMCS 22(1:22), 2026, §2.3, Definitions 2.4–2.6, explicitly uses sort-preserving congruences with finitely many classes **per sort**. Recognition is equivalently inverse image under a homomorphism into a locally finite algebra. The syntactic congruence is the coarsest saturating congruence; the authors refer to Courcelle–Engelfriet, Propositions 3.64 and 3.66. Their Theorem 7.4 applies to **source-free graph languages in their HR algebra**: recognition there iff recognition in every finite-source subalgebra. Lemma 7.3 proves the requisite equality of restricted syntactic congruences. Lemma 7.1 reduces contexts to parallel composition, restriction and renaming. These are structural results for that algebra, not generic facts about arbitrary profile systems. [Primary published paper, §§2.3 and 7](https://lmcs.episciences.org/17687/pdf).

**I2 boundary:** full-profile sorts cannot be silently replaced by finitely many control labels. A context-normal-form theorem in the selected decomposition calculus would be analogous to the cited structural reduction, and must be proved rather than borrowed without an interpretation.

### 1.3 Modal equivalence and image-finite bisimulation

Hennessy–Milner, *Algebraic Laws for Nondeterminism and Concurrency*, JACM 32(1), 1985, Theorems 2.1–2.2, assumes each experiment relation has finite image at every state. It identifies the finite-depth limit with the greatest bisimulation fixed point and characterizes equivalence by their modal language. The index set of experiments need not be finite. Section 3, p.143, then closes observational equivalence under every algebraic context, obtaining the largest congruence contained in it. Section 3.2 already gives strict modal-depth hierarchies. [Primary author-hosted paper, pp.139–143 and Appendix A](https://www.scss.tcd.ie/matthew.hennessy/pubs/old/HMjacm85.pdf).

**I2 boundary:** modal equivalence, contextual closure, and depth hierarchy are strong prior baselines. Image finiteness is branching finiteness, not finite quotient index, finite syntax, or an effective finite operation presentation. Ordinary unary transition modalities do not automatically express a cut's correlated tuple of components and witness.

### 1.4 Coalgebraic quotient computation

Wißmann–Dorsch–Milius–Schröder, *Efficient and Modular Coalgebraic Partition Refinement*, LMCS 16(1:8), 2020, Theorem 4.20 gives the simple quotient for a progressing select routine when the coalgebra has finitely many quotients, within §4's categorical hypotheses. Corollary 5.21 adds a zippable Set-endofunctor and selection respecting compound blocks for the optimized finite algorithm. Theorem 7.16 requires a suitable linear-time refinement interface for its complexity result. Section 8 provides multisorted modular constructions. Remark 4.15 incorporates observations as an output component. [Primary published paper](https://lmcs.episciences.org/6064/pdf).

**I2 boundary:** exact coalgebra type matters. A finite-powerset of products retains correlated cut alternatives; a product of finite-powersets generally does not. A behavioural simple quotient is not, without another theorem, a multicategory/witness-calculus quotient compatible with grafting.

### 1.5 Mixed algebra–coalgebra compatibility

Turi–Plotkin, *Towards a Mathematical Operational Semantics*, LICS 1997, §7, Theorem 7.1 relates distributive laws of a syntax monad over a behaviour comonad to liftings. A bialgebra satisfies the mixed compatibility equation. Corollaries 7.4–7.5 assume the behaviour functor preserves weak pullbacks to give bisimulation full abstraction and a final bicongruence. The paper includes possibly multisorted syntax without variable binding. [Primary author-hosted paper, §7](https://homepages.inf.ed.ac.uk/gdp/publications/Math_Op_Sem.pdf).

**I2 boundary:** the mixed-operation idea itself is established. The decomposition-specific contribution must establish an actual typed compatibility law (or a direct substitute), retaining admissibility, interfaces, occurrences and witnesses. Merely naming cuts a coalgebra and grafts an algebra supplies none of those facts.

## 2. Required logical distinctions for the realization theorem

The following are audit criteria and elementary deductions for I2, not claims of new general theory.

### Finite index has three meanings

Write `Q_s = X_s / ≡_s`, where `s` is the **full profile**.

1. **Per-profile finite:** every `|Q_s|` is finite. This allows arbitrarily large finite indices across profiles.
2. **Uniform finite control bound:** some finite `K` bounds every `|Q_s|`. This still does not make the disjoint typed carrier finite when infinitely many profiles are inhabited. Shared labels must remain paired with their profile.
3. **Finite total typed carrier:** `Σ_s |Q_s| < ∞`. This requires only finitely many inhabited profiles.

Neither (1) nor (2) supplies a computable schema for operations. A finite carrier and infinitely many declared operations still need a finite basis, or a terminating complete schema-splitter test. No generic algorithm can inspect an arbitrary unspecified infinite signature.

### Exact quotient cuts need joint tuple lifting

For a declared cut label/profile `κ`, suppose the concrete cut relation is

`D_κ(x) ⊆ W_κ × X_s₁ × ⋯ × X_sᵣ`.

Let `q_W` and `q_s` be the witness and object quotient maps. Exact representative-independent decoding requires

`D̄_κ(q(x)) = { (q_W(w),q_s₁(x₁),…,q_sᵣ(xᵣ)) : (w,x₁,…,xᵣ) ∈ D_κ(x) }`

**for every representative x**, not merely the union over representatives. Thus equal source classes must have equal sets of complete quotient tuples. This equation is the two-direction lifting requirement: every concrete cut maps to an abstract cut, and every abstract tuple can be lifted at each chosen equivalent source. It does **not** require an arbitrary chosen tuple of concrete child representatives to be jointly realizable; that stronger requirement needs a separate theorem.

Marginal projections are insufficient: `{(a,a),(b,b)}` and `{(a,b),(b,a)}` have identical coordinate projections but different joint alternatives whenever `a,b` remain distinguishable. Losing the witness coordinate can similarly lose compatibility or occurrence evidence. Tests against products of definable child blocks can distinguish these sets when the relevant blocks are definable and branching hypotheses justify the modal argument; this adequacy must be proved for the fixed probe grammar.

### Decoder scope must be declared

- An **observation decoder** returns the requested observable value and establishes `obs = decode ∘ q`.
- A **cut decoder** returns precisely the abstract cut tuples above, with soundness and lifting established independently of construction.
- A **concrete witness reconstruction decoder** recovers concrete representatives or certificates. This is stronger: class identifiers and finite observations need not determine a unique concrete witness.

A claim of a minimal witness calculus needs identities, typed composition, equations and witness/cut structure to descend. If only labels and transitions descend, the correct output name is an observational transition system. A cut system is intermediate and its precise operations must be stated.

### Minimality is relative to a representation class

Specify the competitors: sort-preserving surjective realizations of the same concrete family, preserving the fixed observations, grafts, transports and exact cut behaviour. For a candidate map `h`, the standard argument is `ker h ⊆ ≡`, followed by the canonical surjection `h(X_s) → Q_s`, `[h(x)] ↦ [x]`. Prove its well-definedness and all structure preservation, especially cuts. This gives a per-sort lower bound. Uniqueness up to typed isomorphism requires observable separation/minimality in that declared category, not an unrestricted claim about every machine with the same outputs. If unreachable states are admitted, remove them or weaken the statement. No arbitrary stochastic-minimizer uniqueness follows.

## 3. What must be added beyond I5 and these baselines?

| I2 output | Already standard or supplied by I5 | Target-specific evidence still required |
|---|---|---|
| Stable contextual equivalence | Syntactic congruence, modal equivalence, stable repair | Fixed probes adequate for correlated cuts; occurrence-aware semantics |
| Realizability criterion | Finite syntactic index / simple quotient patterns | Exact typed quotient structures and the distinction between local index, uniform control, and total finiteness |
| Minimality and uniqueness | Factorization through observable quotient | Declared competitor category; cut-preserving factorization; full profiles retained |
| Effective construction | Finite refinement mechanics | Complete context/cut basis or effective schemata; unbounded empty/unary syntax covered |
| Mixed operation compatibility | Bialgebra frameworks; I5 stability machinery | Concrete cut-after-graft law, including crossing/internal cuts and witness transport, wherever admitted |
| Decoder | Output factoring is standard | Independently checked soundness and joint lifting, not checking an encoder against its own copied tables |
| Quantitative theorem | Finite partition-height bound | Genuine selected C5 parameter family, strict state/index growth or stabilization necessity, and actual distinguishing cuts after grafts |

For a finite sorted represented input with `n_s` states and `b_s` initial blocks, `Σ_s(n_s−b_s)` bounds strict block-increasing steps. This count alone is not running time, an infinite-schema stopping test, a structural lower bound, or a theorem that the quotient is a witness calculus.

**Bottom line.** A satisfactory restricted I2 theorem can honestly import standard typed syntactic/behavioural minimization and I5's repaired equivalence. Its additional work is the realization: descend the actual compositional and correlated cut structure, establish representative-independent decoding, prove the concrete mixed laws and finite-schema coverage, and exhibit a parameterized necessity family. None of the comparisons here asserts that these remaining specialized statements are absent from the literature.

# I1: baseline comparison and exact transfer boundary

31 October 2026. Technical research note for the authorized I1 investigation. This is not a novelty claim or a discharge certificate.

## Contract and existing bridge

Original I1 is the unchanged obligation at lines 622–637 of `Original_Completion_Contract_v0.1_VERBATIM.md`. It requires nontrivial shared interfaces, a pushout/comparison construction, conservativity, complete mixed refinement coherence, additional cut/restriction conditions, and a converse or unbounded obstruction family. Its floor explicitly excludes bare pushout existence, disjoint signatures, or a single finite enumeration.

The existing source `dependencies/modular_repair_theorem.md`, especially §§2–6 and 9, proves a relative **comparison** theorem for coefficient products over a retained graph spine. Its actual certificate doctrine retains the graph refinement forest and coefficient products at every active occurrence. Its cut theorem uses whole shared records and fixed-source lifting. It explicitly does not establish unrestricted I1. These boundaries should survive verbatim into the new theorem.

## 1. Primary-source baseline facts (precise scope)

**Coherent rewriting.** Guiraud–Malbos, *Polygraphs of finite derivation type*, §3.1, Lemma 3.1.5 and Theorem 3.1.6: critical confluence characterizes local confluence for 2-polygraphs; termination turns local confluence into confluence. Theorem 4.3.2 says a chosen family of generating confluences of a convergent 2-polygraph is a homotopy basis of its free `(2,1)`-category. The extension adds a 3-cell for each critical branching. This concerns parallel 2-cells modulo the generated 3-dimensional equivalence after 2-cells are inverted, not literal equality of directed rewrite paths in the unextended free 2-category. Finiteness of the presentation yields finite critical data in this string/path setting. Applying it to unrestricted multicategory/tree rewriting needs a separate encoding or appropriate critical-pair theorem. [Primary text, §§3.1 and 4.3](https://arxiv.org/pdf/1402.2587).

**Matched pairs.** Rida-e Zenab, *Algebraic properties of Zappa–Szép products of semigroups and monoids*, §1, Definition 1.1 and the following monoid paragraphs, gives four compatibility axioms and four unit axioms for the product on `S×T`; the same section identifies its embedded factors and the internal unique-factorization interpretation. With one action trivial this specializes to a semidirect product. Consequently the coefficient-level construction below is standard matched-pair algebra, not by itself the extra I1 result. [Primary published text, §1](https://link.springer.com/article/10.1007/s00233-017-9878-1).

**Structured cospans.** Baez–Courser, *Structured Cospans*, Theorem 2.3 needs a functor `L:A→X` and chosen pushouts in `X`; it supplies a double category with structured cospans as horizontal arrows and commutative diagrams as squares. Theorem 3.9 assumes finite colimits in `A,X` and preservation by `L` to obtain symmetric monoidal structure. A left adjoint is sufficient for that preservation, not necessary. These are composition/coherence results, not assertions that arbitrary apex maps, presentation embeddings, or witness fibres are injective. [Primary text, Theorems 2.3 and 3.9](https://arxiv.org/pdf/1911.04630).

**Decorated cospans.** Fong, *Decorated Cospans*, Theorem 3.4 assumes finite colimits in `C`, a braided monoidal `D`, and a lax braided monoidal `F:(C,+)→(D,⊗)`; it constructs a symmetric monoidal hypergraph category of decorated cospans and the wide undecorated embedding. The decoration composition uses the laxator and pushout maps. It does not assert that a selected factorization/cut fibre is a pullback or that observation-matching witnesses glue. [Primary text, Theorem 3.4](https://arxiv.org/pdf/1502.00872).

## 2. Explicit coefficient calculation: what the candidate must check

The following is a direct calculation for the proposed presentation, included to make its hypotheses auditable rather than importing an unnamed distributive law.

Let `A,B` be finite monoids and let

`r:B×A→A×B`, `r(b,a)=(λ(b,a),ρ(b,a))`.

Present the separate multiplication tables, remove unit letters, and orient mixed rules

`B_b A_a → A_{λ(b,a)} B_{ρ(b,a)}`,

with unit outputs omitted. Required equations are:

* units: `r(1,a)=(a,1)` and `r(b,1)=(1,b)`;
* BAA: if `r(b,a)=(x,c)` and `r(c,a')=(y,d)`, then `r(b,aa')=(xy,d)`;
* BBA: if `r(b',a)=(x,c)` and `r(b,x)=(y,d)`, then `r(bb',a)=(y,dc)`.

These are finite table tests, but their role is all-word: multiplication triples AAA and BBB use associativity; BAA and BBA are precisely the genuinely overlapping mixed triples. Unit overlaps use the two unit equations; independent redexes commute. Length followed lexicographically by the count of B-before-A inversions strictly decreases. A mixed step either shortens the word or exchanges one adjacent BA pair for AB. Same-channel multiplication shortens it. Thus termination is proved independently of confluence.

The irreducibles are empty, `A_a`, `B_b`, or `A_aB_b` with nonunit letters. Every pair `(a,b)` has exactly one such representative. Their induced product is

`(a,b)(c,d)=(a λ(b,c), ρ(b,c)d)`.

Joining every listed critical triple proves confluence and associativity on all words, not merely the checked length-three words. Conversely, within this fixed table-rule class, unique AB normal forms force the unit, BAA and BBA equalities by comparing the two reductions. If a mixed equality fails, distinct AB normal forms become equal in the quotient presentation. That is failure of this normal-form/coherence criterion; it does not automatically mean an equation inside A or inside B collapses.

The embeddings `a↦(a,1)` and `b↦(1,b)` are injective monoid homomorphisms. **The coordinate projections need not be homomorphisms.** In a nontrivial semidirect product the private A projection generally fails multiplicativity. Therefore I5's projection-based cut/repair proof cannot be copied unchanged.

Bijectivity of `r` is not needed for the terminating normal-form construction. If the intended interpretation requires invertible swaps as maps of coefficient pairs, require it separately. Inverting rewrite 2-cells in the track-category sense is a different operation from requiring this set map to be bijective.

For finite groups and a homomorphism `φ:B→Aut(A)`, `r(b,a)=(φ_b(a),b)` satisfies the tests and is bijective. This is a convenient all-parameter positive subclass. It is still ordinary semidirect-product algebra until the retained graph-witness theorem is proved.

## 3. Pushout versus comparison: independent elementary check

Fix a nontrivial presented common theory `S` and actual inclusions into presentations `P_A,P_B`. Their presentation pushout identifies the common generators/relations and otherwise takes the union. Its universal property concerns maps agreeing on `S`.

Adding prescribed mixed equations gives a further quotient `Q` of that pushout. Its universal property concerns agreeing pairs of maps that also satisfy those equations. Do not call `Q` the unconstrained pushout. Unique coefficient normal forms can prove both inclusions into `Q` are conservative even though `Q` is a proper quotient of the pushout.

For a genuinely shared scalar palette `K`, the easy positive extension uses local coefficients `A×K`, `K×B` and global coefficients `(A⋈B)×K`, with one identified K alphabet and K commuting with both private alphabets. It does not require K itself to be commutative. This provides a nontrivial coefficient intersection as well as the common graph theory. More general shared coefficients require fresh compatibility conditions; disjoint-factor matched-pair axioms do not solve arbitrary amalgamation over K.

## 4. The graph-distribution and refinement bridge still required

Fix actual C5 graph operations and retained occurrence-indexed refinement forests, not merely a profile name. At every nonempty object add coefficient unary arrows. For an old graph generator g, require the diagonal distribution equation: an outer coefficient moves to the *same* coefficient on every active input occurrence. Empty occurrences carry none.

For a fixed finite forest, push coefficients down to leaves, preserving path order, then use the table normal form on each leaf. Copying a pair `(a,b)` before sorting versus sorting before copying must yield the same pair at each descendant. A shared outer factor is not replaced by independent child choices. Multiplication/distribution is checked because each child receives the same ordered product. The old graph relations must preserve the relevant occurrence maps and must commute with this decoration operation.

This proves forestwise coefficient normal forms only after the stated occurrence/distribution checks. To claim a convergent presentation for the entire graph syntax, supply a combined well-founded order including old graph reductions and show an exhaustive list of graph/graph, graph/distribution, distribution/distribution, distribution/multiplication, and distribution/twist overlaps. Otherwise state a **relative theorem over the established common spine**, as I5 §9 does. Arbitrary arity and empty slots may demand effective rule schemata rather than a literally finite global presentation.

For Squier-style transfer, interpret generators and selected confluence 3-cells in the certificate target and require that every mixed confluence boundary has the specified filler. The homotopy-basis theorem then reduces all track-category coherence to those generators. If certificate arrows are directed/noninvertible, this conclusion does not apply without additional proof. For the I5 retained-certificate doctrine, a direct forest-product proof may be both stronger operationally and safer than an unsupported full Squier import.

## 5. Cuts, restrictions, and interfaces are additional structure

For an actual cut c and source z, the coefficient fibre consists of a **single tuple** `(u_i,v_ij)` satisfying `u_i v_ij=z_ij`; one `u_i` serves all its children. An iterated cut retains the whole factor tree.

Conservative operation embeddings do not imply fullness on these fibres. Even `A→A×B` has extra global cuts of `(a,1)` whenever B contains nontrivial factors of its identity. In particular any nontrivial finite group has `b b^{-1}=1`, so a group-based positive normal-form theorem cannot claim full reflection of embedded local cuts. For finite monoids, absence of nontrivial units is sufficient to prevent this omitted-channel phenomenon in direct products. Twisted products need a separate submonoid factor-closure condition: every permitted factor tuple of an embedded source must lie in the embedded subtheory. This is necessary and sufficient for fibre fullness at the specified cut shapes.

The I5 local-to-global proof needs more than normal forms: a source-preserving bijection of whole global witness fibres with the fibre product of local fibres over the exact shared record, plus lifting of every local witness at each fixed global source. Direct products have this by pairing labels and using units in the omitted channel. Arbitrary twists need not; lack of monoid projections already blocks that argument.

An interface restriction must preserve the actual graph/cut record and occurrence maps and act on coefficients by compatible homomorphisms. For maps `f:A→A'`, `g:B→B'`, the explicit condition is

`(f×g) r = r' (g×f)`.

Then the induced pair map preserves mixed multiplication. If restrictions identify or discard occurrences, specify how the shared-factor tuple is transported and prove its cut-square property; coefficient equivariance alone is insufficient. Inverse or groupoid transport requires the relevant maps to be isomorphisms, separately from mere restriction.

## 6. Recommended claim boundary

Already supplied by the baseline: coefficient normal forms and associativity under matched-pair tests; embedded factors; chosen-critical-confluence track coherence; and cospan composition with its categorical coherence under stated colimit/lax-monoidal hypotheses.

The extra I1 work is an all-parameter theorem for **the actual path-typed graph witness presentation**: conservativity across its nontrivial interface, mixed certificate interpretation, exact cut-fibre and restriction conditions, and a converse/obstruction family with independently verified input embeddings and local convergence. In particular, normal forms alone neither manufacture the cut pullback nor let independently matching shared factors glue. The surviving I5 counterexample in §8 already illustrates that mismatch, but is not the original I1 failure of interface identification creating a new equation.

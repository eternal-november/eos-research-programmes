# A typed dictionary and relationship ledger

This is a reading aid for the existing theory, not a proposal for another generalization. It normalizes notation across the archived sources and separates three sorts of connection: an established theorem, a source's stronger stated/conjectured claim, and a translation not yet checked in our work. “Inspected” below means the cited argument was read in the earlier audit, not formally verified. Sources and local evidence are listed at the end.

## 1. Start with the arrow, not the name

Fix an ordinary category C. Composition of ordinary arrows is right-to-left.

| Structure | Arrow from A to B is represented by | Ordinary arrow u:A→B maps to |
|---|---|---|
| Monad T, Kleisli | f:A→TB | η_B u |
| Comonad G, coKleisli | f:GA→B | u ε_A |
| Contextad | P∈K_A and f:e_A P→B | unit context, then ε, then u |
| Contentad | Q∈L_B and f:A→d_B Q | u, then unit content η |
| Candidate mixed form | P∈K_A, Q∈L_B, f:e_A P→d_B Q | both unit grades |

The last row specifies objects of a potential hom-category. It does not yet specify a composition. Even the pure functor needs the one-sided unit structures and compatible comparisons before one has a mixed category.

The ordinary Kleisli composite is μ_C T(g)f. The ordinary coKleisli composite is g G(f)δ_A. In both cases the action on the second arrow follows from already supplied structure. The dependent analogues have extra indexing: a subsequent requirement must be transported to the actual object where the next computation runs.

### Contextad: dependency on the input

Write K:C^op→Cat for the indexed category of contexts and e for the extension functor on its total category. For P∈K_A, write e_A P=A⊙P. An arrow u:A→B gives u*:K_B→K_A and an extension map e_A(u*P)→e_B P.

There are unit contexts I_A, maps ε_A:e_A I_A→A, and combinations

    P⊗R ∈ K_A,    where P∈K_A and R∈K_(e_A P),
    δ_(P,R):e_A(P⊗R) → e_(e_A P)R.

For (P,f):A⇒B and (Q,g):B⇒C, the composite grade is P⊗f*Q. Its body applies δ, the extension map of the cartesian lift over f, and then g. Pullback is along f:e_A P→B, not along a hypothetical underlying map A→B. This is dependent context accumulation rather than a fixed product of two resources.

### Contentad: dependency on the output

Write L:C→Cat and d for the total extension functor. Covariant transport along u is u!:L_A→L_B, with extension map d_A Q→d_B(u!Q). There are J_A and η_A:A→d_A J_A.

To avoid a tensor-order ambiguity in the contextad paper's contentad prose, define an explicitly ordered operation:

    Q◇S ∈ L_A,    where Q∈L_A and S∈L_(d_A Q),
    μ_(Q,S):d_(d_A Q)S → d_A(Q◇S).

Then (Q,f):A⇒B, f:A→d_B Q, followed by (S,g):B⇒C has grade S◇g!Q. Indeed g!Q belongs to L_(d_C S), exactly the second input expected by this operation. The body is f, then the extension map over g, then μ. The symbol ◇ is ours; it normalizes the source rather than claiming another operation.

### Mixed dependency: the crossing changes the base

Take f:e_A P→d_B Q followed by g:e_B R→d_C S. One cannot write f*R: R is over B while f lands in d_B Q. A crossing for the central pair (Q,R) must instead supply

    Rhat ∈ K_(d_B Q),    Qhat ∈ L_(e_B R),
    χ:e_(d_B Q)Rhat → d_(e_B R)Qhat.

The candidate composite grades are P⊗f*Rhat and S◇g!Qhat. The body passes through context accumulation, transport over f, χ, transport over g, and content accumulation. Typing this chain is the first test; naturality, independence of presentations, units, accumulation laws and higher coherence are further tests. Conversely, once an appropriate law in a suitable ambient category is available, established composition machinery handles these tests together.

### Two small positive translations

On Set, let M be a monoid. A writer Kleisli arrow A→M×B is exactly a pair of functions m:A→M and f:A→B. In its transposed context presentation the grade is the input-dependent function m, and extending by that grade leaves the carrier A unchanged. The composite grade is a↦m(a)n(f(a)); the body is g∘f. This is an identity-on-objects **ordinary category isomorphism** for this concrete construction, not an invocation of the unproved general PRA claim. The same computation can therefore be described as output annotation or input-indexed grade bookkeeping.

For a set R, a reader Kleisli arrow A→B^R is naturally the same as A×R→B. The reader monad multiplication evaluates both environment arguments at the same r; the product comonad uses (a,r)↦((a,r),r). Currying consequently gives an identity-on-objects **ordinary category isomorphism** between the reader Kleisli and product-comonad coKleisli categories. This uses cartesian closedness and the indicated monad/comonad structures, not just a resemblance between arrow shapes. Neither example proves an equivalence preserving arbitrary noninvertible presentation cells.

## 2. Cells: neither side is silently reversed

At fixed endpoints a mixed cell from (P,Q,f) to (P′,Q′,f′) is a pair

    α:P→P′,    β:Q→Q′,    with d_B(β) f = f′ e_A(α).

Both grade maps point forward. They form a commuting square. Calling the input side “contravariant” refers to transport between base fibres, not reversal of every within-fibre cell. This convention matches the native contextad and contentad cells.

With changing endpoints u:A→A′ and v:B→B′, the corresponding grade maps are α:P→u*P′ and β:v!Q→Q′. Insert the extension map over u on the input side and over v on the output side in the same commuting square. This distinguishes base variance from cell orientation.

## 3. Fixed effects and higher effects

For a comonad G and monad T on C, arrows GA→TB compose using a mixed law λ:GT⇒TG:

    g⋆f = μ_C · T(g) · λ_B · G(f) · δ_A,
    id_A = η_A · ε_A.

Compatibility is with both monad laws and both comonad laws. A family of maps GT→TG with no such compatibility is not enough.

Street's **mixed opwreath** is more general: G need not separately be a comonad. For a monad T, it supplies ζ:GT⇒TG, d:G⇒TGG and e:G⇒T, with seven axioms. Duplication and discharge can themselves produce T-effects. Its convolution has arrows GA→TB, identity e_A, and body

    GA → TGGA → TGTB → TTGB → TTTC → TC.

This is the KL orientation. Street's **mixed wreath**, a comonad in EM(K), instead uses TG⇒GT. Switching the label without switching the direction changes the mathematical input.

Garner already supplies a bicategorical two-sided Kleisli construction: for a pseudocomonad G, pseudomonad T and suitable mixed pseudo-law on a bicategory B, its hom-category is B(GA,TB). Thus retaining nontrivial hom-categories does not by itself require a new generic mixed-composition theorem. Contextads, however, are organized through higher displayed-span machinery; an arbitrary contextad/contentad pair is not automatically the input to Garner's theorem. Specifying the common ambient and its dualities is a translation task, not merely renaming K and L as G and T.

Walker and Gambino–Lobbia explain how laws, compatible liftings and extension presentations express the same structure at higher levels. They are valuable dictionaries: a lifting may be easier to construct in a particular example. Their equivalences do not make an arbitrary lifting exist.

## 4. Three comparison levels that should not be conflated

**Local, cell-retaining calculation.** For small categories and functors e:K→C, d:L→C, the project established an ordinary strict Cat-coend isomorphism

    ∫^Z (e↓Z) × (Z↓d) ≅ (e↓d).

It sends composable legs to their composite. The inverse splits at eP, and the proof handles morphisms, including noninvertible grade maps. Applied to e_A and d_B, this identifies the category of mixed triples with a balanced local presentation. It does not construct horizontal composition.

**Ordinary promonad comparison.** Given the already constructed one-sided horizontal bicategories, take isomorphism classes of objects in each hom-category. This produces ordinary categories with identity-on-objects pure functors from C, hence promonads in Prof. With left-to-right tensor notation, context-then-content is M⋄N. A law N⋄M→M⋄N supplies its composite promonad. Here a crossing is an isomorphism class of mixed presentations, not a canonical choice of grades. Noninvertible hom-cells have been discarded. Promonad generality here concerns ordinary arrow semantics; it does not say that the original indexed grades, display fibrations or presentation cells have been retained.

**Full weak, retained-cell comparison.** Combining the previous two observations into an equivalence for all dependent actions and pseudo-coend coherences has not been proved in this work. This is an unchecked bridge in our presentation, not a claim that the literature has no such theorem.

The finite failed crossing is useful as a typing lesson: it already failed independence under moving an intermediate pure map across the balanced tensor. Associativity was not the first issue. The positive List/probability-family example instead supplies and checks an actual crossing, with noninvertible context cells retained; its content fibres are terminal, so it is not an example with arbitrary nonthin structure on both sides.

## 5. Six recurring distinctions

1. **Noninvertible component versus lax coherence.** Ordinary distributive laws need not be invertible. Contextad ε and δ also need not be invertible. A pseudo-law can have a noninvertible transformation but invertible coherence modifications. Replacing those structural isomorphisms by one-way cells is a different weakening; skew theorems have their own axioms and exactness hypotheses.
2. **Pure versus deterministic.** “Pure” names the image of the chosen base functor; faithfulness is an additional property. “Deterministic” may name a copying-preserving subcategory of a Markov category. These are not definitions of the same class. A deterministic physical state transition may still be effectful. Copying a realized sample is not independently rerunning its sampler.
3. **Isomorphism classes versus connected components.** The ordinary Prof bridge uses the former: a noninvertible grade map must not identify presentations there. The probability-history comparison's connected-component quotient forgets more. State the quotient before asserting an equivalence.
4. **Local reflection versus global pseudofunctor.** The finite probability construction has local E⊣J with EJ=id. The canonical sampler section J has a generally noninvertible comparison that forgets an intermediate sample. Local fully faithfulness does not turn this into global pseudo-equivalence.
5. **Categorical product versus probability tensor.** Independent-product measures use a cartesian product of underlying sets. In the category of probability spaces and measure-preserving maps this is a monoidal tensor, not generally a categorical product: marginal maps do not force independence.
6. **Representation comparison versus universal completion.** A local isomorphism of 2-categories, an equivalence restricted to representables, a bicategorical construction, and an adjoint triequivalence of completions are different claims. None can be promoted to the next level just because object formulas agree.

## 6. Compact relationship ledger

Status key: **B** = established baseline with proof in source (inspection qualifications stated); **S** = source statement with proof omitted; **C** = explicit source conjecture; **P** = project result with proof/checks in local notes; **U** = unchecked bridge in our work. No row is a historical novelty claim.

| Key | Connection and exact level | Essential hypotheses / boundary | Status and locator |
|---|---|---|---|
| CM1 | Contextad → contextful pseudocategory; cells and dependent composition | Display fibration, extension, unit/combination, invertible grade coherences; ε,δ may be noninvertible | B: Capucci–Myers Defs 3.15, 3.17, 3.26, pp19–30 |
| CM2 | Comprehension → contextad | Unit, strong dependent sums, Beck–Chevalley, closure of displays | B: CM Ex3.20; display spans Ex3.21 |
| CM3 | Structured contextad → structured pseudocategory | Def5.13's compatible 2-monad structure; not arbitrary enrichment | B: CM Thm5.16 |
| CM4 | Explicit local 2-category isomorphism versus full KL completion | Local construction verified; stronger adjoint triequivalence is separate | B: Thm4.12; C: §4.4 footnote17; higher wreath formula taken for granted, Rem4.20 |
| CM5 | Polynomial/PRA Kleisli ↔ transposed context presentation | Polynomial data, or PRA with indicated left adjoint | S: CM ThmA.4, RemA.5; Capucci 2025 PSSL slides11/14 |
| K1 | Strict Tel-algebras ↔ monoids of strict fibrant spans | Strict maps and normal cleavage; strict units/accumulation | B: Kamiya Cor2.20; only strict subclass |
| K2 | Grothendieck span extension → pseudomonad; telescope comparison | Split left fibrations; for main transport, supplied display contextad and fibrewise comprehension equivalence | B: Kamiya Prop3.2, Prop3.5, Thm4.2; focused proofs inspected |
| K3 | Kleisli comparison on representables | Indexed Grothendieck pseudomonad plus stated transport hypotheses | B: Kamiya Prop3.6; not equivalence on all indexed objects |
| ST | Mixed opwreath → mixed Kleisli category in Cat | Monad T, ζ,d,e, seven axioms in strict 2-category | B: Street Def5, Prop7; adjunction mate correspondence Prop6 left as exercise |
| GA | Pseudo mixed law → two-sided Kleisli bicategory | Pseudomonad, pseudocomonad, supplied coherent law | B: Garner Def14; generic constraints not fully displayed; concrete Mod law Props20,38/Cor39, with Double clubs dependencies |
| WL | Pseudo-law ↔ extension/warping presentations | Invertible structural modifications; extra compatibility W5 | B: Walker Thms4.1.8,5.0.1; source calls overall proof a sketch |
| GL | Pseudomonad/lifting triequivalence; laws ↔ pseudoalgebra liftings | Gray-category setting and compatible higher data | B: Gambino–Lobbia Thms3.4,4.5; dual Cor4.6; routine coherence checks omitted |
| LS | Skew Kleisli and right-unit normalization | Reflexive coequalizers preserved by right tensor for normalization; further adjoint/opmonadic assumptions in application | B: Lack–Street §§4–5, Thms8.1–8.2; cannot drop invertibility from pseudo proofs |
| RW | Factorization → crossing and reconstruction | Strict unique factorization, or explicitly weakened factorization modulo isomorphism | B: Rosebrugh–Wood §3.3/Thm3.8, §§5.7–5.9 |
| LA | PROP composition from factorization | Wide symmetry-containing tensor-closed subcategories; uniqueness modulo permutations | B: Lack Thm4.6; PB/PO examples §§5.3–5.4 |
| SP | Double-category recognition of factorization systems | Exact filler/flatness/bicartesian conditions, not arbitrary double category | B: Štěpán Thms3.3.7,3.3.33; retained squares included |
| FZ | Corelations as Cat pushout | PB/PO, costable factorization, monic M and compatibility of chosen A | B: Fong–Zanasi Assumption1/Thm3.1; abelian Rel≅Corel Cor3.4 |
| PR | Identity-on-objects functor ↔ promonad in Prof | Ordinary categories; pure functor need not faithful | B: Román Thm3.9, AppB.2 |
| LC | Strict local Cat-coend ≅ mixed comma category | Small categories, ordinary strict coend; fixed endpoints | P: mixed_theorem_bridge.md §1 |
| PB | One-sided isoclasses → mixed promonad-law problem | Already constructed one-sided compositions; discard noninvertible cells | P: same §§2–3; retained-cell weak global bridge U |
| LP | List/probability-family dependent mixed composition | Set base, finite positive fibres, independent draws per list occurrence, terminal content fibres | P: nonthin_categorical_test.md; all stated cells checked |

## Source pointers and evidence trail

Primary identifiers: Capucci–Myers [arXiv:2410.21889](https://arxiv.org/abs/2410.21889); Street [1610.07281](https://arxiv.org/abs/1610.07281); Garner [math/0606735](https://arxiv.org/abs/math/0606735); Walker [2102.12468v4](https://arxiv.org/abs/2102.12468v4); Gambino–Lobbia [TAC37(2)](https://www.tac.mta.ca/tac/volumes/37/2/37-02.pdf); Kamiya [2610.00302v1](https://hexagonmath.org/2610.00302v1); Román [2205.07664v4](https://arxiv.org/abs/2205.07664v4).

Exact inspected-source hypotheses and locators are archived in `contextad_scoping_audit_20261101/{contextad_transposition_audit,mixed_baselines,dependent_effect_baselines}.md` and its source manifest/PDFs. Project proofs are in `contextad_reduction_test_20261101/{mixed_theorem_bridge,cell_preservation_reduction,finite_relational_reduction}.md` and `contextad_harder_tests_20261101/nonthin_categorical_test.md`. This guide does not re-open the earlier decomposition-equipment contract or assert that an unchecked translation is a missing theorem in mathematics.

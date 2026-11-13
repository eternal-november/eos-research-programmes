# A construction kit for context-dependent categorical computation

Conceptual map for the theory guide, 1 November 2026. Based on the already inspected primary-source dossiers, not a fresh literature census. The purpose is understanding and organization: which mathematical tools do which jobs, how they fit together, and what information a comparison preserves.

## 1. Three axes, not one ladder of generality

The most useful picture is a construction kit with three independent axes.

1. **Shape of an arrow.** What extra input may an arrow use? What extra output may it produce? Typical shapes are `GA → B`, `A → TB`, and `GA → TB`.
2. **Dependence and composition.** Are the extra objects fixed globally, parameterized by a monoidal category, or dependent on the current object and earlier choices? What transports parameters and combines successive stages?
3. **Information retained by comparison.** Are we comparing functions, arrows up to isomorphism, whole categories of parameterizations, or observation laws? An equivalence at one level need not be an equivalence at another.

Contextads primarily organize axis 2 while producing a particular shape on axis 1. Wreaths organize the construction itself. Distributive laws organize interaction. Prof/coends and factorization provide alternate representations or recognition principles. Telescopes describe freely assembled dependent sequences. These are complementary jobs, not rival answers to one question.

## 2. First layer: ordinary arrows and one-sided computations

For a monad `(T,η,μ)` on C, Kleisli arrows have shape `A → TB`. Composition applies T to the second arrow and then μ. For a comonad `(G,ε,δ)`, co-Kleisli arrows have shape `GA → B`; composition duplicates context using δ and then applies G to the first arrow. These are the cleanest examples of producing content and using context.

Two tiny examples:

- A monoid W gives writer arrows `A → W × B`. Multiplication combines the two recorded monoid elements.
- A fixed set E gives the product comonad `G(A)=E×A`. Co-Kleisli arrows `E×A → B` use a shared parameter; diagonal copying of E supplies δ. In Set, currying gives `Set(E×A,B) ≅ Set(A,B^E)`. With the induced reader monad structure on `(-)^E`, this respects Kleisli/co-Kleisli composition. This is an **adjunction-induced correspondence**, not an identification of the two endofunctors.

The second example already warns against reading “context” and “content” as immutable physical meanings: a parameter can move across a hom by a mathematical adjunction.

### Monoidal parameters: actegories and Para

A right action of a monoidal category M on C supplies parameterized arrows `(P,f:A ⊙ P → B)`. Successive parameters combine as `P ⊗ Q`; action coherence relates iterated action to the tensor action. This is the Para pattern. M need not be cartesian: the tensor is how parameters combine, not automatically copying or categorical product.

**Map edge:** suitable monoidal actions specialize the contextad data; their contextful construction recovers Para, with the corresponding parameter maps as cells. This is an **instance/recovery statement**, not an equivalence between all contextads and actegories. Contextads add object-dependent parameter fibres and transport along actual arrow bodies.

Source: Capucci–Myers (CM), examples in §3 and the contextad definition below.

## 3. Second layer: parameters that depend on their location

### Contextads

Write an indexed category `M:C^op → Cat` and extension `A ⊙ P` for `P ∈ M_A`. A contextad gives:

- a unit context `I_A` and `ε:A ⊙ I_A → A`;
- a combination `P ⊗ Q ∈ M_A` for `Q ∈ M_(A ⊙ P)`;
- a comparison `δ:A ⊙ (P ⊗ Q) → (A ⊙ P) ⊙ Q`;
- coherent transport and grade unit/associativity data.

A contextful arrow is `(P,f:A ⊙ P → B)`. Given the next arrow `(Q,g:B ⊙ Q → D)`, the composite parameter is **`P ⊗ f*Q`**. Pulling Q back along the actual f is the crucial dependence: the next requirement lives over B, whereas the preceding extended input is `A ⊙ P`.

The maps ε and δ need not be invertible in the existing definition. The specified grade coherence and transport comparisons are invertible. These are different kinds of structural maps.

**Equivalent presentation:** a cloven fibration and indexed category are related by the Grothendieck construction, up to the usual appropriate equivalence and choices of cleavage. This reorganizes the same dependence; it is not an additional effect.

**Specializations:** comonads recover co-Kleisli, actions recover Para, pullback-stable display maps recover display spans. A comprehension category with unit and strong dependent sums satisfying Beck–Chevalley supplies another contextad instance. Beck–Chevalley says combining dependent stages is compatible with change of base.

Sources: CM Defs 3.15, 3.17, 3.26; Ex3.20 (comprehension), Ex3.21 (display spans). The general coherent-transport version is already in §7, Defs7.9–7.10.

### Contentads

Reverse the relevant variance: use `N:C → Cat`, covariant transport `u_!`, and extension `Q ▷ B` for `Q ∈ N_B`. A contentful arrow is `(Q,f:A → Q ▷ B)`. An opfibration replaces a fibration, and accumulation combines output stages.

For precise typing, if `Q ∈ N_D` and `P ∈ N_(Q ▷ D)`, write `combine_D(Q,P) ∈ N_D`. For `f:A → P ▷ B` and `g:B → Q ▷ D`, the composite parameter is `combine_D(Q,g_!P)`.

**Map edge:** contextads and contentads are **variance-dual construction patterns**, implemented in appropriately dual higher ambient settings. The assertion is not that two arbitrarily chosen structures on C are automatically compatible or literally identical endomonads in one ambient category.

**Specializations:** monads recover Kleisli; actions give Copara; pushout-stable codisplay maps give cospans. Source: CM §6, especially Defs6.1–6.3 and Ex6.4–6.7.

### A small transposition lesson

In Set a writer arrow `f:A → W×B` is exactly a pair `(w:A→W, b:A→B)`. One can regard `w` as an A-indexed grade with unchanged extension A. Sequencing multiplies the first grade with the next grade pulled back along b. This shows concretely how an output presentation can become a dependent-grade presentation.

This arrow-level calculation is an elementary teaching example. It should not be inflated into a blanket theorem that all context/content transpositions preserve every cell and every ambient universal property. CM Appendix A states the polynomial version; its stronger source-status qualifications are collected at the end.

## 4. Third layer: formal organization of these constructions

### Wreaths, KL and EM

The formal theory of monads treats monads themselves as objects of higher categories. Wreaths encode additional monadic structure in such an ambient, and wreath products assemble the resulting computation.

CM realizes contextads as wreath/pseudomonad data using displayed spans and the KL-side machinery; Ctx is the resulting wreath product. Contentads use the corresponding EM/right-opfibrant side. This **structural representation** explains why Kleisli, Para and Span constructions share a composition pattern. It is more informative than saying they merely have similar formulas.

There are two levels to keep separate:

- CM Thm4.12 supplies an explicit local 2-category isomorphism, and Thms4.18–4.19 connect this organization to contextads and Ctx.
- The stronger free tricocompletion identification discussed in §4.4/footnote17 is explicitly conjectural there; Remark4.20 takes a higher wreath-product formula by analogy. The concrete formulas can still be studied directly without settling that stronger universal description.

### Structured lifting

CM Thm5.16 supplies a **lifting theorem**: specified compatible 2-algebraic structure on the contextad induces corresponding structure on Ctx. The hypotheses are those of Def5.13 (including compatibility of action, multiplication and unit). This provides a reusable route for moving structure through the construction, rather than an automatic compatibility theorem for unrelated effects.

## 5. Fourth layer: interacting input and output mechanisms

The mixed arrow shape is `GA → TB`, or dependently `A ⊙ P → Q ▷ B`. The central issue is moving the output mechanism of the first stage past the input mechanism of the second.

### Supplied interaction: distributive laws and opwreaths

For a comonad G and monad T, an appropriately oriented mixed distributive law `GT → TG` supplies that crossing. Unit, counit, multiplication and comultiplication equations make the resulting composition lawful.

Street's mixed **opwreath** is broader: G need not already be an ordinary comonad. Alongside the monad T one has `ζ:GT→TG`, `d:G→TGG`, and `e:G→T`, satisfying seven axioms. Its mixed Kleisli arrows are `GA→TB` (Def5/Prop7). Ordinary mixed laws are a **special case** of this packaging. The mixed wreath uses the opposite EM-side orientation; these names should not be interchanged.

Garner's Def14 gives the **higher analogue**: a pseudocomonad, pseudomonad and mixed pseudodistributive law yield a two-sided Kleisli bicategory. The same paper constructs a substantive example in Mod using matchings and verifies its coherence (Prop38/Cor39). Thus both the packaging and interesting derivations of laws already exist.

### Alternate presentations of a law

Walker Thm5.0.1 relates pseudodistributive laws, algebraic presentations and compatible Kleisli extensions. Gambino–Lobbia Thm4.5 identifies laws with liftings to pseudoalgebras; Cor4.6 gives a right-module/Kleisli counterpart.

**Map edge:** these are **equivalence-of-data/recognition theorems**, in the specified higher setting, not claims that all pairs interact. They are useful positively: choose the presentation in which the desired example is easiest to construct and verify. A lifted action may be easier to see than a large pasting diagram, or vice versa.

For noninvertible coherence, Lack–Street's skew warpings and normalization provide a separate established toolkit. Thm8.1 needs appropriate reflexive coequalizers preserved by right tensoring; Thm8.2 adds adjoint/opmonadic conditions. This is a change of structural regime, not an instruction to erase invertibility hypotheses from a pseudo theorem.

## 6. Fifth layer: alternate representation and recognition

### Promonads and coends

A category of effectful arrows with a pure identity-on-objects functor `J:C→M` is equivalently a promonad on C in Prof (Román Thm3.9; proof B.2). The unit inserts pure arrows; multiplication composes effectful arrows. J need not be faithful.

A coend describes composition while balancing over the intermediate pure object: moving a pure arrow to the left or right representative gives the same composite. For left-to-right notation,

`(M ⋄ N)(A,B) = ∫^Z M(A,Z) × N(Z,B)`.

A law `N ⋄ M → M ⋄ N` then makes `M ⋄ N` a composite promonad. This is the ordinary **change of presentation** of the mixed-composition problem.

The project's exact local cell-preserving calculation is:

`∫^Z (e ↓ Z) × (Z ↓ d) ≅ (e ↓ d)`

for small categories and functors `e:K→C`, `d:L→C`, using the ordinary strict Cat-valued coend. It composes factorizations and retains all commuting parameter-map squares. It is a **local categorical isomorphism**, not by itself a global pseudo composition theorem.

For the existing Ctx/Cnt constructions, passage to isomorphism classes of hom objects gives an ordinary Prof presentation but forgets noninvertible cells. This is a **quotient/change of information level**, not a full equivalence of the original cell-rich structures. This single distinction keeps much of the theory map honest and intelligible.

### Factorization recognizes crossings

If every relevant composite has a suitably unique normal factorization, refactorization defines the crossing and uniqueness proves its equations. Rosebrugh–Wood §3.3/Thm3.8 supplies the strict category version. Lack Thms3.8 and4.6 give PRO/PROP recognition, the latter modulo permutations with the stated symmetry-containing tensor-closed subcategories.

This is a **recognition/construction principle**, not an arbitrary factorization axiom: strict unique factorization and an orthogonal factorization system are distinct structures. Štěpán's Thms3.3.7 and3.3.33 organize corresponding strict and orthogonal cases with double categories and their cells. It is therefore useful to select the factorization notion matching the intended retained information. A factorization theorem supplies its own specified crossing, not automatically an additional pullback/pushout interchange for every normalization.

## 7. Telescopes: building a sequence versus combining it

A telescope is a sequence of choices in which each later choice may depend on earlier ones. The telescope construction freely assembles those sequences. An algebra for it supplies a coherent way to combine a sequence into one context. This is the categorical counterpart of the difference between a list of composable instructions and their composite.

Kamiya Cor2.20 identifies strict Tel algebras with monoids in the specified strict/cartesian span setting: a strict subclass of contextads. Prop3.2 is a monoidal Grothendieck-extension comparison. Thm4.2 transports the structure through a supplied fibrewise comprehension equivalence with chosen pullbacks and pasting compatibility. Prop3.6 compares Kleisli/co-Kleisli constructions on representables.

**Map edges:** strict-algebra identification; monoidal construction; transport along comprehension equivalence; representable-level comparison. These are different statements. Together they explain dependent sequencing and representation, without making telescope construction a universal solution to mixed interaction.

## 8. A short learning path

1. **Reader and writer.** Compute two composites, then curry reader arrows and separate writer grades from bodies. Learn that arrow presentations can change.
2. **Para with a monoidal action.** Track the tensor of two parameters and one parameter map. See explicitly why tensor is not automatically copying.
3. **Display spans.** Calculate one pullback composite. Then read the contextad formula `P⊗f*Q`: pullback is now recognized as transport, not an isolated trick.
4. **Dependent contexts.** Use a family of sets and its dependent sum; concatenate a two-stage telescope. Compare reindexing before and after combination. Read CM Ex3.20 and Kamiya's strict telescope result.
5. **A mixed law.** Study `List(D X) → D(List X)` for the finite-distribution monad D: independently sample each list occurrence, then check list concatenation and distribution multiplication. Repeated occurrences remain separate samples, and the empty list has its deterministic singleton distribution. This is familiar traversal/commutative-effect mathematics, not a proposed new effect theory. Source: Jaskelioff–Rypacek, Thm3.7 and Lemma4.1; the latter requires a commutative monad. In the project’s dependent probability-family example the independent tensor has underlying cartesian product of sets but is not the categorical product in the category of probability-preserving maps.
6. **Change representation.** Re-express ordinary pure/effectful categories as promonads; work through coend balancing on one pure map. Then distinguish the set-level presentation from retained parameter-map cells.
7. **Formal organization.** Read wreath/KL/EM and the law/lifting equivalences after the concrete constructions have meaning. Finish with factorization recognition as a way of deriving the compatibility data rather than guessing it.

## 9. Compact status legend for the guide

- **Established source machinery:** one-sided contextad/contentad constructions; the cited mixed/opwreath and pseudo-law frameworks; law/lifting presentations; ordinary promonads; the specified factorization recognition theorems.
- **Source-stated restricted results:** telescope strict-algebra and comprehension comparisons, with their explicit hypotheses. Their restricted scope is useful mathematical content, not a defect.
- **Explicit source conjecture:** the stronger KL tricocompletion identification isolated by CM §4.4/footnote 17.
- **Source statements with proof omitted:** CM Appendix A polynomial theorem, explicitly unproved in Remark A.5, and the broader PRA comparison stated without a full proof in the 2025 slides.
- **Not yet assembled by this project:** the global cell-retaining pseudoambient comparison joining the local Cat-coend calculation to all weak dependent transport. This is an unchecked bridge in our account, not evidence of a new literature gap.

The organizing conclusion is positive: there is already a substantial theory of dependent parameters, mixed composition, law recognition, representation and higher coherence. Our immediate task is to learn how to select and connect these tools faithfully, not to manufacture a larger umbrella before understanding the existing ones.

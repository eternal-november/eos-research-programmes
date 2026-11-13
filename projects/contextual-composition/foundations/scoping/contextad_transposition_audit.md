# Contextads, transposition and telescope results: primary-source audit

Audit date: 1 November 2026. Scope: the first scoping obligation, not execution or adoption of the main theorem contract. The programme is generalizing contextads; recovery is one application. This note is a source-and-typing audit, not an exhaustive novelty verdict.

## Conclusions that affect the charter

1. Existing contextads already give dependent context substitution, partial maps, state effects, and many structured constructions. A theorem that merely supplies dependent sums with Beck–Chevalley, or transfers a known contextad along a comprehension equivalence, needs comparison against these baselines.
2. The two one-sided structures are not merely two endofunctors with an ordinary distributive law. Their fibres have opposite variance and their extensions change the base. A mixed normal form must account for this change before generic coherence results can be applied.
3. The current Capucci–Myers arXiv record still lists only v1. Its polynomial transposition theorem is explicitly left without proof; 2025 slides state a general PRA result but do not supply its proof. This is a meaningful claimed baseline, not either a verified import or untouched territory.
4. A newer 25-page telescope manuscript was located and its relevant proofs read. It proves restricted dependent-sum/representation results, rather than arbitrary contextad recognition or mixed context/content composition. Its crucial hypotheses are a pre-supplied display contextad and a fibrewise comprehension equivalence.
5. For this contract, the useful increment remains a derived, independently checkable interaction criterion for the selected mixed class, including comparison/necessity. The evidence does not support advertising dependence, contextad transport, a free telescope construction, or a chosen mixed distributive law as that increment by themselves.

## Primary sources and inspection extent

**CM.** Matteo Capucci and David Jaz Myers, *Contextads as Wreaths; Kleisli, Para, and Span Constructions as Wreath Products*, arXiv:2410.21889v1, 29 October 2024. https://arxiv.org/abs/2410.21889 ; PDF https://arxiv.org/pdf/2410.21889 . Landing page checked this run: only v1, 84 pages. Existing downloaded PDF/text inspected directly, including definitions and proofs identified below.

**PRA slides.** Matteo Capucci, *Contextads abridged*, PSSL110, May 2025. https://matteocapucci.eu/assets/2025/05/pssl-110.pdf . Inspected relevant construction and theorem slides directly. PDF overlays differ from slide numbers. Author's current work listing https://matteocapucci.eu/work/ still describes the talk as gesturing toward general PRA transposition. This listing is not a mathematical proof.

**K.** Kotaro Kamiya, *The Grothendieck construction between the telescope monad and contextads*, Hexagon 2610.00302v1, 17 October 2026. https://hexagonmath.org/2610.00302v1 ; PDF https://hexagonmath.org/pdf/2610.00302v1 . The actual 25-page manuscript was downloaded and read through the proofs in Sections 2–4 and Appendix A.7–A.8. The deposit declares mixed human/AI writing and partial human understanding. That provenance neither proves nor refutes a theorem; the classifications below are based on inspected arguments. No blanket independent certification of the manuscript or all cited dependencies is claimed.

A cited companion *The contextad of double telescopes* appears in K's references as a 2026 preprint. Targeted exact-title and author/contextad searches did not locate its primary text. It is not an imported result in this audit.

## A. Existing contextad data and composition

CM Definition 3.15 pp19–22, indexed restatement Definition 3.26 pp29–30, and Definition 3.17 pp22–24 give the following typed control, with notation normalized to avoid minor printed ordering inconsistencies.

- An indexed category M:C^op→Cat (or a cloven cartesian display fibration p:M→C) and extension functor on its total category, written A⊙P for P∈M_A.
- Unit I_A∈M_A; combination P⊗Q∈M_A for Q∈M_(A⊙P).
- Structure maps ε_A:A⊙I_A→A and δ_(P,Q):A⊙(P⊗Q)→(A⊙P)⊙Q. These need not be invertible.
- Cartesian unit/combination functors, invertible grade unitors/associator and their coherence. Noninvertible ε or δ is not a weakening beyond the existing definition.
- A loose arrow (P,f):A⇒B has f:A⊙P→B. Given (Q,g):B⇒C, its grade is P⊗f*Q. Its body is δ followed by the action on the cartesian lift of f and then g. The pullback is along the actual body f, so Q is transported to the changed input object A⊙P.

CM Example 3.20 pp25–26 assumes a comprehension category with unit and strong dependent sums, including Beck–Chevalley and closure of display composition. It constructs context combination from those sums; Beck–Chevalley is exactly what makes the multiplication cartesian. Example 3.21 gives display spans, and the partial-map case follows by choosing appropriate displays. These already cover substantial input dependence.

CM Theorem 5.16 pp58–59 is a structure-lifting control: for a 2-monad T on the given paradise, a colaxly/strongly T-structured contextad produces the correspondingly structured pseudocategory. Definition 5.13 includes strict T-structure on the normal display fibration, colax action and compatible multiplication/unit/coherence. The proof checks strictness of source and target using the lifted pullback construction. This is not an automatic theorem that arbitrary desired enrichment or a second effect interacts with a contextad.

CM Section 7, Definitions 7.9–7.10 pp70–74, already replaces universal cartesian reindexing by coherent transport over a pseudocategory. Invertible transport compositors, unit-context and combination comparisons remain required. A proposal consisting only of 'choose transport rather than a pullback' is therefore already within the paper; a proposal using noninvertible structural comparisons requires further work.

## B. Contentad typing and the mixed mismatch

CM Definitions 6.1–6.3 pp63–65 dualize to a right-opfibrant span and Cnt. A coparadise has the codomain projection of the arrow object displayed. The right-leg opfibration supplies covariant transport. A single common ambient setting for both constructions must support the relevant left- and right-displayed structures; selecting Cat is one possible control, not a mixed theorem.

For reliable typing use a separate action symbol and normalize the order as follows:

- N:C→Cat, with u_!:N_A→N_B for u:A→B, and extension P▷A.
- Unit J_A∈N_A, map η_A:A→J_A▷A.
- Given Q∈N_C and P∈N_(Q▷C), an accumulation combine_C(Q,P)∈N_C, with μ:P▷(Q▷C)→combine_C(Q,P)▷C.

For f:A→P▷B and g:B→Q▷C, g_!P lies in N_(Q▷C). The composite passes through g_!P▷(Q▷C), then uses μ; its grade is combine_C(Q,g_!P). This is equation (6.1.8) with explicit indexing. The source's surrounding prose and tensor ordering are inconsistent if copied literally: it writes the resulting combination as g_*P⊗Q. A charter should define its own ordered operation and verify types rather than silently rely on ambiguous typography.

Now the candidate mixed body f:A⊙P→Q▷B has P∈M_A and Q∈N_B. A following requirement R∈M_B cannot simply be reindexed along f: f lands in Q▷B, not B. To form a subsequent action one must specify the interaction that relates requirements at B to requirements over produced content Q▷B, along with the corresponding content transport. This is the exact missing entry point before a generic distributive-law theorem can be specialized. The source does not provide an all-purpose solution in Section 6.

## C. Universal-property and transposition proof status

CM Theorem 4.12 p40 gives an explicit local isomorphism of 2-categories; its proof in pp36–40 constructs the maps and verifies the algebra/cartesian conditions. This is distinct from a free tricocompletion theorem.

CM Section 4.4 p40 labels the full universal-property identification of the reduced KL presentation conjectural. Footnote 17 separates known triessential surjectivity from the adjoint triequivalence still conjectural there. Theorem 4.18 p43 transports the local structure to fSpan; Theorem 4.19 identifies Ctx as the wreath product at the stated level. Remark 4.20 additionally takes for granted the higher wreath-product formula in analogy with the lower-dimensional construction. Therefore an argument requiring the full free KL/EM tricategorical universal property must identify the exact verified result it imports. The explicit Ctx formulas and their directly checkable coherence are not invalidated merely because the stronger universal presentation is unsettled.

CM Appendix A, Theorem A.1 and Definition A.3 p83, spell out a polynomial/container monad by shape, position, sequencing and splitting operations, and give the transposed grades X→S and action Σ_(x:X)P(s(x)). Theorem A.4 pp83–84 states an identity-on-objects Kleisli–Ctx isomorphism by the ordinary shape/body correspondence. Remark A.5 explicitly says the theorem is not proved there, with a proposed abstract argument via a left adjoint in fSpan for any PRA monad. The shape/body bijection is transparent, but that is not a source-supplied verification of all structure.

The 2025 slides, slide 11 (PDF p32) and slide 14 (PDF pp39–41), use a PRA T and left adjoint L:C/T1→C to the local-right-adjoint factor, giving the span C←C/T1→C. They state the broader Kl(T)≅Ctx(L) theorem via f:X→TY, shape T!∘f:X→T1 and body L(shape)→Y. No complete proof is supplied in the slides. Classify this as a precisely stated, credible claimed general result whose complete proof remains unverified in the inspected sources. A future charter must not claim discovery of this question, nor count simply repeating its statement as progress. A direct proof in a selected class could be useful but must be attributed and distinguished from a novel generalization.

## D. Newer telescope manuscript: exact scope and checked argument

### D1. Strict telescope algebras are only strict contextads

K Definition 2.1 pp4–5 fixes a base category C and uses endospans with strict leg-preserving maps, tensor by strict pullback, and canonical reassociations. Lemma 2.2 proves countable coproducts are taken in CAT and tensor preserves them separately. The argument uses disjoint coproducts and pullback; it is not a statement about an arbitrary monoidal ambient category.

Definition 2.10 p7 restricts to left-fibrant spans and cartesian maps. The subcategory fSpan_s(C) has identity colaxators. Lemma 2.7, using the pullback/composite fibration lemmas A.3–A.4, proves tensor powers preserve the relevant fibrations/cartesian maps. Coproducts preserve these fibrewise as well. Thus Tel restricts to that subcategory.

Corollary 2.20 p10 identifies strict algebras of Tel there with monoids in fSpan_s(C). Its inverse extracts length-zero and length-two operations; the algebra equation gives the unit/associativity and all comb maps. Under NORMAL cleavage, these are the manuscript's strict contextads: ε=δ=id and λ,ρ,α identities (Definition 2.12 pp7–8). This is not recognition of all ordinary contextads, whose structure maps may be noninvertible. The abstract's shorthand must be read with these restrictions.

### D2. The monoidal extension is a concrete existing construction

Construction 3.1 / Proposition 3.2 pp13–14 require split left fibrations. For a span M its extension on indexed categories is

  P_M(Y)(B) = ∫_(P∈M_B) Y(B⊙P).

Right-colax cartesian span maps act by reindexing along their colaxator. The monoidal comparison identifies a Grothendieck construction of dependent pairs with the iterated Grothendieck construction. Cartesianity of the map gives pseudonaturality; the canonical tuple/composite-fibration identifications give coherence. Fibres of coproducts and coproducts of integrands prove preservation of coproducts. Accordingly P transports pseudomonoids to pseudomonads. The displayed proof was inspected; no substantive failure was found in this focused check. It is not a general mixed context/content distributive law.

### D3. Main transport theorem assumes the recognition data

From §3.2 p14 onward, S:C^op→CAT is a strict indexed category and χ:∫S→M is a FIBREWISE COMPREHENSION EQUIVALENCE onto a specified display contextad M. Definitions 2.14–2.17 pp8–9 require normal chosen pullbacks, identities and composition of displays, and the selected square class closed under vertical pasting. Lemma 2.23 p12 gives a cartesian pseudo-inverse. Lemma 2.24 pp12–13 makes relevant hom-categories thin because the source/target pair is faithful and colaxators are invertible.

Proposition 3.5 pp15–16 transports the display contextad along χ. Its ε and δ are invertible. Theorem 4.2 pp18–19 identifies the n-ary dependent sum with the transported Tel pseudoalgebra and compares its extension with iterated Grothendieck-monad multiplication. Its proof uses the pre-existing equivalence, transport of algebra structure, and the thinness lemma to force coherence. Appendix A.7–A.8 pp23–24 constructs Tel on normally cloven spans with INVERTIBLE colaxators; the constraints are canonical cartesian-lift comparisons, with the coherence checked by uniqueness of the relevant cartesian factorizations.

The argument is meaningful and explicit, but does not infer a contextad from an arbitrary computational double category. It assumes a display contextad and comprehension equivalence at the outset. It also covers a strong/invertible-extension subclass rather than arbitrary noninvertible ε,δ. The independently usable part is the specified display/comprehension criterion, not a universal intrinsic recognition theorem.

### D4. Kleisli comparison is restricted to representables

Proposition 3.6 pp16–17 constructs the Grothendieck pseudomonad on [C^op,CAT] and compares its Kleisli construction ON REPRESENTABLES with coKl(∫S). Two-Yoneda turns yB→P_(∫S)(yX) into (F,f:B.F→X); the proof computes the composite as (F combine f*G, δ followed by f's lift followed by g), and compares the cells as well. It gives an equivalence identity on the base/tight arrows. It is not an equivalence of the entire Kleisli bicategory on arbitrary indexed categories with a category whose objects are only C, and it is not arbitrary PRA transposition.

### D5. Audit status

Treat the narrowly scoped arguments above as inspected positive related results, subject to their stated hypotheses and ordinary imported Grothendieck/transport facts. This audit did not independently formalize them or verify every cited theorem. The source gives actual proofs, unlike the unproved A.4/PRA slide statement. No theorem in it identifies a dependent context/content interaction or derives the mixed compatibility sought by the present workstream.

## E. Scoping consequences

- Choose and type context and content fibres separately before proposing a common normal form. A plain arrow-shaped expression does not define their interaction.
- A display/comprehension route is a useful tractable subclass. If selected, the charter must disclose that comprehension equivalence and Beck–Chevalley already provide strong structure; cannot describe those as discovered semantics or intrinsically reconstructed interfaces.
- A free telescope or Grothendieck-extension theorem is a baseline, not sufficient completion of the mixed contract. It can supply a checkable normal-form/presentation tool whose interaction with the opposite variance remains to be proved.
- Keep a map from every planned conclusion to a specific existing theorem or a genuinely open proof obligation. The additional result should derive compatibility from a stated structural criterion, or establish a sharp preservation/normal-form obstruction with a useful repair.
- Do not rely on the strongest universal KL/EM completion claim without its proof status, and do not automatically promote a representable-only comparison to all objects or a strong-contextad subclass to arbitrary contextads.
- No safe semantic-discovery algorithm, runtime permissions, partial undo, global disintegration, noncartesian ambient extension or general internal language is established by these baselines. Those are application or programme-level questions, not prerequisites smuggled into this first theorem.

End of audit.

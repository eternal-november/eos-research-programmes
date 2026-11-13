# Mixed distributive laws, liftings and wreaths: strongest-source audit

Audit date: 1 November 2026. Scope: the first scoping/audit obligation only. This is a primary-source comparison, not adoption of a theorem target or an exhaustive novelty review. Primary PDFs were downloaded and the indicated definitions and proof arguments inspected. No theorem is claimed newly proved here.

## Executive finding

There is a stronger baseline than the draft's fixed comonad–monad control: **Street already constructs mixed opwreath Kleisli categories whose context duplication and counit themselves produce monadic effects.** Generic coherent mixed composition, including that relaxation, should not be the claimed advance. Walker and Gambino–Lobbia also show that changing from laws to compatible liftings, pseudoalgebras or no-iteration operators does not by itself add mathematical content.

The substantive prospective increment is a *derived dependent interaction* for declared display/codisplay data, and a typed bridge from those data into the relevant higher mixed construction. A strict 2-categorical mixed-wreath theorem is not automatically a theorem for contextads living in a tricategory of displayed spans. This is a precise applicability gap, not evidence that a higher generalization does not exist.

## 1. Walker: law presentations and Kleisli extension

Primary: Charles Walker, **Presentations of pseudodistributive laws**, arXiv:2102.12468v4. https://arxiv.org/pdf/2102.12468v4

For two pseudomonads on a 2-category, Theorem 5.0.1 (p.26) equates pseudomonoidal, decagon, pseudoalgebra, no-iteration and warping descriptions with compatible extension of one pseudomonad to the other's Kleisli bicategory. Theorem 4.1.8 (p.14) requires a pseudomonad morphism and opmorphism together with the additional W5 compatibility. Merely having both structures is insufficient. Definition 4.1.3 uses invertible modifications. The law transformation itself is not required invertible.

The proof is an explicit chain: Lemma 5.1.2 changes pentagons to a decagon; Propositions 5.2.1–2 form the pseudoalgebra and extension; Corollaries 5.3.6/5.4.1 and Propositions 5.5.2–3 establish equivalences. Inspected these transformations and inverse constructions. The paper calls the overall argument a sketch and omits some modification-level verifications; this is a proved published result with stated omissions, not an unproved conjecture. Invertibility is used in the comparison argument (Remark 5.4.2).

**Application judgment (our analysis).** If a proposed construction supplies a compatible lifting and then extracts a law, it may already be this theorem. The charter must identify what independently constructs the lifting or forces a nontrivial compatibility condition. Requiring an extension to preserve its pure/Kleisli embedding is part of the hypothesis, not a consequence to advertise independently. Noninvertible *structural* comparisons are outside the equivalences as stated. Walker's result is for two pseudomonads; turning the contract's context/content pair into that input is an obligation, not a substitution of notation.

## 2. Gambino–Lobbia: the formal lifting theorem

Primary: Nicola Gambino and Gabriele Lobbia, **On the formal theory of pseudomonads and pseudodistributive laws**, TAC 37 (2021), 14–56. Author version inspected: https://eprints.whiterose.ac.uk/id/eprint/170302/1/pseudomonads-tac.pdf . Journal: https://www.tac.mta.ca/tac/volumes/37/2/37-02.pdf .

For a Gray-category K, Theorem 2.5 constructs Psm(K); Theorem 3.4 proves its triequivalence with Lift(K). Theorem 4.5 identifies a pseudodistributive law d:ST⇒TS with lifting T to pseudo-S-algebras. Corollary 4.6 gives the dual right-module formulation; when represented, it yields extension to a Kleisli object. See §§3–4, author printed pp.23–30 (PDF pp.24–31).

The inverse lifting construction evaluates on the free pseudoalgebra S, producing φ₀:TFS→FS, then obtains φ:TF→FS by composing TFs with φ₀. This is not an abstract existence assertion without reconstruction. The proof of Theorem 4.5 uses Psm(Psm(K)) and preservation of triequivalences. Some routine coherence/quasi-inverse calculations are expressly omitted; inspected the argument and reconstructed cell types, not a machine verification of all pastings.

**Application judgment (our analysis).** This supplies a strong anti-reinvention test: an “intrinsic criterion” stated as a fully coherent algebra lifting is equivalent packaging unless an independent construction of that lifting is provided. A strictifying Gray-category replacement does not automatically preserve the chosen displayed-span substructure or recover the desired pure arrows; any such bridge needs explicit comparison data. The theorem's data and variance must be checked before appealing to its EM or KL form.

## 3. Street: mixed opwreaths are the closest direct control

Primary: Ross Street, **Wreaths, mixed wreaths and twisted coactions**, arXiv:1610.07281. https://arxiv.org/pdf/1610.07281 . The downloaded PDF carries arXiv v1 identifier and a later internal date; no priority conclusion depends on that discrepancy.

Definition 3 (p.9) makes a mixed wreath a comonad in EM(K). Definition 5 (p.10) makes a mixed *op*wreath a comonad in KL(K). For a monad T on A in a strict 2-category, the latter has endomorphism G and cells

    ζ:GT⇒TG,   δ:G⇒TGG,   ε:G⇒T,

subject to seven displayed axioms. G need not separately be an ordinary comonad. Proposition 7 (p.11) states the mixed Kleisli representing property; in Cat its arrows are A(GA,TB). Proposition 6 identifies opwreaths with wreaths under an adjunction G⊣S. Section 3 gives the construction by applying the appropriate completion functors, the representing properties and convolution formula; the mate correspondence is left as a string-calculus exercise. This is broader than the ordinary fixed mixed-law control.

**Typed formula checked (our reconstruction of source formula 3.15).** For f:GA→TB and g:GB→TC:

    GA --δ_A--> T G G A --T G f--> T G T B
       --T ζ_B--> T T G B --T T g--> T T T C --μ_C^(3)--> T C.

The identity is ε_A:GA→TA. Ordinary comonad data (δ⁰,ε⁰) and a compatible λ:GT⇒TG give the special case δ=η_GG∘δ⁰ and ε=η∘ε⁰; monad unit laws reduce the convolution to the contract's ordinary formula. Thus “allow effectful duplication and discharge of context” is not, by itself, a new generalization.

**Orientation warning.** Street's mixed wreath uses ξ:TG⇒GT (EM orientation). The draft's arrows GA→TB require the *opwreath* direction GT⇒TG (KL orientation). Calling both simply “mixed distributive law” without choosing variance conceals a real typing distinction. No invertibility of ζ is imposed, but that does not remove the seven axioms.

## 4. Skew weakening already has a substantial baseline

Primary: Stephen Lack and Ross Street, **On monads and warpings**, Cahiers 55-4 (2014), pp.244–266. https://cahierstgdc.com/wp-content/uploads/2017/05/LackStreet_55-4.pdf

Sections 4–5 construct a skew Kleisli bicategory from a skew warping. Proposition 5.2 derives three axioms from two only when the relevant comparison maps are invertible. Theorem 8.1 normalizes a skew monoidal category using right-unit modules, assuming particular reflexive coequalizers preserved by right tensoring. Theorem 8.2 applies when i:A→B has a right adjoint, is opmonadic, and specified hom-functors preserve reflexive coequalizers. See printed pp.251–253 and 263–264. The construction and proof of the normalization, including its universal factorization, were inspected.

**Application judgment.** A proposal to weaken all comparison isomorphisms cannot inherit the pseudo proofs unchanged. Conversely, a claimed normalization needs comparison against this theorem before being called new. These are genuine independent categorical hypotheses, so this is a useful model for what a noncircular compatibility criterion might look like. It is not currently a theorem about the contract's dependent mixed data.

## 5. Exact applicability to contextads: what has and has not been supplied

Capucci–Myers places contextads as pseudomonads in the KL-side higher ambient, via left-fibrant spans and colax maps (Theorems 4.18–4.19). Contentads instead use right-opfibrant spans with the opposite colax direction and the EM-side presentation (§6, Definition 6.2 and (6.1.1)–(6.1.3)). These objects are not literally two endopseudomonads of an already chosen 2-category with a supplied Walker law. Nor is an arbitrary pair automatically Street's comonad in KL(K).

The source's §4.4 (p.40, footnote17) expressly isolates a conjectural full universal-property identification for the displayed tricocompletion: triessential surjectivity is known there, promotion to the specified adjoint triequivalence is the conjectural part. Therefore distinguish an explicit typed construction and concrete coherence proof from any stronger result invoking the full universal completion. The reported concrete contextad results are not all thereby disproved; the extra universal-property import is what needs a separate verified source or conditional label.

A bridge useful to the contract should specify:
1. A common ambient and exact opposites/dualities for both kinds of data.
2. Which endomorphisms, cells and modifications form the mixed structure.
3. How an independently available crossing or factorization constructs those cells.
4. Why dependent reindexing/pushforward and context/content accumulation preserve them.
5. Which higher coherence is derived from universal properties, and which remains input.
6. How pure/tight arrows and one-sided structures are recovered, with the exact comparison level.

This list identifies proof obligations. It is not a claim that furnishing the list as axioms would solve the problem.

## 6. Scope implications

Keep the proposed substantive target at the level of **deriving a stable dependent crossing and proving that it realizes an existing mixed construction**, with a bounded converse for the chosen representation. Count the generic convolution/law-lifting equivalence as imported infrastructure. A one-sided presentation may already suffice; the comparison should describe the extra distinctions rather than require an absolute no-encoding theorem.

The candidate factorization c r = r' c' is promising only after its base-change, pasting and accumulation stability is checked. Rosebrugh–Wood strict factorization and the span/cospan distributive-law results are detailed in the accompanying effect and factorization ledger. This audit does not assume that a pointwise factorization gives those coherences. Likewise, allowing lax comparisons is a separate branch with skew baseline, not a harmless notation change.

## Proof-access boundary

The original Lack–Street 2002 full proof was not retrieved in this pass; no direct proof claim here relies on its abstract. Street's later explicit mixed construction and the contextad paper supply the relevant inspectable statements. The source manifest identifies the inspected copies. This is not an exhaustive no-prior-art certification.

## Higher mixed control from Garner

Richard Garner, *Polycategories via pseudo-distributive laws*, https://arxiv.org/pdf/math/0606735v2, is a direct baseline, not merely a related application. **Definition 14 (printed pp. 11–12)** assumes a pseudomonad S and a pseudocomonad T on a bicategory B and a mixed pseudo-distributive law δ:TS⇒ST. It defines the two-sided Kleisli bicategory with hom categories B(TX,SY), identity η_X ε_X, and composite μ_Z Sg δ_Y Tf Δ_X. This already covers the generic higher-dimensional two-sided construction. The text explicitly omits the associativity and unit constraints, stating that they are constructed from the three supplied structures. Thus the construction is established source material but this paper is not a fully displayed proof of every generic constraint.

More significantly, the paper **derives a nontrivial mixed law**, rather than only assuming one. Proposition 12 (pp. 10–11) supplies a pseudomonad and pseudocomonad on Mod from the free symmetric strict monoidal construction. Section 3 uses double clubs: Proposition 16 gives an evaluation-at-1 equivalence for collections (under its completeness requirements; proof delegated to *Double clubs*, Proposition 30); Proposition 18 gives the compatible monoidal structure (again referring to the companion paper). Proposition 20 (pp. 19–20) constructs lifts by pullback and uses that source/target strictly create the relevant pullbacks. Fully faithful evaluation lifts the invertible comparison cells and reduces their axioms to the component at 1. Section 4 constructs that component using suitable matchings. **Proposition 38 and Corollary 39 (pp. 41–43)** check all ten mixed pseudo-distributivity coherence axioms: the projections of the relevant faces are local monomorphisms, so two special maps over the same projection coincide. Those proofs were inspected directly. Theorem 42 (p. 44) identifies polycategories with monads on discrete objects in the resulting two-sided Kleisli bicategory; Proposition 41 leaves some axiomatic equivalence checks as straightforward verification.

**Scope correction.** Neither “make the mixed construction bicategorical” nor “derive a law using suitable additional structure” in the abstract is a defensible new target. Garner supplies both higher packaging and a concrete structural derivation. A contextad-specific candidate would have to establish the common typed ambient and explain whether the required dependent crossing is obtained by an existing evaluation/collection/club argument, a factorization argument, or genuinely additional structure. The present audit has not instantiated those hypotheses for arbitrary contextad/contentad data, and does not claim impossibility of doing so. Contextads live in higher displayed-span machinery rather than automatically being endopseudomonads on a common bicategory. An identification theorem plus independently checkable sufficient hypotheses and a useful specialization could be substantive; merely assuming the mixed law and applying Definition 14 is not.

Proof coverage boundary: the companion *Double clubs* results referenced above were not independently re-proved or fully audited in this pass; their precise dependencies are recorded rather than represented as directly checked. No absence-of-literature novelty claim follows.

# Strong effect and factorization baselines for the contextad scope audit

Audit date: 1 November 2026. This is a targeted primary-proof inspection, not an exhaustive novelty review. The source manifest identifies the retrieved primary copies; inaccessible alternate endpoints did not prevent the stated proof inspections. No theorem of the proposed new workstream is proved here.

## Executive consequence

The first charter must distinguish three different ambitions:

1. Changing a typed pre/post-state index and selecting later commands from returned values.
2. Dependent types or contexts indexed by a realized value, retaining a dependent sum/joint execution witness.
3. Extending arbitrary dependent sections across a monad unit A -> T A, where a type can inspect the whole effectful value.

These are not interchangeable. Existing parameterised effects already cover much of (1). The finite history contextad covers an instance of (2). Vákár's dependent Kleisli theory studies (3), including precise failures and a concrete repair. A generic factorization crossing with coherence derived from uniqueness is also already an established construction. The new increment must be stated after these comparisons, not inferred from the phrase “result-dependent requirements.”

## A. Atkey: parameterised monads and Freyd categories

Primary: Robert Atkey, *Parameterised Notions of Computation*, JFP 19(3–4), 2009, 335–376. Author manuscript: https://bentnib.org/paramnotions-jfp.pdf . Locators below use its printed manuscript pagination.

Definition 1, pp.5–6, requires C with finite products, a category S, T:S^op × S × C -> C, dinatural unit and multiplication, and strength. Composition matches the intermediate state index. Proposition 1, p.15, constructs the parameterised Kleisli category with hom((A,S),(B,S'))=C(A,T(S,S',B)), and its parameterised adjunction. Proposition 2 identifies strength with the appropriate premonoidal structure; Proposition 3 supplies closure precisely with Kleisli exponentials. Theorem 1, p.16, concludes equivalence with closed parameterised Freyd categories. I read these constructions and proof paragraphs; their routine axiom verifications are explicitly abbreviated. Theorem 3, pp.30–31, gives inverse lifting constructions for state endofunctors and compatible transformations. Its proof identifies monad-multiplication compatibility with preservation of composition.

Application overlap is substantive: changing state types, session I/O, and monoidal framing of untouched resources are established examples, not new contextad capabilities. Theorem 2's syntax completeness proof refers back to the 2006 paper; I did not check that referred completeness proof and do not import it.

### Our scope inference

An arrow has a declared endpoint S', so simply showing that a command changes a capability/state type is insufficient as a new dependent mixed result. A next requirement genuinely varying with a returned value needs an explicitly indexed family or a sum/existential packaging; the charter must compare that encoding rather than declare it impossible in parameterised semantics. Conversely this paper does not itself exhibit the sought contextad/contentad interaction and its double-category cells. Any reduction to it must identify what data the reduction preserves and forgets.

## B. Vákár: dependent Kleisli extensions are extra structure

Primary: Matthijs Vákár, *In Search of Effectful Dependent Types*, 2017 thesis, https://www.cs.ox.ac.uk/people/aleks.kissinger/theses/vakar-thesis.pdf . Companion paper https://arxiv.org/abs/1603.04298 . The thesis is the stronger inspected source.

Theorem 5.2.9, p.204, constructs a dCBPV− model from an indexed monad on a pure dependent-type model using indexed Eilenberg–Moore algebras. The proof constructs algebra structures on dependent products; some algebra-axiom checks are left to the reader. Definition 5.3.2, p.210, adds dependent Kleisli extensions, with unitality, composition and agreement with ordinary extension. Remark 5.3.4 derives dependent costrength and pairings. These are additional conditions, not consequences of an arbitrary indexed monad.

Sections 5.3.3.1–3, pp.213–215, give explicit Fam(Set) writer, reader and global-state non-models. The writer predicate is inhabited only at the monoid unit, blocking a total extension. Page 214 gives a positive setoid model using a codiscrete monoid: dependent predicates cannot distinguish printed output, while judgemental distinctions may remain. I read these arguments and repair, not merely their abstracts. The full syntactic completeness chain in Theorem 5.3.5 was not reverified.

### Our scope inference and a checked finite diagnostic

The relevant extension crosses η:A -> T A. It is stronger than choosing a next context after observing a sampled a. For normalized finite distribution T on Set, unrestricted Fam(Set) dependent extension fails by the same pattern:

- Let A={0,1} and let B(t) be a singleton when t is Dirac and empty otherwise, for t in T A.
- The free computation family U F B has fibre T(B(t)). Along η all fibres are singletons, so a section exists.
- At t=(δ0+δ1)/2, the target fibre is T(empty)=empty, so no extended section can exist.

This is an elementary deduction from the displayed definition and free-algebra case (Remark 5.3.3), not a claim that the source states this probability example. It needs no disintegration and does not obstruct forward-sampling dependent sums or the ordinary finite history contextad. It is a warning against silently requiring global transport of arbitrary predicates over effectful values. An obstruction-plus-restricted-observations repair is already part of the established literature, so that shape alone is not a novel result.

## C. Rosebrugh–Wood: unique factorization already derives a crossing law

Primary: Robert Rosebrugh and R. J. Wood, *Distributive Laws and Factorization*, JPAA 175 (2002), 327–353. Author PDF: https://mta.ca/~rrosebru/articles/fac.pdf . Locators use its printed preprint pages.

Section 3.1, p.11, defines strict factorization by literal unique decomposition through two wide subcategories. Section 3.3 derives the ME -> EM crossing by refactorizing a composite; unit and multiplication equations follow from uniqueness. Theorem 3.8, p.13, reconstructs the original category by an identity-on-objects isomorphism. I read the constructions and proofs. Strict factorization is not the same definition as an ordinary orthogonal factorization system: the paper states this explicitly.

Sections 5.7–5.9, pp.25–26, treat classical factorization with chosen factorizations and laws relative to the isomorphism category, reconstructing after the appropriate quotient. These proofs were also read. Section 3.6 stops short of a full biequivalence on arrows and transformations; §5.11 identifies retained bicategorical span structure as requiring further analysis in that paper. Those limits are not evidence that later literature has left the problem open.

### Our scope inference

The proposed c∘r=r'∘c' crossing cannot count as new merely because factorization uniqueness proves its equations. A real increment would need the actual dependent display/codisplay typing, the retained cells, and their relation to the specified contextad/contentad construction. Merely assuming factorization systems with that structure already encoded would be circular. Classical uniqueness-up-to-isomorphism does not authorize a literal strict crossing without choices/quotients/coherence.

## D. Lack: PRO/PROP recognition and pullback/pushout laws

Primary: Stephen Lack, *Composing PROPs*, TAC 13(9), 2004, 147–163; journal currently supplies revised PDF dated 2021: https://tac.mta.ca/tac/volumes/13/9/13-09.pdf . Read §§3.7–3.10, 4.5–4.8, 5.3–5.4.

Theorem 3.8 characterizes composite PROs by strict monoidal subcategories with unique factorization. Theorem 4.6, p.157, treats PROP factorizations unique modulo permutations, assuming wide symmetry-containing tensor-closed subcategories. Its proof constructs the crossing, derives its equations from associativity, and obtains an isomorphism by existence/uniqueness of factorizations. Section 4.5 warns that component maps of a general composite need not be injective, so the subcategory case is restricted.

Section 5.3, pp.158–159, obtains a cospan-to-span distributive law by pullback pasting; §5.4, p.160, gives the pushout dual. The resulting categories identify isomorphic spans/cospans and discard 2-cells. These are explicit prior constructive compatibility results, not just “assume a law.” I read their derivations; I did not audit all later bialgebra presentation calculations.

### Our scope inference

A pullback/pushout or unique-normal-form entry criterion may still be an appropriate starting baseline. It is not by itself a scientific increment. The charter should show whether it adds dependence, preserves cells discarded by the existing classifying-category construction, or connects to contextads through a nontrivial representation theorem. “Derive coherence from universality” is a standard proof pattern, not a novelty claim.

## Recommended entries in the scoping ledger

- Already applicable: parameterised effects for changing typed state and local framing; strict normal-form crossing from unique factorization; PROP crossing from permutation-relative factorization; PB/PO law construction at the displayed quotient level.
- Applicable only after mapping hypotheses: dCBPV indexed models and dependent extension; any proposed contextad mapping to parameterised Freyd or factorization frameworks. State exact transport/cell conditions first.
- Not established by this audit: equivalence between dependent mixed contextads and dCBPV+, universal criterion for their compatibility, a new dependent double-factorization recognition theorem, or completeness of the novelty search.
- Do not count as a new outcome alone: a state-changing typed protocol, a global dependent-extension obstruction, an observation-restricting repair, or normal-form associativity from uniqueness.

For the charter's application tests, require an explicit row stating whether each example uses realized-value dependence, whole-effectful-value dependence, or only fixed pre/post indices. This prevents the examples from quietly requesting different theorems.

## E. Fong–Zanasi: linear relation/corelation positive controls

Primary: Brendan Fong and Fabio Zanasi, *Universal Constructions for (Co)Relations: categories, monoidal categories, and props*, extended paper https://arxiv.org/abs/1710.03894 . Read Assumption 1 and Theorem 3.1 (p.8), Corollary 3.4 and its proof (pp.10–11), §4.7 (pp.17–18), and the full Appendix A proof of Theorem 3.1. The extended text notes a correction to its conference version; do not substitute the older version's hypotheses.

Assumption 1 requires pullbacks and pushouts, a costable factorization (E,M) with M monic, and a pullback-stable subcategory A containing M whose pushout-of-pullback comparison for cospans lies in M. Theorem 3.1 exhibits Corel(C) as a Cat pushout of span/cospan categories. Appendix A derives the mediating functor by descending cospan representatives; uniqueness uses fullness and identity-on-objects of the quotient. Corollary 3.4 specializes to abelian C, giving Corel(C)≅Rel(C); its proof verifies the comparison hypotheses via kernels, cokernels and images. Section 4.7 covers linear relations and their relational composition.

Our scope inference: a vector-space positive model for the candidate normal forms must be compared to this known calculus, not counted as new simply because it closes under composition. The potentially substantive increment remains the precise contextad/contentad presentation and the cells or dependence that it preserves. A relation category with only isomorphism-class witnesses does not automatically provide the requested double-category comparison theorem.

Mal'cev/difunctionality was also located as a classical characterization in primary later papers and original-source references. The original characterization proof was not inspected in this pass, so it remains a follow-on comparison lead rather than an imported theorem here. No exact-Mal'cev generalization is claimed.

## F. Factorization recognition already retains double structure

Primary: Miloslav Štěpán, *Lax structures in 2-category theory*, doctoral thesis, https://arxiv.org/abs/2504.04467v1 (2025), Chapter 3. It incorporates the author's *Factorization systems and double categories*, TAC 41(18), 2024, 551–592. The journal PDF endpoint returned HTTP503; the complete thesis PDF was retrieved successfully, so proof access was not blocked.

Read Definition 3.2.8, §§3.3.1–2 definitions, Lemmas 3.3.3/6, Proposition 3.3.32, and full proofs of Theorems 3.3.7 and 3.3.33. Theorem 3.3.7 (pp.118–119) gives an equivalence between codomain-discrete double categories and strict factorization systems. Codomain-discrete means each top-right corner has a unique square filler (codomain functor discrete opfibration). Theorem 3.3.33 (pp.131–132) gives an equivalence between factorization double categories and orthogonal factorization systems. Definition 3.3.24 requires invariance, fillers for top-right corners with every square bicartesian, and joint monicity of bottom-left corners. These imply flatness. Morphisms are double functors versus factorization-preserving functors. The proofs construct natural isomorphisms, including reconstruction of squares; these are not only object correspondences.

### Scope consequence

The limits of Rosebrugh–Wood's 2002 discussion do NOT leave a generic “retain double-category cells” recognition problem untouched. This later theorem directly fills a substantial part of that space. A proposed increment must exhibit its precise contextad/contentad-dependent structure, prove how it relates to these classes, and identify a specific remaining comparison or a non-flat situation outside their hypotheses. Merely passing from categories to flat doubles, adding squares, or proving functorial reconstruction is not enough. No claim that all further relevant literature has been exhausted follows.

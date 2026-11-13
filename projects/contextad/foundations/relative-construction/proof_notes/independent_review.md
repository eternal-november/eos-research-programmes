# Independent construction review (1 November 2026)

Reviewed common_ambient.md, mixed_factory.md, instances.md and conservativity.md independently. No substantive blocker found in the core construction. This is a mathematical realization and mixed-normal-form construction, conditional on interaction data, not a claim that all effects interact automatically.

## Checked arguments

* Relative Cat-promonad realization retains hom categories and their noninvertible arrows. The reverse construction uses pure whiskering; monoid units recover the original actions up to coherent equivalence.
* Relative-quintet square orientation is correct. Forward bending by eta_u, alpha, epsilon_v has top J(v)F and bottom GJ(u). Inverse vertical pasting has the claimed boundaries. Companions suffice; conjoints are not needed.
* Pseudocoend/comma normalization works on all generators. Psi's three steps are well typed, Phi Psi is identity, and b_x gives Psi Phi -> identity. Naturality covers product arrows and balancing generators. This is special to these comma modules, not a general strict/pseudo-coend identification.
* Source endpoint change is related by b_eu(P); output transport commutes through the normal split. Lift composition plus balancing composition supplies global coherence.
* Covariant content Grothendieck construction and corepresentable Kleisli restriction are correctly typed. The 1-cell-opposite is necessary; hom arrows are not reversed.
* Marked generic-arrow recovery recovers supplied total categories and extension data; it is not intrinsic recovery from an unmarked bicategory.
* Unit maps into a nontrivial mixed composite need not be faithful. The inverse-amalgamation counterexample and distinction between faithfulness, fullness and local full faithfulness are correct.

## Required wording/source precision

1. For non-normal J, globular squares are canonically identified with B-cells using unitors, not literally those cells. Normalize or state the identification.
2. The full presheaf Kleisli constructor uses a 2-category as base. It fits the full Lawler ambient; restriction to representables returns the ordinary-pure-base relative object. Do not silently identify the full presheaf Kleisli bicategory with the representable part.
3. Comparisons defined here use pure-compatible icons. Retaining every native grade cell does not prove an unrestricted triequivalence of every possible higher morphism notion. Existing scope disclaimer is necessary.
4. Native weak coherent units/associators remain invertible; permitting noninvertible grade arrows does not cover arbitrary lax structural associators.

## Composite-pseudomonad primary source verified

Downloaded the primary TAC paper into sources/marmolejo1999.pdf and extracted its text. Francisco Marmolejo, 'Distributive laws for pseudomonads', TAC 5(5), 1999, pp91–147 (the abstract page inconsistently lists81–147).

Section4 p98: r:UD -> DU is an arbitrary1-cell in the hom2-category A(K,K), hence an arbitrary2-cell of the Gray-category. Only the four structural comparison2cells in that hom are required invertible. Section5 pp101–102 defines V=DU, unit 1 -> U -> DU and multiplication DUDU -> DDUU -> DDU -> DU, with explicit unit and associativity pastings. Theorem5.1 p102 states this is a pseudomonad; proof uses the distributive-law coherence diagrams. Introduction p92 explains passage from tricategories to Gray-categories by triequivalence. Therefore it applies to the Biprof construction after Gray replacement and transport; no invertibility of the crossing is required.

Inspection covered statement, definition, multiplication/pasting construction and proof mechanism, not a fresh verification of every diagram in the published proof. Gambino–Lobbia Def4.1 gives the modern arbitrary-Gray law formulation; its Thm4.5 is a lifting theorem, not the direct composite construction citation.

Kamiya archived source Construction3.1/Prop3.2 explicitly gives monoidal Grothendieck extension, coproduct preservation and pseudomonoids-to-pseudomonads before the comprehension-equivalence hypothesis begins in section3.2. Thus the broader use of Prop3.2 here is justified.

## Later comparison additions

Reviewed expanded common_ambient.md: varying-base (f,H,theta) strong comparisons, direct lax double comparisons, retained vertical transformations, and HistProb/FinStoch E/J example. The strong square conjugation is typed correctly. The direct lax definition correctly avoids inverting a noninvertible compositor. In the support sampler, y -> v(y) preserves measures exactly by the stochastic-square equation; pair -> final output is natural against arbitrary endpoint squares and associative by final-coordinate projection. The local adjunction E left adjoint J, EJ=identity, and noninvertibility example are valid. This expands comparison coverage without asserting a blanket higher equivalence. Distinguish the support-sampler symbol J from the pure-inclusion symbol in final notation.

## Final TeX pass

Reviewed delivery/One_relative_construction_for_context_content_and_effects.tex through its full sections1–11 and bibliography. Two additional scope corrections were requested and are now verified in the file: native marked recovery is one-sided/input-retained, not recovery from possibly nonfaithful mixed images; the bicyclic example refutes universal conservative amalgamation, not by itself existence of every possible nonconservative crossing. Exact opposite1-cell Lawler convention is now stated and no unqualified Kleisli universal property is imported through it. No substantive blocker remains at the paper's stated scope.

Also downloaded primary sources/lawler.pdf (arXiv1502.08017v1, Finn Lawler), SHA256 4c93fa6039f9b6fa7e65e081f158d593740f1fb3568d755ddefe62b9e21cead6, 793966bytes; accompanying text retained. This verifies author/title/version and supports the ambient/realization import. No fresh line-by-line formal verification of all cited foundational theorems is claimed.

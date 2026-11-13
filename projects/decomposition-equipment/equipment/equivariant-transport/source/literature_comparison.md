# D1 transport literature comparison

## Conclusion

D1 should be presented as a witness-sensitive application and compatibility theorem, not as a new free-operad, equivariant-quotient, or groupoid-coloring construction. The four primary sources below establish the relevant baseline. None is used as a substitute for proving transport on the particular occurrence-refinement categories required by D1.

Scope: the D1 contract in `../contract_revision_20261028/final_artifacts/Original_Completion_Contract_v0.1_VERBATIM.md`, lines 366–380. Sources checked on 2026-10-31. Page references below are printed PDF pages; versioned links avoid locator drift.

## Direct equivariant free and quotient baseline

Jonathan Rubin, *Combinatorial N∞ operads*, [arXiv:1705.03585v3](https://arxiv.org/pdf/1705.03585v3).

- Conventions, p. 5: finite discrete G; symmetric operads in a cartesian ambient category.
- §5.2, Definition 5.1 and Proposition 5.3, p. 20: congruence compatibility with G × Σ and substitution; quotient universal property.
- Definition 5.5, Corollary 5.6, and Proposition 5.8, pp. 21–22: generated congruence, universal factorization, and contextual equivariant closure.
- §5.4, Proposition 5.18, p. 24; §5.5, Proposition 5.20, p. 25: free-forgetful adjunctions.

These directly preclude novelty claims for free equivariant extension or invariant quotient descent. Rubin's external G-action and input Σ-action are separate. The cited theorem does not itself assert arbitrary multiobject interface-groupoid transport.

## Typed tree baseline

Clemens Berger and Ieke Moerdijk, *Resolution of coloured operads and rectification of homotopy algebras*, [arXiv:math/0512576v2](https://arxiv.org/pdf/math/0512576v2).

Section 1.6, p. 7, describes change of colors and the resulting fibered category over sets. Theorem 3.2, p. 10, supplies the free adjoint for pointed colored collections. The construction on pp. 10–11 uses edge-colored, vertex-labeled trees, with compatibility of labels and identifications for automorphisms and identities. Remark 1.4, p. 5, distinguishes nonsymmetric colored operads.

This is a standard typed free-tree baseline. A fixed set of colors alone supplies neither chosen actions on primitive witnesses nor D1's refinement-arrow transport.

## Multiobject coloring is also established

Dominik Trnka, *Category-colored Operads, Internal Operads, and Markl O-operads*, [arXiv:2304.02446v2](https://arxiv.org/pdf/2304.02446v2).

The introduction, p. 2, explicitly includes groupoids with arrows between different objects. Definition 1.1, p. 6, uses functors `(C^op)^n × C → V`. Proposition 5.6, p. 28, gives a free internal-operad adjunction. Example 5.7, pp. 28–29, specializes to category-colored operads in vector spaces and balances actions across an internal edge: action on one adjacent vertex is identified with action on the other. Section 6, Definitions 6.4–6.5, p. 31, treats operadic ideals and their generation.

Thus moving beyond a one-object group is not itself a novelty claim. However, this category-colored formalism is not automatically identical to an external diagram of whole signatures. A comparison requires an explicit encoding and verification of which actions and balancing identifications are intended. Its vector-space ideal construction should not be silently substituted for set-valued congruences.

## A similarly named but different equivariance notion

Alexander S. Corner and Nick Gurski, *Operads with general groups of equivariance, and some 2-categorical aspects of operads in Cat*, [arXiv:1312.5910v2](https://arxiv.org/html/1312.5910v2).

Definitions 1.10 and 1.14 concern an action operad: arity-indexed groups `G(n)` equipped with an operad map `G → Σ`, acting on the corresponding operation sets. This generalizes symmetric and braided input symmetries. Remark 1.18 packages the groups as a groupoid having no arrows between distinct natural numbers.

This is not a direct citation for arbitrary external interface changes. Such a change can preserve an ordered occurrence list while relabeling its interface data; an input permutation instead reindexes the list. If both are present, D1 must state their interaction rather than identify them.

## What D1 still needs to establish

The following are mathematical proof obligations inferred from the contract, not novelty assertions or claims that the sources lack more general results.

1. **Supply the action.** Specify a strict groupoid diagram of component and primitive-witness signatures, or give coherence isomorphisms with their axioms. An inventory of interface names is insufficient.
2. **Use the free universal property naturally.** For a strict signature diagram, applying the free construction to its arrows gives identity and composition laws. Prove that the resulting maps agree with the stated recursive transport, including all occurrence data.
3. **Distinguish two quotient questions.** An existing ordinary generated congruence descends only when it is preserved by transport. By contrast, generating an equivariant congruence from arbitrary relations forcibly adds transported relations and can produce a different quotient. A non-invariant presentation must not be called descended merely because this repair exists.
4. **Prove refinement functoriality on arrows.** Identify the entire occurrence-indexed refinement witness, transport every constituent, and check identities, composition, repeated occurrences, and compatibility with equations. Transport on objects or semantic composites alone does not prove this.
5. **State the information lost by quotienting.** Orbit sets and isomorphism classes are not groupoids of transport witnesses. For example, a one-object groupoid with nontrivial automorphism group has one isomorphism class but retains multiple distinct automorphisms.

Recommended report framing: “The free and presented transport mechanism is standard equivariant algebra. The result here supplies the chosen interface action and proves its compatibility with this calculus's retained witnesses and full occurrence-refinement structure.” This bounded comparison supports that attribution; it is not an exhaustive novelty search.

## Access note

The supplied NSF mirror `https://par.nsf.gov/servlets/purl/10393686` repeatedly timed out, and the TAC-hosted Trnka PDF returned HTTP 502. Both papers were successfully inspected through the author-submitted arXiv PDFs above. The NSF mirror and arXiv version have differing pagination, so the locators above deliberately refer only to the verified arXiv versions.

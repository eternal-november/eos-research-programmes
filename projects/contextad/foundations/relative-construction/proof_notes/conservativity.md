# Conservativity audit for a common context/content construction

1 November 2026. Independent proof audit. This note supplies a concrete obstruction and safe universal-property formulation; it does not assert a new general amalgamation theorem.

## 1. Three claims which must remain distinct

For one-sided horizontal bicategories M and N with specified identity-on-objects pure pseudofunctors J_M:C→M and J_N:C→N:

1. **Common ambient:** M and N are structured objects in one higher category. This need not identify any computations and is normally harmless.
2. **Common computation object:** a bicategory P with maps i_M:M→P and i_N:N→P and a specified coherent comparison i_M J_M≃i_N J_N. A universal such object is an amalgamation. This enables arbitrary alternating composites, not necessarily short mixed normal forms.
3. **Conservative mixed normal form:** a specified horizontal hom presentation, e.g. triples (P,Q,f:eP→dQ), with lawful composition and one-sided maps satisfying stated faithfulness/recovery properties. This needs a compatible crossing and separately checked recovery. Neither (1) nor (2) gives it automatically.

“Retains noninvertible cells” must distinguish including those cells as generators from proving they stay distinct and from proving no new cells appear between old arrows. In bicategorical terminology local faithfulness, local fullness, and reflection of equivalences are different claims. A locally fully faithful map retains each old hom category fully; merely having a retraction only ensures a weaker conclusion.

## 2. Explicit obstruction, even with faithful pure maps

Let C be the one-object category whose monoid is free on a. Put

    M = <a,b | ab=1>,    N = <a,c | ca=1>.

The maps C→M and C→N send a to a and are faithful. Indeed M has the transformation representation on natural numbers in which a(n)=max(n−1,0), b(n)=n+1 and multiplication is composition; powers of a are distinct. N has the representation a(n)=n+1, c(n)=max(n−1,0), again with distinct powers of a.

In M, ba≠1: in the displayed representation ba sends 0 to 1. In the pushout category P=M⊔_C N,

    c = c(ab) = (ca)b = b,
    ba = ca = 1.

Consequently M→P is not faithful. Symmetrically ac≠1 in N but ac=1 in P. The pushout is the infinite cyclic group: a becomes invertible and b=c=a⁻¹. This last identification is not needed for the obstruction but follows directly from its presentation.

Thus **faithful common-interface maps are insufficient for faithful amalgamation**. No alternative common category can preserve both sides faithfully while identifying the two copies of a and preserving their equations: the same two-line argument works in every target. This is a compatibility obstruction, not a defect in one pushout implementation.

The bicategorical version is just as relevant. Regard C,M,N as locally discrete bicategories. If their images agree on a up to a coherent invertible comparison, and all one-sided equations are preserved by pseudofunctors, the image of a has both a left inverse c and right inverse b up to invertible 2-cells. The ordinary uniqueness-of-inverse argument, with associators inserted, gives b≅c and ba≅1. But M(∗,∗), a discrete category, has no morphism ba→1. Hence the map from M into that common bicategory cannot be locally fully faithful. This argument does not claim failure of local faithfulness on 2-cells (which would be vacuous for a discrete hom); it disproves the stronger appropriate recovery claim.

This is an abstract counterexample to a generic common-base factory. It is not a claim that this specific pair is realized by the particular dependent contextad/contentad models under study.

## 3. Safe strict universal syntax

For small strict 2-categories M,N and strict 2-functors from a common strict 2-category C, their pushout in strict 2-Cat exists. A completely explicit presentation is:

- objects: the object pushout;
- generating 1-cells: those of M and N, identified on C;
- generating 2-cells: those of M and N, identified on C;
- 1-cell equations: each side's identity and composition equations;
- 2-cell equations: each side's vertical/horizontal composition and identity equations;
- close under whiskering, vertical/horizontal composition, and the strict 2-category axioms.

Smallness ensures these are set-sized term constructions and quotients in a larger fixed universe if necessary. Sending the generators into a strict 2-category X respecting the relations is exactly giving compatible strict 2-functors M→X and N→X. Therefore the presentation has the ordinary pushout universal property, without any embedding conclusion. This is already enough to see why formally adjoining alternating words cannot itself establish a conservative normal-form theorem.

One must not silently use this as a pushout for arbitrary pseudofunctors. Lack, *A 2-categories companion*, discusses precisely this distinction: strict 2-Cat has limits and colimits, whereas the ordinary category with pseudofunctors need not. Source: https://www.math.uchicago.edu/~may/IMA/Incoming/Lack/companion.pdf, early discussion of 2-functors versus pseudofunctors; §§4–5 discuss pseudo-morphism classifiers, co-isoinserters, and coequifiers as a way to encode weak structure using strict constructions.

For a weak relative construction, a safe route is a presentation with explicit invertible compositor/unit cells, explicit comparison cells between the two pure images, and all pseudofunctor/icon coherence equations. One must specify the mapping property (strict maps out classify what exact weak diagrams?) and the allowed transformations. Calling it a “bicategorical pushout” without stating whether cocones use icons, pseudonatural transformations, or strict agreement leaves the result underdetermined. Strictification of each side separately does not automatically strictify the shared-base diagram compatibly or preserve its claimed embedding properties.

## 4. What really suffices for recovery?

### Split recovery, weaker than full embedding

In the strict categorical case, suppose there is F:N→M with F J_N=J_M. By the pushout property there is r_M:P→M with r_M i_M=id_M and r_M i_N=F. Thus i_M is faithful and injective on objects; it reflects isomorphisms. Analogously, a map M→N over C gives a retraction of i_N.

For strict 2-categories, the same split retraction gives local faithfulness and reflection of invertibility of 2-cells. It does **not** imply local fullness: a retract inclusion can have additional target cells between its images. For bicategorical retractions up to equivalence, adjust conclusions to equivalence/reflection rather than literal injectivity.

### Full recovery

A locally fully faithful recovery statement needs a genuine hom-category normal-form theorem, or a separate argument that every ambient cell between old arrows comes from a unique old cell. Neither a word presentation nor a semantic evaluation supplies that by itself. A compatible semantic model in which a side maps faithfully proves faithfulness of the universal inclusion on whatever dimension the model is faithful; full faithfulness still requires fullness and a way to exclude cells invisible under evaluation.

### No unnecessary universal demand

The synthesis can retain M,N and their inclusions as structured input, while allowing the universal mixed output to lose recoverability. The precise theorem can say which comparisons preserve which data and can expose the failure as part of the construction. If the user's intent is a universally conservative merger, the counterexample proves that demand impossible at this generality. If the intent is a single relative factory with explicit compatibility/repair data, the obstruction is compatible with a useful positive answer.

## 5. Relative tensor, crossing, and universal words

A balanced tensor M⊗_C N is a space/category of length-two factorizations. It is not automatically closed under composition: multiplication encounters the middle N⊗_C M. A supplied distributive-law-type crossing into M⊗_C N, with unit/multiplication coherence, provides a normal-form composition. This is the standard role of the law, not an automatic consequence of the existence of the balanced tensor.

A free word object and a law-governed mixed object answer different questions:

- the free word object admits alternating words and preserves one-sided equations, subject to all consequences of sharing pure maps;
- the mixed object adds/evaluates a specified crossing and controls coherence of the resulting normalization;
- an evaluation from words to mixed forms is not generally faithful or an equivalence;
- even a coherent crossing does not, without checking the unit-induced one-sided inclusions, prove conservative recovery.

There is a further strict/pseudo distinction. An ordinary Cat-coend identifies balancing representatives by equality; a pseudo-coend adjoins coherent invertible balancing arrows. A locally proved strict comma/coend formula must not be relabelled a pseudo-coend equivalence without proof.

## 6. Application to the previously tested candidate

The finite epi/mono example already fails at the first relative descent step. If f is contentful, g pure, and h contextful, then

    [f;J_N(g),h] = [f,J_M(g);h]

in the ordinary balanced N⊗_C M. In the pseudo-balanced version these representatives must at least be related by a specified invertible balance. The proposed image/pushout crossing yields source domains {a0,a1} and {a1}. Those are not isomorphic over the source. Therefore it cannot define either the proposed strict balanced crossing or a pseudo crossing whose target preserves this domain distinction.

This is stronger than a nonassociativity check and weaker than a theorem that no compatible common construction exists. A free mixed syntax remains possible; an enlargement may also be possible, but cannot call the failed normalizer an equivalence or conservative reconstruction.

## 7. Recommended claim discipline for the unified construction

A strong, honest final result can have the following shape:

1. One explicitly defined relative ambient stores the pure base, one-sided actions, all hom categories, and endpoint-square data.
2. A specified universal assembly constructs alternating computations, with its exact weak/strict mapping property.
3. Law data internal to the same ambient construct mixed normal forms; the realization/evaluation comparison is defined on all cells.
4. Recovery hypotheses are stated and proved separately, and successful concrete examples satisfy them.
5. The inverse-amalgamation counterexample and the existing pure-balancing counterexample explain why universal conservative recovery and arbitrary automatic crossing are not promised.

This is one mathematical construction with controlled specializations and explicit failure modes, rather than a catalogue. The limitations are substantive compatibility constraints and should not be concealed in the word “embedding”.

## 8. Independent check of the new pseudo-coend bridge

The companion `mixed_factory.md` §§3–4 supplies the missing proof rather than making the prohibited strict/pseudo inference. I checked its presentation and inverse:

- The pseudobalancing generator b_u is invertible, while the original grade arrows α,β are not inverted.
- The normal split at eP defines Ψ on a square by output update β, balancing b_eα, then input update α.
- ΦΨ is identity. The arrow b_x:ΨΦ(t)→t is an invertible natural comparison.
- Naturality for balance generators is b_ux=b_u b_x; for product arrows it uses x=x'eα and balancing naturality. This covers the generators and hence all arrows.
- Endpoint changes use the actual cartesian/cocartesian lift maps, with source normalization comparison b_eu(P). The same balancing composition law checks iterated source changes; no coherent choice of representatives is being assumed.

Thus, in this specific comma-factorization case, the pseudo-coend is equivalent to the comma category. This does not identify arbitrary strict coends and pseudo-coends. The relative factory's remaining interaction is deliberately supplied as coherent law data, as it must be. When citing the composite theorem, use the appropriate tricategorical pseudomonad/pseudodistributive-law version for Biprof; a theorem stated only for monads in a 2-category would not by itself justify that step.

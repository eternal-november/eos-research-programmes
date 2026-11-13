# Restricted-incidence interface obstruction

Status: elementary proved obstruction, not a novelty claim. It concerns partial joint-context incidence and existentially pushed-forward observations in Set. It does **not** refute canonical factorization of a supplied total cylinder, free Isbell functoriality, or the existence of residual-profile quotients when the relevant complete domains and values are actually supplied.

## 1. Precise notion of a value-safe repair

Let P be preparations, T joint tests, A⊆P×T the admitted pairs, and e:A→K their outcomes. Here A is genuine operational admissibility, not merely the entries that happen to have been measured. Keep test names fixed for now.

An equivalence relation ≈ on P is **existentially value-safe** if

    p≈p' and (p,t),(p',t)∈A imply e(p,t)=e(p',t).

It produces a well-defined partial pairing on P/≈ and T, with ([p],t) admitted if SOME representative p'≈p has (p',t)∈A, and value given by any such representative. It does not assert that every representative admits that test. This distinction is exactly what later causes incompatible-witness composition.

A coarsest repair would be a greatest value-safe equivalence under inclusion. A minimum-cardinality repair instead minimizes the number of classes; these notions are different.

### Theorem 1: arbitrary graph coloring and failure of coarsest repair

Every finite simple graph G=(V,E) occurs as the conflict graph of a restricted-incidence pairing. Consequently value-safe preparation quotients are exactly the proper color-class partitions of G, and the least number of interface states is its chromatic number. A greatest value-safe equivalence need not exist; minimum-cardinality repairs need not be unique even up to relabeling of classes.

**Proof.** Set P=V, T=E and K={0,1}. For every edge t={u,v}, admit precisely (u,t) and (v,t), assigning them different outcomes, with an arbitrary chosen orientation determining 0 and 1. Two distinct vertices have a common admitted test with different values exactly when they are adjacent. Thus a partition is value-safe exactly when each block is an independent set. This is precisely a proper coloring modulo color renaming.

For the explicit four-preparation example take edges {a,b} and {c,d}. Assign a↦0,b↦1 at the first test and c↦0,d↦1 at the second. Both

    π₁ = {{a,c},{b,d}},     π₂ = {{a,d},{b,c}}

are safe and have the optimal two classes. Neither refines the other. Any equivalence containing both has a≈c≈b and hence merges the endpoints of the first edge; indeed its single block is all four vertices. It is unsafe. Therefore there is no greatest safe equivalence, and the two optimal partitions are genuinely different partitions of the labeled preparations. ∎

Allowing a test quotient does not remove this obstruction: merging tests cannot make two unequal values at the SAME original test become equal. Hence the two safe pairs (π₁,id_T),(π₂,id_T) still have no common safe upper bound in the product order on preparation/test equivalences.

This theorem is not about ordinary total Chu spaces. If every pair is admitted, safety simply says that only identical rows may merge, giving a unique greatest equivalence. The restricted-domain quantifier is essential.

## 2. What additional information restores uniqueness?

Call a quotient **domain-exact** when

    p≈p' ⇒ [(p,t)∈A iff (p',t)∈A]  for every t,

as well as value-safe. Define the partial residual profile

    ρ(p)(t) = e(p,t) if (p,t)∈A, and ⊥ otherwise,

where ⊥ is a distinct symbol for actual inadmissibility.

### Theorem 2: unique domain-exact residual quotient

The kernel of ρ is the greatest domain-exact value-safe equivalence. Every domain-exact value-safe quotient q:P→Q admits a unique surjection Q→im(ρ) satisfying ρ=(Q→im(ρ))q.

**Proof.** Equality of profiles entails equal domains and equal values. Conversely those two conditions entail equality of profiles. Hence any admissible equivalence is contained in ker(ρ). Define Q→im(ρ) by [p]↦ρ(p); this is well-defined, surjective and uniquely determined since q is surjective. ∎

This is a useful exact specification, not a construction from the original local middles. It demands the domain and value residuals for the declared joint tests. In the graph construction with a complete graph on n≥3 vertices, all profiles are different, so the unique domain-exact repair has n states. There is no cardinal bound in terms of a local observational middle alone: add one local test with the same value on every preparation, so the image of the local observation map is a singleton for every n, while the declared joint tests force n states. This is a statement about ordinary observational/image realization, **not** about free Isbell reconstruction, which may retain preparation-presentation data even when scalar observations coincide.

Domain-exactness may be stronger than the user's mission. If contexts only require existence of an admissible representative, it is not legitimate to impose domain-exactness just to manufacture uniqueness. The first theorem then remains the correct obstruction: optimizing the interface has genuine choices and no universal coarsest answer.

### Unknown is not inadmissible

If A is a measured ledger rather than a genuine admissibility relation, replacing missing entries by ⊥ is not sound. Equality of two unknown placeholders does not certify equality of the two actual outcomes. One must either acquire the necessary evaluations, derive them from independently justified semantic equations, or retain constraints/possible completions. The coloring theorem can still describe consistency with observed entries, but then 'safe' means consistent with SOME completion, not observationally adequate for the actual completion or ALL compatible completions.

For instance, two preparations with no measured tests are compatible with identifying them, but are also compatible with a future test separating them. A canonical partial-record quotient cannot resolve this missing semantic information.

## 3. Exact witness obstruction at a relational cut

Let q:X→Q be surjective, R⊆U×X and S⊆X×V. Write

    R̄={(u,qx):(u,x)∈R},    S̄={(qx,v):(x,v)∈S}.

Then always

    S∘R ⊆ S̄∘R̄.

The right side contains (u,v) iff there exist x,y with u R x, qx=qy and y S v; the left side requires one z with u R z and z S v.

### Theorem 3: exact cut criterion

Equality holds exactly when every such pair of endpoint-compatible witnesses x,y can be replaced by a common witness z with the same external endpoints. Equality holds for ALL R,S and all U,V exactly when q is injective.

**Proof.** The first assertion is the two membership formulas. If q is injective, qx=qy implies x=y and supplies z=x. Conversely, for distinct x,y with qx=qy, take U=V={*}, R={(*,x)}, S={(y,*)}. The actual composite is empty and the quotient composite is {(*,*)}. ∎

Thus a universal indiscriminate relation supplies at most a lax overapproximation, not observation preservation. In Boolean existence semantics the error already changes false to true. Keeping raw witnesses through the cut restores equality, but that is a diagnostic explanation of the missing information, not a compressed reconstruction theorem. A usable compressed solution must establish the displayed endpoint amalgamation property for its actual admitted cuts, or supply quantitative bounds for the spurious witnesses.

For functional wires w:X→Y and v:Y→Z, with surjections qX,qY,qZ and Rw=qY·graph(w)·qXᵒᵖ, there is a weaker endpoint criterion:

    Rv∘Rw = R(vw)

iff for all x∈X,y∈Y with qY(y)=qY(wx), there exists x'∈X such that

    qX(x')=qX(x),    qZ(vwx')=qZ(vy).

Indeed the left side is represented by x,y and the right by x'; this proves both directions. This need not require v itself to descend through qY: some alternative input witness x' in the same external class may repair the cut. It therefore avoids replacing the desired contextual comparison with unnecessarily strong global congruence.

## 4. Quantitative rather than exact amalgamation

Suppose a suffix v:Y→Z has a test pullback v*:TZ→TY and cut residual at most ε:

    |EZ(vy,t)−EY(y,v*t)|≤ε,

or the same inequality in a metric outcome space. Define row pseudometrics using the displayed test domains. If every qY-fiber has diameter ≤δ in the Y row pseudometric, then qY(y)=qY(wx) implies

    dZ(vy,vwx) ≤ δ+2ε.

**Proof.** For each final test t, insert EY(y,v*t) and EY(wx,v*t) between the endpoint evaluations, apply triangle inequality, and then take the supremum. ∎

Thus every endpoint produced by the quotient relational cut has a genuine directly composed endpoint within δ+2ε, witnessed by the SAME initial x. This is a one-sided Hausdorff/coverage estimate, not exact equality of relations. To state it on quotient Z, require the Z quotient to identify only zero-row-distance preparations, or explicitly retain representative-valued observation profiles; an arbitrary quotient does not automatically inherit this metric.

For final tests of budget b and suffix cost c, δ must be certified using intermediate tests of budget b+c, with preparation ranges enlarged as needed. An old local fiber diameter over tests of budget b gives no such conclusion. For an exact syntactic cut, ε=0 and the defect bound is δ. This isolates a checkable numerical missing obligation instead of assuming full contextual adequacy.

## 5. Scope and consequence

1. **Formal:** the known free Isbell product/wiring construction is unaffected.
2. **Semantic:** actual joint incidence, values, and common-witness/amalgamation information can distinguish objects whose local observation middles coincide. A finite interface declaration consisting only of operation names does not provide those semantics.
3. **Representation/admissibility:** exact partial profiles are legitimate Set-valued semantic records, but neither this fact nor existential quotient consistency proves representability in a positive/physical category.
4. **Resources:** no uniform interface-size bound follows from local middle size. A complete graph forces n states while the local observational middle is one state. No claim is made that supplying all residual profiles is an efficient solution; constructing or compressing them requires additional proved structure.

The constructive next question is consequently narrow: for the actual declared joint contexts, can their incidence and witness-amalgamation constraints be derived from a compact independently verified interaction law? The theorems identify exactly what that law must settle. They do not substitute global contextual completeness, a raw truth table, or a preservation axiom for that work.

## Appendix: independent audit of the mixed-corner CFS comparison

Let one supplied joint cylinder have nested preparation subdiagrams P⊆P'⊆P'' and nested test subdiagrams T⊆T'⊆T''. Fix canonical CFS factorizations R(P,T) for every displayed rectangle. Then grid maps

    R(P₁,T₂) → R(P₂,T₁)    (P₁⊆P₂, T₁⊆T₂)

exist uniquely: use the full E-cocone of the source, the full M-cone of the target, and the restricted preparation/test legs to make the orthogonality square. No restriction-stability axiom on either cone class is needed. Grid maps commute because both composites solve the same full-source-E/full-target-M lifting problem.

The mixed-corner span for a nested rectangle inclusion is

    R(P,T) ← R(P,T') → R(P',T').

Its left leg is in E₀ and its right leg in M₀, the opposite orientation from the earlier honest-realization (M₀,E₀)-span. For the first claim, a lifting problem against an M₀-arrow can first be solved using the target's E preparation cocone; equality on the source follows using its E preparation cocone and uniqueness. Dually the second claim follows using the common M test cones. In Set these legs are respectively a surjection and an injection.

Assume the relevant pullbacks exist in C. The grid maps give a canonical apex map

    R(P,T'') → R(P,T') ×_{R(P',T')} R(P',T'').

Hence the direct span maps TO the composite span. With the conventional apex-map 2-cells in Span(C), this is an **oplax** compositor. Associativity follows because the two maps to the threefold pullback have the same three components by grid commutativity; unit laws follow by the same universal property. Working in all Span(C) needs only the relevant pullbacks. Restricting to the (E₀-left,M₀-right) subclass additionally requires E₀ pullback stability for closure under composition; do not infer that stability from arbitrary CFS axioms.

A completely supplied finite Set example shows that this compositor is not generally invertible. Take preparations a,b and tests c,d with c(a)=c(b)=0, d(a)=0,d(b)=1. Preparation objects are singletons and test codomains are {0,1}. Set

    P₀={a}, P₁=P₂={a,b};  T₀=T₁={c}, T₂={c,d}.

In the jointly-surjective/jointly-injective Set CFS, R(P₀,T₀)=R(P₁,T₁)=1 and R(P₂,T₂)=2. The direct mixed apex R(P₀,T₂) is 1, whereas the composed apex is

    R(P₀,T₁) ×_{R(P₁,T₁)} R(P₁,T₂) = 1×₁2 = 2.

The compositor includes the a-profile and omits the b-profile. The composite span introduces b by changing representative at the intermediate constant-test class; the direct span cannot do so. There are no missing observations, partial admissibility, or unproved preservation assumptions in this example.

This is a genuine CFS-derived controlled comparison for nested restrictions/enlargements of ONE supplied joint cylinder. It does not construct that cylinder from local middles, determine its observations, or model arbitrary physical gluing/feedback without further semantic data.

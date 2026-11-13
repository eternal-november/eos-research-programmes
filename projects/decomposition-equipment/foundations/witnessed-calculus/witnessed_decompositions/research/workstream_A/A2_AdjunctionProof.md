# A2: signature category, free functor, naturality, and adjunction

Date: 24 October 2026 UTC. Author submission, not acceptance. Contract: `research/CompletionContract.md`, v0.1-proposed, SHA256 `47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e`. The A2 exact-target pre-attempt PASS at 18:10 UTC applies. This note supplements the already checked arbitrary-target extension in `WitnessedDecompositions/FreeExtension.lean`; it does not replace that theorem by a structural-fold assumption.

## 1. Scope and theorem

Fix an arbitrary type of interfaces V : Type u and arbitrary Quiver.{v} V. A component c retains its source, target, and actual edge. A profile at c is the complete ordered path from c.source to c.target. No finiteness, decidable equality, inhabitation, injectivity, or reconstructivity hypothesis is imposed on the base, signatures, or targets.

For every profiled generating collection C with operations in Type w and every strict calculus M with operations in independently chosen Type z, there is an explicit bijection

  Hom_Calc(F C, M) ≃ Hom_Collection(C, U M).

The bijection is natural in C and M, including maps between different operation universes. F preserves identity and composition, and the unit/counit satisfy both triangular identities. At a fixed common operation universe max u v w, these data form actual Lean `CategoryTheory.Functor` values and an actual `CategoryTheory.Adjunction`. The common-universe category packaging is not a restriction on the preceding cross-universe theorem.

The collection convention is equivalent to the original raw `Signature`, and F applied to the collection associated with S is explicitly strictly isomorphic to the original `Tree.freeCalc S`. Thus every original frozen signature, with every parallel primitive retained, is covered. Nullary profiles remain enabled; positive profiles remain positive because the whole input path is preserved.

## 2. Exact signature category and raw-signature comparison

A profiled collection C consists of types C.Op(c) and a map profile_C : C.Op(c) → Path(c.source,c.target). Its fibre at (c,p) is the subtype of a with profile_C(a)=p. A morphism h:C→D is a component-indexed function with profile_D(h(a))=profile_C(a). Identity and composition are ordinary identity and composite functions. Profile preservation for composition is the transitive composite of the two preservation equalities. Both unit laws and associativity are function equality; proof irrelevance identifies only the preservation proofs, not operations. This is the existing `Collection` category.

For a collection C, let L(C) be the raw signature with generators Σ c, C.Op(c), output c, and input profile_C(a). For an original raw signature S, let R(S).Op(c) consist of pairs (g,h) with g:S.Generator and h:S.result(g)=c. Its profile is S.input(g) transported along h. The following are exact inverse correspondences, not a quotient:

- S.Generator → L(R(S)).Generator sends g to (S.result(g),(g,refl)). The inverse forgets the component/equality fields and returns g. The first inverse law is reflexivity. For (c,(g,h)), equality induction on h makes the second inverse law reflexivity. The output and full profile are preserved in both directions, using exactly h in the backwards direction.
- C → R(L(C)) sends a:C.Op(c) to ((c,a),refl). Its inverse sends ((d,a),h:d=c) to transport_C.Op(h,a). The first composite is identity by reflexivity. For the other composite, equality induction on h again reduces it to reflexivity. The same induction proves profile preservation.

These are checked as `Signature.totalizedGeneratorEquiv` and its output/profile lemmas, and `Collection.toSignatureCollection`, `fromSignatureCollection`, `to_from_signatureCollection`, and `from_to_signatureCollection`.

For complete agreement on maps, a raw signature map S→T means an ordinary function f:S.Generator→T.Generator equipped with

  r_g : T.result(f(g)) = S.result(g),
  transport_Path(r_g,T.input(f(g))) = S.input(g).

Its map R(S)→R(T) sends (g,h) to (f(g),r_g.trans(h)). Preservation of the transported profile follows by induction on h from the displayed input law. Conversely, a collection map R(S)→R(T), applied to (g,refl), gives f(g) and r_g, and its profile law gives the displayed input law. These constructions are inverse: one direction is reflexivity on g; the other follows by induction on h. The Lean declarations `Signature.Hom.generatorMap`, `result_map`, `input_map`, `ofGeneratorMap`, and their two inverse lemmas prove precisely this claim. `Signature.Hom` is defined using these equivalent fibre maps, and an actual category instance is supplied.

For completeness, L acts on collection maps by (c,a)↦(c,h(a)); R acts on raw maps by the formula above. These formulas preserve identities and composition by function application and transitivity of equality. The displayed comparison isomorphisms are natural: on an original g, either composite returns the same mapped g; on ((d,a),h), induction on h reduces either composite to h(a) in the required component. Thus the change of signature convention is a category equivalence at any common universe containing the base. The low-universe data comparisons and Hom constructions themselves do not require a common operation universe.

## 3. The explicit hom-set bijection

Write F(C)=Tree.freeCalc(L(C)) and U(M)=M.toCollection. A map a:C→U(M) gives a raw primitive assignment A(c,x)=(a(x),profile_a(x)) in the prescribed operation fibre M.Operation(c,profile_C(x)). Conversely, an assignment A gives the collection map x↦A(c,x).val. The inverse laws hold componentwise by subtype extensionality. This is `Free.assignmentEquiv`, with independent universes w and z.

The existing `Tree.extend` sends an identity edge to M.identity and sends a node to the target substitution of the assigned primitive by the recursively interpreted children. Its full profile-slot and independently prescribed-fibre substitution preservation have already been proved from the target calculus laws. It is a genuine strict morphism, and its uniqueness theorem ranges over every strict morphism, not only maps satisfying a stipulated recursion.

Define E(a)=Tree.extend(A), and define R(f)(x)=f(corolla(c,x)). The existing corolla computation gives R(E(a))=a. Conversely, the existing strict-morphism uniqueness proof gives E(R(f))=f for every f:F(C)→M. The composite of these explicit equivalences is `Free.homEquiv`; the named inverse laws are `Free.restrict_extend` and `Free.extend_restrict`. In particular, if R(f)=a, then applying E gives f=E(a), proved as `Free.extend_unique`. No field in C, M, F(C), or a assumes this universal property.

## 4. Functor and both naturality laws

Use ordinary composition notation, with g∘f meaning first f, then g. Define η_C(x)=corolla(c,x). Thus R(f)=U(f)∘η_C. For h:C→D define

  F(h)=E(η_D∘h).

Its restriction is η_D∘h by the inverse law. For a strict target map k:M→N, direct evaluation on each primitive gives

  R(k∘f)=U(k)∘R(f).                                      (1)

For a source map h:C→D and f:F(D)→M, combine this direct computation with R(F(h))=η_D∘h:

  R(f∘F(h)) = U(f)∘R(F(h))
              = U(f)∘η_D∘h
              = R(f)∘h.                                 (2)

These are `Free.restrict_comp` and `Free.restrict_natural_source`. Applying the uniqueness of extension to (1) and (2), respectively, proves

  k∘E(a)=E(U(k)∘a),
  E(a)∘F(h)=E(a∘h).

They are `extend_natural_target` and `extend_natural_source`. Combining them proves the full two-variable equation `extend_natural`:

  k∘E(a)∘F(h)=E(U(k)∘a∘h).

Every displayed map retains its full typed profile; no comparison uses equality of arities alone.

The restrictions of F(id_C) and id_F(C) are both η_C, so uniqueness proves F(id_C)=id_F(C). For h:C→D and j:D→E, (2) gives

  R(F(j)∘F(h))=R(F(j))∘h=η_E∘j∘h=R(F(j∘h)).

Injectivity of restriction proves the composition law. These are `Free.map_id` and `Free.map_comp`. U preserves identity/composition literally by forgetting the two strict preservation fields. These laws construct the actual `Free.functor` and `Free.forgetFunctor` at operation universe max u v w.

## 5. Unit, counit, and triangular identities

Define ε_M=E(id_U(M)):F(U(M))→M. This evaluates a primitive named by a target operation to that very operation. From R(F(h))=η_D∘h we get U(F(h))∘η_C=η_D∘h, proving η natural. For k:M→N, source naturality applied to id_U(N) and target naturality applied to id_U(M) both identify the respective sides with E(U(k)):

  ε_N∘F(U(k))=E(U(k))=k∘ε_M.

This proves ε natural, with no assumed coherence.

The second triangle is the first hom-set inverse law applied to id_U(M):

  U(ε_M)∘η_U(M)=R(E(id_U(M)))=id_U(M).

For the first triangle, source naturality identifies ε_F(C)∘F(η_C) with E(η_C). The identity strict map of F(C) has restriction η_C. Uniqueness therefore gives

  ε_F(C)∘F(η_C)=E(η_C)=id_F(C).

The checked declarations are `unit_natural`, `counit_natural`, `triangle_forget`, and `triangle_free`. They directly populate the unit-counit constructor of the actual `Free.adjunction`; no abstract existence theorem or choice of adjoint is used. Its induced forward hom map is definitionally the explicit restriction, and its inverse equals E by source naturality and the right identity law. These identifications are checked as `adjunction_homEquiv_apply` and `adjunction_homEquiv_symm_apply`.

## 6. Compatibility with the actual original free calculus

For each original S define i_S:Tree.freeCalc(S)→F(R(S)) by sending g to the corolla named by (S.result(g),(g,refl)) and extending. Define j_S:F(R(S))→Tree.freeCalc(S) by sending (g,h) to the original corolla of g transported along h and extending. The first composite j_S∘i_S restricts to the original corolla at every g, hence equals identity by the original strict uniqueness theorem. For the other composite, inspect an arbitrary generator (g,h) of R(S), induct on h, and use corolla evaluation; its restriction is η_R(S), hence it is identity by the profiled-collection uniqueness theorem. These inverse strict equalities are `rawToProfiled_profiledToRaw` and `profiledToRaw_rawToProfiled`.

This also supplies explicit categorical packaging entirely in the original raw convention if desired. Let G(S)=Tree.freeCalc(S), and for a raw map s:S→T define

  G(s)=j_T∘F(R(s))∘i_S.

The identity law cancels j_S∘i_S. For composable s,t, cancel i_T∘j_T between the middle factors and use the already proved F composition law. Hence G is a functor. Its value on a primitive g is the corolla of s(g), with exactly the output/profile transports stipulated by s: i first retags g, F(R(s)) sends it to the retagged s(g), and j removes the tags. Consequently the transported naturality squares above are the ordinary raw generator-map squares, not new morphisms.

The raw forgetful functor is U_raw(M)=L(U(M)): its generators are (c,m), with their existing profiles, and U_raw(k)(c,m)=(c,k(m)). A raw map S→U_raw(M) is exactly a primitive assignment: send g to (S.result(g),a(g).val); in reverse, transport its chosen target operation along its recorded output equality and use its input-preservation equality to put it in M.Operation(S.result(g),S.input(g)). The inverse laws are equality induction followed by subtype equality. Composing with the original Tree hom equivalence gives Hom(G(S),M)≃Hom_raw(S,U_raw(M)). Naturality in s follows by evaluating the two sides at g, where both are the image of the corolla of s(g); target naturality follows by applying k to that same image. The raw unit names the original corollas and the raw counit evaluates primitives named by operations. Their second triangle holds on every operation by corolla evaluation; their first holds on every generator by that computation and hence on every free operation by strict uniqueness. This proves the same adjunction without narrowing the raw signature class.

## 7. Checked artifacts, trust, and remaining program obligations

Candidate: `FreeAdjunctionCandidate.lean` (427 lines), SHA256 `051c84272302d8650e774e07a548054c871745cddad723c29faa09fb3c3c3e0b`.
Stable snapshot: `FreeAdjunctionStable.lean`, same hash. No source modules or ledger were modified by this task. The integration owner controls integration and review status.

Reproduction:

  source ./env.sh
  lake env lean FreeAdjunctionCandidate.lean
  lake env lean logs/FreeAdjunctionAxiomAudit.lean
  lake env lean logs/FreeAdjunctionPrint.lean

Compiler: Lean 4.35.0, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc. The candidate and axiom audit compile successfully. `logs/FreeAdjunctionAxiomAudit.log` records the exact dependency closures. There are no placeholders, custom axioms, native_decide, or arbitrary leaf atom parameters.

Every substantive new universal-property, naturality, functor-law, triangle, and raw-comparison theorem has closure contained in [propext, Quot.sound]. `Collection.signature` and `Signature.totalizedGeneratorEquiv` need no axioms. The actual optional mathlib `CategoryTheory.Adjunction` packaging and its two comparison lemmas additionally depend on standard Classical.choice. This is not hidden: `CategoryTheory.Adjunction.mk` already has that closure because its unit/counit types involve mathlib's `CategoryTheory.Functor.comp`; that existing definition's generated map-identity/map-composition proof fields have Classical.choice in their closure. `logs/FreeAdjunctionPrint.log` prints that chain. The separately named naturality/triangle laws and explicit hom equivalence do not acquire that dependency. The constructor is populated directly, avoiding any selection of an adjoint or inverse function.

Direct project sources at this check:

- Core.lean: 465bf2bb96e3ab16a473c466f471eb48f2a8d1188635179c29d98076410b4b7d
- Collections.lean: c15a31f877b952dce29ae9e03d5ac8323eb3ed17a53bf161ff2873179cfa6004
- Calculus.lean: 7f47c010035f6676aab3ab782b0446c2d93509e41a76ac23fda09454fedfcf5c
- FreeCalculus.lean: 294ab03493698787c35cfc104b6b6c79748c61a32e2440c55ce9e7fadfefe16e
- FreeExtension.lean: ae5991a75daa8e0ded0e796811223823837c3d5cd482475559e085f88f85c543
- TreeOccurrences.lean: bf0e5d53cb4a09072b2921d584315d2ba9e0e5eae61881896a183fe650cf85b1

This completes the assigned categorical packaging proof as author-local L/P evidence. It does not independently certify A1, the remaining A2 target-model/negative-assignment tests, or scientific acceptance. The nontrivial relational/graph-cut target and two distinct primitive assignments are separate integration obligations; no terminal or syntax-only model is substituted here. The result is the expected free path-profile nonsymmetric multicategory infrastructure, not a claim of a novel mathematical mechanism.

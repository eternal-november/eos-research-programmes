# Collage gluing and free-CFS reconstruction: an exact completed cut law

Status: derived theorem for small Set-enriched distributors and declared serial cuts. It proves a specified **CFS-completed gluing** law, not that forgetting the completion gives physical gluing, and not a compression theorem. All primitive incidence and common-interface identifications are retained. No claim of novelty.

## 1. Setup and statement

Let A,B,C be small categories and

    P:A^op×B→Set,       Q:B^op×C→Set.

Write L=Coll(P), R=Coll(Q). Our collage convention has objects the disjoint union of its two boundaries, their original within-boundary homs, cross homs L(a,b)=P(a,b), and no reverse cross homs. Relabel the two copies of B identically. Let

    D = L ⊔_B R.

Let F:CAT→CFS denote Garner's free-cylinder-factorization pseudofunctor, with underlying category F(K)=I(K); this distinguishes the free functor from the underlying Isbell pseudomonad. The theorem is:

1. D is both the ordinary CAT pushout and a **bipushout** of the collage span.
2. Its external homs are

       D(a,c) = ∫^{b∈B} P(a,b)×Q(b,c).

3. F(D), with its induced legs, is a bipushout in CFS:

       F(L) ⊔^bi_{F(B)} F(R)  ≃  F(D).                 (1)

4. Every small actual cylinder in either collage, or in the external collage of Q∘P, has its canonical free-CFS factorization transported into F(D) by the corresponding CFS map. There is additionally an explicit connector-factorization law for compatible local cylinders, proved in §5.

Equation (1) specifies the completion in “reconstruction commutes with completed gluing.” It is not an assertion that the underlying categories I(L) and I(R) have ordinary pushout I(D).

## 2. Actual gluing, including the ordinary-versus-bi distinction

Construct D explicitly. Its objects are A⊔B⊔C; its within-layer homs are those of A,B,C; homs A→B are P, homs B→C are Q; homs A→C are the displayed coend; all reverse-layer homs are empty. Compose p∈P(a,b) and q∈Q(b,c) to [p,q]. The coend relation is generated, for f:b→b', by

    [P(a,f)p,q] = [p,Q(f,c)q].

Boundary actions give the remaining compositions. Their compatibility and associativity are precisely the functoriality and commuting actions of P,Q plus this relation. All homs are sets since the categories are small.

For functors H_L:L→X and H_R:R→X agreeing strictly on B, there is a unique extension H:D→X: its value on [p,q] is H_R(q)H_L(p). This is well-defined by the balance relation. Natural transformations agreeing on B extend uniquely too: naturality on A→C follows by composition from naturality on P and Q. Thus there is an isomorphism of categories

    CAT(D,X) ≅ CAT(L,X) ×_{CAT(B,X)} CAT(R,X).          (2)

A strict pushout is not automatically a bipushout. Here the special inclusions prove that it is. Given a pseudococone (H_L,H_R,gamma), where

    gamma:H_L|B ⇒ H_R|B

is invertible, define H_R' on B-objects to be H_L and on C-objects to be H_R. Set t_b=gamma_b and t_c=id, and on every R-arrow f:x→y define

    H_R'(f)=t_y^{-1} H_R(f) t_x.

Naturality of gamma implies H_R'|B=H_L|B exactly. The maps t form an isomorphism H_R'⇒H_R; hence the new strict cocone is isomorphic to the original pseudococone. The inclusion of strict cocones into pseudococones is fully faithful: between identity-matching cocones, the pseudococone morphism condition is precisely agreement of the two natural transformations on B. Therefore the strict pullback in (2) is equivalent to the isocomma/pseudopullback. This proves the bipushout property, naturally in X, without assuming arbitrary CAT pushouts are bipushouts.

The construction uses a literal common interface and full, object-injective collage boundary inclusions. More general identifications require their own bicolimit verification.

## 3. Why completion preserves this gluing — the actual hom proof

The only imported CFS result is Garner, *The Isbell monad*, Definition 2.5 and Theorem 3.3: CFS has E/M-preserving functors and all natural transformations, and restriction along Yoneda gives an equivalence

    CFS(F(K),X) ≃ CAT(K,U(X)),                         (3)

pseudonatural in K and X. See [primary PDF, pp. 7 and 11–13](https://arxiv.org/pdf/1410.7108). This is the free-CFS biadjunction, not a quantaloid fixed-point theorem.

For any CFS X, combine (2), its proved pseudopullback version, and (3):

    CFS(F(D),X)
      ≃ CAT(D,U(X))
      ≃ CAT(L,U(X)) ×^iso_{CAT(B,U(X))} CAT(R,U(X))
      ≃ CFS(F(L),X) ×^iso_{CFS(F(B),X)} CFS(F(R),X).

The last equivalence uses the pseudonaturality of (3), including the boundary restriction comparison isomorphisms. This is exactly the defining hom-category equivalence for a bipushout in CFS. It exhibits F(D) as that bipushout, so no separate general existence assumption for CFS bicolimits is needed. Choices yield equivalent bipushouts with their specified cocones.

This is stronger than merely saying a left biadjoint preserves bicolimits: both the source bicolimit and the hom-level transport have been supplied. It is weaker than asserting the forgetful functor U preserves this bicolimit; nothing here implies that.

## 4. External restriction: comparison, not an unjustified equivalence

Let E=Coll(Q∘P). The explicit D has a fully faithful inclusion

    k:E→D

onto its A,C objects. It follows that F(k):F(E)→F(D) is an available CFS morphism. **It does not follow that F(E)≃F(D).** D retains the internal interface, and free completion is not an operation of discarding it. Even A=C=empty and B a two-object discrete category gives E=empty and D=B: I(empty) has one object, while I(B) contains two nonisomorphic fully faithfully Yoneda-embedded objects with no arrows between them, so cannot be equivalent to I(empty).

No preservation-of-full-subcategories assertion is required. For an actual small cylinder r:D_0⇒T_0 in E, choose its canonical factorization in F(E), with middle R_E(r). Applying F(k) gives an E/M-factorization of the image cylinder in F(D), using the pseudonatural Yoneda comparison. Uniqueness of factorization therefore gives the leg-compatible isomorphism

    F(k)(R_E(r)) ≅ R_D(k r).                           (4)

Exactly the same argument applies to the collage inclusion maps L→D and R→D. Thus boundary reconstruction has a rigorous comparison into the completed gluing even though the entire boundary-only completion is not identified with it.

An actual cylinder means chosen, natural arrows for every declared preparation/test pair. A distributor supplies hom-sets of possible witnesses, not automatically a choice of one arrow for each pair. The coend computes the possible composite witnesses from primitive incidence; obtaining a particular cylinder still requires the stated experiment/context data. This is not reconstruction of joint incidence from marginals.

## 5. Explicit middle-object wiring in any CFS

The following elementary cut law works in every CFS, so in particular in F(D). It converts a compatible local wiring into a factorization recipe, rather than just naming an ambient completion.

Suppose preparations D_0:I→X, tests T_0:K→X and an actual interface object b carry a cocone r_i:D_0(i)→b and cone s_k:b→T_0(k). Factor these local cylinders:

    D_0 --e∈E--> x --m∈M_0--> b,
    b --n∈E_0--> y --v∈M--> T_0.

Factor the **actual interface connector** n m:x→y:

    x --h∈E_0--> z --j∈M_0--> y.

Then

    D_0 --h e∈E--> z --v j∈M--> T_0                  (5)

is the canonical factorization of the wired cylinder t_ik=s_k r_i, up to its unique leg-preserving isomorphism.

Proof: (v j)(h e)=v(n m)e=s r. E-cocones are closed under postcomposition by E_0 arrows: lift first against e, then against h, using orthogonality, and uniqueness twice. Dually M-cones are closed under precomposition by M_0 arrows. Hence (5) is an E/M-factorization; canonicality follows from orthogonality. END.

In F(D), the x and y can be transported local middles from F(L) and F(R), by §4. Their connector uses the matched Yoneda image of the actual b. Thus (5) is an exact **local-middle → actual-cut-middle** reconstruction law in the specified completed setting. It does not assume an arbitrary physical wiring operation preserves E/M: the relevant maps are constructed as CFS maps by the free universal property, and the residual connector is explicitly refactorized.

### Connected diagram interfaces

More generally, let r:D_0⇒B_0 and s:B_0⇒T_0 be cylinders for a nonempty connected indexing category J and interface diagram B_0:J→X. Factor r=m e and s=v n. Naturality implies n_j m_j:x→y is independent of j: for f:j→j',

    n_j m_j = n_j' B_0(f) m_j = n_j' m_j'.

Connectedness propagates this equality. The composite t_ik=s_jk r_ij is likewise independent of j. Factor the common connector and apply the same proof. For disconnected or empty J there need not be one such arrow or cylinder; one must retain component/witness data or specify the actual composite cylinder. An arbitrary coend of possible witnesses must not be confused with this common-connector condition.

## 5A. Interpretation into the original realization category

**Do not identify F(Coll(P)) with the reconstructed middle of an original cylinder.** The former is a whole free CFS category; the latter is one object with specified preparation/test legs. The preceding theorem does not equate them. Nor do marked middles retaining an observation pairing necessarily retain all operational witness sets P(a,b).

There is nevertheless a precise conversion when a semantic interpretation is given. Let X be the original CFS category. Supply boundary functors

    alpha:A→X, beta:B→X, gamma:C→X

and natural maps of witness sets

    rho_ab:P(a,b)→X(alpha(a),beta(b)),
    sigma_bc:Q(b,c)→X(beta(b),gamma(c)).

These maps need not be injective. They determine functors L→X and R→X agreeing on B, hence the proved pushout gives an evaluation functor H:D→X with

    H([p,q]) = sigma(q) rho(p).

The free-CFS hom equivalence extends H to a CFS morphism

    H#:F(D)→X,     H# Y_D ≅ H.

For every actual small cylinder r in D, E/M preservation and factorization uniqueness give

    H#(R_D(r)) ≅ R_X(Hr),                             (6)

with the preparation/test legs respected through the displayed Yoneda isomorphism. Thus this interpretation sends the reconstructed **object** in the free completed gluing to the original category's actual reconstructed object. It sends the explicit connector refactorization (5) to the same connector-factorization law in X.

To use (6) for a given original cylinder one must exhibit r with Hr that cylinder: namely, its primitive entries need specified natural witness lifts into P and Q, or the composite entries need specified compatible coend elements. This requirement is real; an observation value alone is not a witness. One always has a formal choice P(a,b)=X(alpha(a),beta(b)) and Q(b,c)=X(beta(b),gamma(c)) when boundary categories are small and X locally small, but that choice retains all such primitive arrows and may exceed the declared operational interactions. For a given interaction use its supplied witness interpretation instead, and do not silently substitute all homs.

Accordingly, (6) is a conditional but explicit semantic bridge, not a proof that the operational witness presentation can be recovered from local observation middles. The completed ambient law together with (5) and (6) proves actual preservation for the stated serial, compatible-cylinder model. It does not by itself settle the unrestricted context-sensitive realization target.

## 6. Associativity, relation semantics, and stopping boundaries

For a finite **serial chain** of small profunctors, the iterated collage gluing has one layer per boundary; its forward homs are iterated coends. Their associativity follows directly by taking the quotient of tuples of primitive witnesses by the interface-action relations, independent of parenthesization. The glued category, with all layers retained, is independent of binary bracketing up to its canonical isomorphism. Repeated use of the hom proof gives the same CFS bipushout universal property for every bracketing. Universal equivalences commute with the original legs, and their coherence follows from that universal property. The isomorphisms of cylinder middles are coherent because they preserve the same factorization legs and are unique.

For discrete A,B,C and Boolean relations viewed as subterminal Set-valued profunctors, the coend hom D(a,c) is the set of matching middle witnesses, not just a Boolean. Its **nonemptiness** is exactly existential relational composition. Multiple witnesses produce multiple parallel arrows in the ordinary CAT pushout. Passing to Boolean support is a separate quotient/interpretation; this theorem does not identify its free-CFS completion with the completion retaining witnesses.

This proof covers typed serial cuts and the compatible cylinder cuts in §5. It does not establish arbitrary simultaneous multiport wiring from independent port marginals. Such a primitive must first have its full joint boundary incidence encoded in the input doctrine. Nor is gluing outputs back to inputs an automatic relational fixed-point trace: categorical identifications may create arbitrarily many composable paths, whereas a prescribed feedback semantics can demand a different simultaneous consistency condition. No feedback theorem is asserted here.

## 7. What has advanced and what remains

Established: a specified, unlimited-size free-CFS completion is compatible with actual Set-profunctor serial gluing, at the level of the precise bipushout law (1); actual cylinders transport via (4); compatible local cylinders have the explicit middle-object cut formula (5). All three statements retain the real interface and primitive incidence. Equation (6) transports these constructions to an original CFS whenever the explicit primitive witness interpretation and required cylinder lifts are available.

Not established: an equality between ordinary gluing of completed underlying categories and the CFS bipushout; deletion of the internal interface after completion; an unrestricted multiport/feedback theorem; or identification with a particular physical realization. Those are additional targets, not premises silently used here. Infinite completion is allowed throughout; no compactness or efficiency assertion is needed for the proved law.

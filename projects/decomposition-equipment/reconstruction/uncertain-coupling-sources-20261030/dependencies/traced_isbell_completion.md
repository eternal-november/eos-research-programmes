# Traced-to-Isbell completion: a faithful bridge for port-shaped cylinder wiring

Status: derived completion lemma, using Joyal–Street–Verity plus Garner and the monoidal Isbell construction already proved in `isbell_external_product.md`. This removes the requirement that the original semantics itself be compact closed. It does not assert physical implementation or compactness of the completed realization.

## 1. Precise completion lemma

Let C be a **small traced symmetric monoidal category**, with a specified total JSV trace representing the admitted algebraic feedback. Put

    D = Int(C),      K = I(D),      H = Y_D J : C→K.

Then:

1. K has its free cylinder factorization system and a symmetric monoidal structure.
2. H is fully faithful and strong symmetric monoidal.
3. Every original wire H(U) has a specified dual in K, namely Y_D((J U)^*).
4. H preserves the given trace over original wires:

       H(Tr_C^U f) = Tr_K^{H(U)}(Hf),                 (1)

   where strong-monoidal constraints are understood and the right side is the cup/cap trace using that specified dual.
5. Thus finite admitted traced wiring in C can be computed faithfully in K. Local canonical free-CFS middles can be wired using the port construction below, obtaining an honest realization and a canonical controlled span to the reconstructed actual joint cylinder.

**Do not strengthen (3) to “K is compact closed.”** New Isbell middles need not be dualizable. Nor is a total trace on all objects of K asserted. Only trace over the designated representable wire objects is needed.

### Primary facts checked

JSV, *Traced monoidal categories*, Propositions 4.1, 4.2 and 5.1 respectively establish full faithfulness of J:C→Int(C), its strong monoidal structure, and the tortile structure making J traced. The symmetric, trivial-twist specialization is compact closed. Proposition 3.1 gives the canonical cup/cap trace. [Primary paper, pp. 453–462](https://octocurious.com/papers/joyal1994-traced-monoidal-categories.pdf).

Garner, *The Isbell monad*, Proposition 3.1 and Theorem 3.3 supply the free CFS on I(D); the Yoneda embedding is fully faithful. [Primary paper](https://arxiv.org/pdf/1410.7108). The symmetric-monoidal lift used here is the explicit external-product/Kan-extension construction already derived in `isbell_external_product.md`, not an additional theorem attributed to Garner.

## 2. Proof, including the trace claim and size

Int(C) has pairs (A,U) as objects and

    Int(C)((A,U),(B,V)) = C(A⊗V,B⊗U).

Its composition uses the given trace; J(A)=(A,1). In the symmetric case the dual of (A,U) is (U,A). These formulas show that small C gives small D; the primary results above supply the category, coherence, and trace-preservation axioms.

On K use

    X ⊗_K Z = I(⊗_D)(ext(X,Z)),      1_K=Y_D(1_D).

The external-product calculation gives associativity, symmetry, unit coherence, and a strong symmetric monoidal Y_D. Explicitly both signed presheaves of X⊗_K Z are the corresponding left Kan extensions of the external products of their signed presheaves. Thus Y_D preserves the selected evaluation and coevaluation maps and their snake equations. In particular, H(U) has dual Y_D((J U)^*).

For f:A⊗U→B⊗U in C, JSV gives

    J(Tr_C^U f) = Tr_D^{J(U)}(Jf).

Expand the right side into evaluation, coevaluation, symmetry, tensor and composition in D. Applying strong symmetric monoidal Y_D turns this expression into the same cup/cap expression in K. This proves (1) directly, without invoking trace preservation for a target that has not been proved globally traced. Full faithfulness follows by composing the two fully faithful functors J and Y_D.

Consequently, for f,g:A→B in C,

    H(f)=H(g) iff f=g.

No original observable arrow is identified by the completion, and no extra arrows appear between these embedded original endpoints. Equality of the completed network with H(actual network) therefore preserves the original semantics exactly, not merely an overapproximation.

For universes: take C small in U and U-small sets as presheaf values. D remains U-small; K is generally large relative to U but locally U-small, with the CFS for U-small cylinders. Work in a larger ambient universe containing these presheaf categories. The Kan-extension coends and finite tensor constructions are U-small. No assertion that K is small or finitely representable is made, and no iteration over all K-objects is required.

## 3. How the bridge applies to actual two-sided cylinders

This section states the port-shaped scope explicitly rather than replacing every cylinder by one full-port arrow.

For each primitive node v, give an actual small cylinder in C whose objects have the form

    preparation: A_v(p) ⊗ In_v,
    test:        B_v(q) ⊗ Out_v,

where In_v and Out_v are fixed finite tensors of typed wire objects. Its entries r_v(p,q) are supplied morphisms of C, natural in p and q. Factor its H-image in K:

    H(A_v(p)⊗In_v) --e_v,p--> M_v --m_v,q--> H(B_v(q)⊗Out_v).

The entire preparation cocone is in E and the entire test cone in M. The object M_v is the actual canonical middle of this image cylinder, not I(Coll(r_v)) or another ambient category.

Now specify a finite typed network matching output ports to input ports, permitting precisely the feedback interpreted by C's given trace. Give joint preparation and test indexing categories, their selections of local contexts, and natural external preparation/test arrows. A joint preparation may be correlated: it is an actual map into the tensor of the selected A_v(p), not a product of its marginals. The dual statement holds for joint tests. These maps must have the stated preparation-only and test-only dependence. Passthrough wires can be represented by identity nodes.

Let E_int be the internal wires. A common carrier is

    W = (⊗_v M_v) ⊗ (⊗_{e∈E_int} H(U_e)^*),          (2)

up to a fixed permutation. Construct its preparation cocone by:

- applying the actual joint preparation map;
- creating a cup for each internal wire U_e;
- feeding its U_e end into the corresponding input port;
- applying every e_v,p and retaining every dual U_e* end in W.

Construct its test cone by applying every m_v,q, contracting each outgoing internal U_e with the retained U_e* via evaluation, and applying the actual joint test map. Call these maps p_a:D_a→W and q_b:W→T_b. Their naturality follows from that of the original cylinders and joint context maps.

Substituting m_v,q e_v,p=H(r_v(p,q)) reconnects precisely the declared wires. Compact string identities and equation (1) identify the result with the H-image of the **actual** traced network cylinder s:

    q_b p_a = H(s_ab).                               (3)

This is a constructed honest realization of that joint cylinder. It uses only the original fixed wire duals, never duals of M_v. No hypothesis that an external wiring operation or trace preserves E/M was imposed. The new preparation/test legs need not themselves be in E/M because cups and caps intervene.

If a primitive has no fixed port shape, or its internal type/entry selection depends jointly on preparation and test in a way not expressible by the supplied separate legs, this theorem does not manufacture such a presentation. Likewise, local marginals do not determine the required joint preparation map. The completion fixes availability of duals; it does not create missing operational/context data.

## 4. Canonical controlled comparison

Let the canonical factorization of Hs be

    HD --e∈E--> R_K(Hs) --m∈M--> HT.

Factor the constructed preparation cocone p as

    HD --a∈E--> Z --b∈M_0--> W.

Orthogonality of a against m gives a unique h:Z→R_K(Hs) satisfying

    h a=e,       m h=q b.

Since a and h a=e are E-cocones, the usual orthogonality cancellation argument gives h∈E_0. Hence the promised comparison is

    W  ←[b∈M_0]  Z  →[h∈E_0]  R_K(Hs).              (4)

Both legs are compatible with the displayed actual preparation/test data. The span need not be invertible. It is a comparison of objects realizing the same actual cylinder, not merely an inequality of supports. Permutation and reassociation of the fixed network construction are handled by monoidal coherence, and factorization comparisons preserving the same legs are unique.

For one feedback box f:A⊗U→B⊗U with Hf=m e, the smaller carrier M⊗H(U)* already suffices: cup U in the preparation, apply e, retain U*, then apply m and cap U in the test. Their composite is H(Tr_C^U f). This directly verifies the cyclic case without any M-dual.

## 5. Original CFS versus the new free CFS

R_K(Hs) is reconstruction in the **new free CFS** K. If C already has a preferred CFS, H is not thereby proved to preserve it. In particular,

    H(R_C(s)) ≅ R_K(Hs)

has not been established. Full faithfulness preserves original arrows, not arbitrary chosen E/M structures.

If R_C(s) with its original legs exists, its H-image is at least another honest realization of Hs, since functors preserve the equation expressing factorization. The same procedure as §4 therefore constructs a controlled span

    H(R_C(s)) ← M_0-leg apex → E_0-leg R_K(Hs)

inside K. This is a separate derived relation, not a preservation assertion. Descending a newly constructed K-object to C would need additional semantic/realization structure and is not required by this lemma.

The theorem concerns a specified **total JSV trace**. Guarded, partial, causal, normalized probabilistic, or physically motivated feedback operations do not automatically supply one. Nothing here adds feedback to C that the input trace did not already interpret. Nor does faithful formal completion certify a physical implementation of its new objects.

**Admissibility and cost boundary.** Full faithfulness preserves original external arrows and their equalities, not experimental or computational resource charges. The semantic claims concern the declared original wiring diagrams, their supplied contexts, and the designated trace. Newly available abstract states, cups/caps, or maps are not automatically admissible physical operations or experiments. The completion is not a zero-cost implementation and does not extend a resource budget or guardedness discipline for free. A budgeted or guarded lifting law would be a separate result requiring its own definitions and proof.

## Appendix: mixed E/M pullbacks in the Isbell envelope

These formulas justify composition of the polarized spans without a hidden completeness assumption. In I(D), a singleton E_0 arrow has invertible positive component, and a singleton M_0 arrow has invertible negative component, by Garner's projection description.

For f:X→Z, g:Y→Z, the candidate pullback has

    P+ = X+ ×_{Z+} Y+,
    P- = X- ⊔_{Z-} Y-,                               (5)

where negative arrows are reversed: f-:Z-→X-. The pairing evaluates an X- representative against the X+ projection, or a Y- representative against Y+. These agree on Z- because f+(x)=g+(y) and both arrows preserve their pairings. Positive pullback and negative pushout universality then prove the Isbell pullback universal property.

For small D all presheaves are allowed, so (5) gives arbitrary pullbacks. For a merely locally small large D, the positive pullback of small presheaves may not be small: do not infer arbitrary completeness. Nevertheless, pullbacks along E_0 always exist: their positive pullback is isomorphic to the other small presheaf, and the negative pushout is a small colimit of small copresheaves. The E_0 projection remains E_0.

Most importantly, for f:U→R in E_0 and g:V→R in M_0, take explicitly

    P+=V+,     P-=U-,
    xi_P(u-,v+)=xi_U(u-,(f+)^{-1}g+(v+)).

The projections are

    P→U: positive (f+)^{-1}g+, negative identity;     hence M_0,
    P→V: positive identity, negative f- (g-)^{-1};    hence E_0.

They are the pullback projections by (5), and no potentially large positive limit is needed. Consequently spans with left leg M_0 and right leg E_0 compose: each apex pullback is of exactly this mixed form, and the composite legs stay in the respective classes. The usual pullback associators are coherent. This gives a valid ambient span calculus; it does not by itself assert that every independently selected network-normalization comparison is its compositor.

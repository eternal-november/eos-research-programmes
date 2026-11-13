# Regression: noncompact original ports with rational Schur feedback

**Result: PASS.** The partial-trace/CFS completion applies to genuinely noncompact original port semantics, not merely Rel or quantale matrices. This is a regression of the established theorem, not a novelty, learning, or efficiency claim.

## 1. Exact admissibility doctrine verified in the primary source

Let C be the small skeleton of finite-dimensional rational vector spaces (objects Q^n; rational matrices), with monoidal operation DIRECT SUM ⊕ and unit 0. For

    f = [ A  B ] : X⊕U → Y⊕U,
        [ C  D ]

choose the partial feedback

    Tr_U(f) = A+B(I_U−D)^−1 C

**defined exactly when I_U−D is invertible.** This exact domain and formula are Malherbe–Scott–Selinger, *Partially traced categories*, §3.3.2, Definition 3.11; Proposition 3.12 verifies the Haghverdi–Scott partial-trace axioms. The definition applies over any field. No kernel-image extension is needed. [Primary PDF, printed p. 8](https://www.mathstat.dal.ca/~selinger/papers/ptrace.pdf#page=8).

This is not ordinary tensor-product trace. Indeed C with ⊕ is noncompact: any prospective coevaluation 0→U⊕U* and evaluation U*⊕U→0 are zero maps. The snake composite on U is consequently zero, so a dual can exist only when U=0. In particular the one-dimensional rational port is not dualizable in the original monoidal category.

## 2. Two exact scalar checks

For X=Y=U=Q take

    f_good = [ 1  1   ].
             [ 1  1/2 ]

Here I−D=1/2, with inverse 2, and

    Tr_Q(f_good)=1+1·2·1=3.

For

    f_bad = [ 1  1 ],
            [ 1  1 ]

I−D=0 is not invertible, so the chosen trace is UNDEFINED. This is a domain failure, not the rational value 0, infinity, or any arbitrary completed value. Both computations were also checked using exact rational arithmetic.

## 3. What the completion preserves—and refuses to legalize

MSS Theorem 6.1 gives a faithful strong symmetric monoidal, trace-preserving and trace-reflecting embedding J into the compact category

    D=P(Int_p(C))/~.

Its trace reflection is with respect to the chosen domain above. [Primary PDF, printed p. 25](https://www.mathstat.dal.ca/~selinger/papers/ptrace.pdf#page=25).

Apply the previously proved free-Isbell step K=I(D), H=Y_D J. Full faithfulness of Y_D preserves reflection. Consequently

    Tr_K^(HQ)(H f_good)=H([3]),

where [3]:Q→Q is multiplication by 3. Meanwhile the completed trace of H f_bad exists but lies OUTSIDE H(C(Q,Q)). Otherwise it would equal H(g) for some rational linear map g, and reflection would make the original trace of f_bad defined—a contradiction.

The monoidal constraint is H(X⊕U)≅H(X)⊗_K H(U). Thus the compact trace in K models the ORIGINAL direct-sum Schur feedback; it does not replace it by the familiar tensor-product trace on finite-dimensional vector spaces. The added duals are formal completion objects. H is not claimed full, and its new arrows do not authorize original executions.

For every port-shaped finite network whose feedback nodes carry the original invertibility certificates, the existing partial-trace theorem therefore yields the honest joint-cylinder realization and CFS comparison in K. Undefined or uncertified loops remain excluded from the original experiment family. A mixed preparation/test family still needs an admitted rectangle; a valid one-entry regression does not waive that requirement.

## 4. Finite original versus full completed cylinder factorization

Original FinVect_Q has image factorizations of finite-indexed cylinders: form the finite colimit-to-limit map and take its image. Do not label this a full small-cylinder CFS. In fact the countable cylinder with every preparation/test object Q and entry δ_ij has no finite-dimensional realization: preparation vectors would have to be linearly independent, since its tests extract every coefficient. Thus even existence of a middle fails for that small infinite cylinder in FinVect_Q.

The small category D has the free Isbell envelope K with its full small-cylinder CFS in the selected universe. That is the ambient CFS used here. No preservation of the original finite-cylinder middles by H is assumed; their images are honest realizations compared with the completed canonical middles by the existing span construction.

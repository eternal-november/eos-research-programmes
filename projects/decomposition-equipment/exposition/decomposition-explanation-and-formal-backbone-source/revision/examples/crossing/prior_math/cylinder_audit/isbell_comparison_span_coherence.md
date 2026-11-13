# Coherent raw comparison spans in a free Isbell envelope

Status: proved in K=I(C), for the stated smallness doctrine and fixed actual cylinders. This strengthens normalized-endpoint coherence to **invertible coherence of the raw M-left/E-right realization-comparison spans**. It also proves invertible context-enlargement compositors in the free envelope; descent to an arbitrary chosen CFS retains a coherent, potentially noninvertible comparison.

## 1. Realizations and their polarized spans

Fix an actual small cylinder r:D⇒T in K. Define Fact(r):

- objects are factorizations D --p_X--> X --q_X--> T with q_X p_X=r;
- an arrow f:X→Y satisfies f p_X=p_Y and q_Y f=q_X.

The legs need not themselves be E/M. Choose the canonical E/M factorization D --e--> R --m--> T. For each realization X, factor its preparation cocone

    p_X = b_X a_X,     a_X∈E, b_X∈M_0,
    D --a_X--> G_X --b_X--> X.

The test cone at G_X is q_X b_X. Orthogonality supplies h_X:G_X→R with

    h_X a_X=e,       m h_X=q_X b_X.

The cancellation lemma for E-cocones implies h_X∈E_0. Thus there is a canonical comparison in Fact(r)

    C_X = (X ←[M_0] G_X →[E_0] R).                  (1)

Throughout, a comparison span X←U→Y means both legs are arrows of Fact(r), not merely arrows between their underlying objects. These compatibility equations are essential.

## 2. Mixed pullbacks and their preservation

In I(C), E_0 arrows have invertible positive components, and M_0 arrows have invertible negative components. Here a map X→Y has components X+→Y+ and Y-→X-. These characterizations follow from the singleton case of Garner's projection description of the free CFS (Proposition 3.1 of [The Isbell monad](https://arxiv.org/pdf/1410.7108)).

For f:U→Y in E_0 and g:V→Y in M_0, their pullback P exists even if C is large. Explicitly,

    P+=V+,    P-=U-,
    xi_P(u-,v+)=xi_U(u-,(f+)^{-1}g+(v+)).

The projections are

    s:P→U:  s+=(f+)^{-1}g+,  s-=id,                 s∈M_0;
    t:P→V:  t+=id,          t-=f- (g-)^{-1},         t∈E_0.

Pairing compatibility follows from that of f and g. The positive component is the pullback along an isomorphism; the negative component is the pushout along an isomorphism. These component universal properties give the pullback in I(C). Both presheaves remain small. No arbitrary large-presheaf pullback is asserted.

**Mixed-square lemma.** Every commuting square in I(C) whose horizontal arrows belong to E_0 and vertical arrows belong to M_0 is a pullback. Compare it to the explicit pullback above. The comparison's positive component is an isomorphism because the top arrow is E_0; its negative component is an isomorphism because the left arrow is M_0. Hence the comparison is an Isbell isomorphism.

Consequently any functor between free Isbell envelopes preserving E_0 and M_0 preserves these mixed pullbacks. This is not an assumption about arbitrary limits. The image square still has horizontal E_0 and vertical M_0, so the lemma applies.

The same component argument works for finite products of such envelopes. Hence an n-variable functor preserving E_0/M_0 separately preserves the componentwise mixed pullbacks: simultaneous E_0 or M_0 tuples are handled by factoring their image into changes of one coordinate at a time.

Thus M-left/E-right spans form a bicategory with these pullbacks; E/M-preserving functors lift to pseudofunctors on it. Associativity and unit comparison isomorphisms are the unique maps commuting with pullback projections. Preservation of those projections proves their coherence.

## 3. Rigidity of a comparison into the canonical middle

**Theorem.** Any compatible span

    S=(X ←[u∈M_0] U →[v∈E_0] R)

in Fact(r) is uniquely isomorphic to C_X, preserving exterior legs and realization data.

**Proof.** Write p_U for U's preparation cocone. Since u p_U=p_X=b_X a_X and a_X∈E, u∈M_0, orthogonality gives a unique

    eta:G_X→U,     eta a_X=p_U,     u eta=b_X.

The arrows v eta and h_X have the same composites with a_X, namely e. They also have the same composites with m:

    m v eta = q_U eta = q_X u eta = q_X b_X = m h_X.

Orthogonality of a_X against the canonical test cone m gives v eta=h_X. Now u eta=b_X, with u and b_X in M_0, implies eta- is an isomorphism. Similarly v eta=h_X, with v and h_X in E_0, implies eta+ is an isomorphism. Therefore eta is an isomorphism in I(C), and its equations make it an isomorphism in Fact(r). The orthogonality construction gives uniqueness among maps preserving the preparation and left leg. END.

Equivalently, the category of compatible polarized comparison spans from X to R has one object up to unique isomorphism. Even if span maps are defined using exterior legs alone, uniqueness remains: the right E_0 leg determines a map's positive component, and the left M_0 leg determines its negative component. The realization compatibility then follows from these same component equations.

This uses a special feature of the free Isbell CFS: membership in E_0/M_0 has the indicated component-isomorphism form and hence each class has two-out-of-three. It is not established for an arbitrary CFS.

## 4. The invertible compositor

Let S=(X←[M_0]U→[E_0]Y) be any compatible span in Fact(r). Compose it with C_Y by the mixed pullback

    V = U ×_Y G_Y.

The preparations into U and G_Y have equal composites into Y, so they induce a preparation cocone into V. Its test cone can be computed through either projection; the expressions agree by the pullback square and the two realization equations. Hence V is an object of Fact(r).

The composite left leg V→U→X is M_0; the composite right leg V→G_Y→R is E_0. The rigidity theorem therefore gives a unique invertible 2-cell

    C_X  ≅  S ; C_Y.                                 (2)

For S:X⇝Y and T:Y⇝Z, the two applications of (2) and the direct application to S;T are maps between the same compatible spans X⇝R, after the canonical pullback associator. They agree by uniqueness. For an identity span, (2) is the usual unit isomorphism, again by uniqueness. This proves associativity and unit coherence, not merely coincidence of final canonical middles.

Notice that the preparation cocone of V was not assumed E. Rigidity proves retrospectively that it is E, since the constructed isomorphism identifies it with a_X. Omitting that point would have made the argument circular.

### Naturality for changes of realization object

An arbitrary arrow k:X→Y in Fact(r) need not be an M/E span. Nevertheless orthogonality of a_X against b_Y gives a unique G(k):G_X→G_Y with

    G(k)a_X=a_Y,      b_Y G(k)=k b_X.

The canonical test cone implies h_Y G(k)=h_X. These equations define a comparison-of-spans cell with vertical source boundary k and target boundary id_R. They imply identity and composition laws by uniqueness. Since h_Y and h_X have invertible positive components, so does G(k), although G(k) need not be an isomorphism. This naturality statement compares different source objects without pretending their spans lie in one hom-category with an unchanged source.

## 5. Assembly by actual raw network carriers

Consider a fixed port-shaped network with fixed dualizable wire types, in the symmetric monoidal Isbell envelope already constructed in `isbell_external_product.md`. Its raw carrier operation is

    F_N(X_v)=(⊗_v X_v)⊗(⊗_internal wires U_e*).

Assume local S_v=(X_v←[M_0]U_v→[E_0]Y_v) preserve their actual local preparation/test legs. Tensoring the spans and identity maps of the auxiliary wire objects gives

    F_N(X_v) ←[M_0] F_N(U_v) →[E_0] F_N(Y_v).         (3)

The leg polarities follow from the already proved separate E/M preservation of the lifted tensor. The preparations are assembled from the actual external joint preparation maps, cups, and local preparation legs; the tests from local test legs, caps, and actual joint tests. The local span equations imply that both legs of (3) preserve these assembled preparations and tests. Thus (3) lies in Fact(r_N) for the same actual joint cylinder r_N.

Combining (3) with (2) proves

    C_(F_N(X_v))  ≅  F_N(S_v) ; C_(F_N(Y_v)).          (4)

This is the raw-span substitution law sought: replacing local realizations by compatible reconstructed ones and then comparing globally yields the same comparison span, up to a specified coherent isomorphism, as comparing the raw global realization directly.

Moreover F_N preserves the mixed pullbacks by §2. Consequently its lift respects composition of local spans, not just their endpoints. This validates whiskering of (2) through another layer of network assembly.

For hierarchical substitution of a fixed finite graph, flattening the raw carrier only reassociates/permutates the same primitive-middle factors and the same internal-wire-dual factors. These are monoidal coherence isomorphisms, compatible with preparations and tests. Apply (4), mixed-pullback preservation, and rigidity: all hierarchical routes from that fixed raw carrier to R(r_N) agree as comparison spans. This includes the identity **wiring operation** that leaves the graph and its carrier unchanged.

Partial/guarded operational semantics retain their separate domain/admission requirements. Formal normalization in the completed category is not automatically an executable replacement. The algebraic equations here concern compatible realizations of a declared actual cylinder; they do not supply missing operational certificates.

## 6. Identity-box insertion is not the same as a syntactic unit

Inserting an evaluated identity node changes the raw carrier, so direct comparison spans before and after insertion have different left endpoints. They cannot literally be identified. The required boundary comparison must be constructed.

For insertion on an internal wire U, write the chosen canonical identity factorization

    U --e--> M_id --m--> U,     m e=id_U.

The old wire contributes a stored U*. The new wire segment contributes

    V=M_id⊗U*_new⊗U*_old.

There are explicit maps

    p:U*→V: create coev':1→U⊗U*, apply e to U,
              and carry the old U*;
    q:V→U*: apply m, evaluate its U against the old U*,
              and retain the new U*.

The snake equation gives q p=id_U*. Thus V is an honest realization of the singleton identity cylinder on U*, whose canonical middle is U*. Its canonical comparison supplies a compatible M/E span V⇝U*. Tensor it with the rest of the network. Its preparation is exactly the preparation with the extra identity node and extra cup; its test contracts exactly the subdivided wire. Therefore it gives an explicit span from the inserted carrier to the original carrier. Equation (2) then compares their global canonical spans with that boundary span included. There is also a direct realization arrow k=id_rest⊗q from the inserted carrier to the original one: k p_inserted=p_original follows from qp=id, and q_original k=q_inserted follows from the construction. The naturality cell of §4 applies to this arrow. This is a double-span comparison with changing source boundary, not an isomorphism of spans with falsely identified sources.

At a fixed-typed external port, one may instead isolate the identity node together with the adjacent **canonically reconstructed** primitive cylinder. The enlarged local subnetwork realizes that same cylinder; its canonical comparison targets the previous primitive middle. Equation (4) transports this verified local replacement through the rest of the graph. This requires the stated common local cylinder and is not an unproved rule for arbitrary added nodes or contexts.

Repeated such insertions have coherent comparisons whenever their raw carriers and intervening boundary spans are related by the displayed constructions: after composing toward the same R, rigidity identifies the routes. No claim that identity insertion leaves an unnormalized carrier unchanged is needed.

## 7. Free context-enlargement spans also compose strongly

Let r:D⇒T be an actual cylinder in C, and restrict its preparation/test diagrams along commuting context-index functors P→P' and Q→Q'. Let R(P,Q) be its canonical free middle in I(C). Its signed presheaves are

    R(P,Q)+ = colim_p C(-,D(p)),
    R(P,Q)- = colim_(q in Q^op) C(T(q),-).

Enlarging preparations gives R(P,Q)→R(P',Q) in M_0: its negative component is the identity. Restricting tests gives R(P,Q')→R(P,Q) in E_0: its positive component is the identity. The context squares commute by the canonical leg equations. These assertions concern the actual restricted incidence, not a reconstruction of it from marginals.

For successive context enlargements, the direct comparison span has apex R(P_0,Q_2). Its comparison to the composite is the square

    R(P_0,Q_2) --E_0--> R(P_0,Q_1)
         |M_0                |M_0
         v                   v
    R(P_1,Q_2) --E_0--> R(P_1,Q_1).

By §2 this square is a pullback. Therefore the canonical comparison

    R(P_0,Q_2) → R(P_0,Q_1) ×_[R(P_1,Q_1)] R(P_1,Q_2)

is invertible in I(C). The E-left/M-right mixed-corner spans consequently have coherent invertible compositors in the free envelope. All associativity/unit diagrams commute by their common projections. Noninjective context-index functors are allowed when the diagrams and entries commute; an inclusion notation is not a hidden injectivity assumption.

The same mixed-square preservation argument lets the lifted E/M-preserving tensor operations transport these pullback squares. This supplies compatibility of such specified context maps with the raw carrier operations. It does not manufacture a context map for an intervention whose new incidence is unrelated to the given cylinder restrictions.

Importantly, this is invertibility of the **span compositor**, not invertibility of either leg of an individual context span. Individual context changes can still be nontrivial.

## 8. Descent explains the coherent nonexactness in an original CFS

Now let C itself have a chosen CFS, and let

    A:I(C)→C,       A Y_C≅id_C

be its CFS reconstruction functor, supplied by Garner's free property. It preserves E-cocones and M-cones. Therefore

    A(R_free(r)) ≅ R_C(r)

for every actual small cylinder r in C, with its preparation/test legs; this follows by applying A to the free factorization and using uniqueness in C. Context-comparison arrows likewise transport to the canonical original-CFS arrows because they satisfy the same orthogonality/leg equations.

Suppose the target C has the pullbacks needed for the images of the selected spans. For a source pullback P=U×_Y V, the image projections give a canonical comparison

    theta: A(P) → A(U) ×_[A(Y)] A(V).                 (5)

This determines a 2-cell from the image of a composite span to the composite of the image spans: its direction is the oplax direction, independently of terminology conventions. For three composable spans, both routes from the image of the iterated source pullback have the same projections to A of every original apex. The target iterated-pullback universal property therefore makes them equal. Identity comparisons are identities up to the chosen pullback unit isomorphisms. Thus descent is coherently oplax, without any assumption that A preserves pullbacks.

The target here can be the ordinary bicategory Span(C). Do not assume its composites stay in a polarized E/M subclass: arbitrary CFS E_0 arrows have not been shown stable under all required pullbacks. If C lacks the specified pullbacks, retain the canonical commuting projection cones instead; a Span(C) assertion is then unavailable.

For the free context square in §7, its source compositor is invertible, but after applying A and then (5), the resulting compositor can fail to be invertible. Via A(R_free(r))≅R_C(r), it is precisely the original mixed-corner comparison derived by the CFS leg equations. Thus the earlier Set row-image counterexample is not contradicted: the free positive presheaf retains formal preparation witnesses, whereas the chosen Set realization identifies equal observational rows. Pullback exactness can be lost under that identification.

The exact condition for invertibility of the descended compositor is preservation by A of this particular source pullback, not a blanket assumption. Formula (5) exposes the controlled defect, and its coherence is automatic even when it is noninvertible.

No monoidality of A has been established. Hence A applied to a coherent formal tensor/wiring construction is not automatically the physical tensor/wiring of A applied locally. The descent theorem transports spans and actual-cylinder reconstructions; comparing it with a separately specified physical wiring operation needs its own compatibility data.

## 9. The admitted intervention doctrine

The intervention claim has three distinct forms:

1. **Specified wiring interventions:** attach or replace a declared node or a supplied joint preparation/test fragment in a port-shaped network. The same raw-span law and its substitution coherence apply uniformly to the resulting network. Its reconstructed behavior may differ from the original behavior; no isomorphism between those behaviors is required or inferred.
2. **Specified context changes:** enlarge/restrict preparation or test indexing with the actual commuting incidence maps of §7. Their comparison spans compose strongly in the free envelope and oplax after descent as in §8.
3. **Supplied behavior-comparison data:** when an intervention comes with an actual cylinder morphism or an explicitly compatible realization/wiring map, use that map to form the corresponding comparison. The same-Fact rigidity theorem applies only when its fixed-cylinder compatibility equations hold, not merely because both cases are called interventions.

An arbitrary unknown internal intervention is not thereby an action on the old canonical middle. Supplying its new primitive cylinder lets the theorem reconstruct the new declared case, but does not show how to predict that cylinder from the old reconstruction. This is a doctrine of specified, admitted interventions and their coherent wiring comparisons, not of all physical counterfactuals.

## 10. Exact scope of the improvement

Proved in free Isbell:

- compatible M-left/E-right realization spans normalize coherently as spans;
- lifted tensor/network carrier operations preserve their mixed pullbacks;
- specified context-enlargement E-left/M-right spans have invertible compositors;
- arbitrary realization arrows have natural comparison-of-spans cells;
- raw graph substitution and identity wiring have the resulting coherent laws, with explicit separate handling of identity-box insertion.

For a chosen original CFS, reconstruction transports exactly but span composition descends only oplax unless the relevant pullbacks are preserved. This explains, rather than removes, the existing nonexact Set example.

Still outside these results are arbitrary interventions without supplied context/incidence maps, automatic compatibility of the original reconstruction algebra with physical tensor, and new feedback-domain, budget, or physical-realizability claims. The proved laws apply to the actual compatible cylinders and port-shaped networks specified above; they do not infer missing joint contexts from marginals.

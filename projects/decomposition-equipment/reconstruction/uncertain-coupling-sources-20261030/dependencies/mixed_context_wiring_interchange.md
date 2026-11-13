# Mixed context/wiring interchange: the coherent variance-aware law and a sharp obstruction

Status: a checked joint law, not an inference from separate coherence results. All previously delivered proofs remain unchanged. Work in K=I(C), initially with C small so the pullbacks used below exist. The fixed-port wiring and its actual joint contexts are supplied; no incidence is inferred from marginals.

## 1. The two context directions must remain visible

Let Prep and Test be categories of context selections/enlargements, and put

    B = Prep × Test^op.

For each (P,Q), suppose an actual cylinder has raw network realization X(P,Q) and canonical middle R(P,Q), with separated signed presheaves

    X(P,Q) = (X_P,T_Q,xi_X),
    R(P,Q) = (G_P,H_Q,xi_R).

The actual preparation/test legs induce natural presheaf maps

    u_P:G_P→X_P,        v_Q:H_Q→T_Q.

Their pairing compatibility means xi_R(h,g)=xi_X(v_Q h,u_P g). The preparation factorization apex is consequently

    U(P,Q)=(G_P,T_Q,xi_U),
    xi_U(t,g)=xi_X(t,u_P g).

There are canonical arrows

    b:U→X,     b+=(u_P), b-=id,     b∈M_0;
    h:U→R,     h+=id,   h-=(v_Q),   h∈E_0.           (1)

For the raw network construction in question, each local canonical free middle has positive colimit of preparation representables and negative colimit of test corepresentables. External products, their signed left Kan extensions, and fixed wire-dual factors therefore yield X_P and T_Q separately. The induced maps u_P and v_Q come from the natural primitive/external preparation and test legs; signed colimit universality makes them natural. These properties are derived for this assembly (and immediate for a fixed honest carrier with its restricted legs), not guaranteed for an arbitrarily selected family of honest realizations depending jointly on P,Q. New incidence requires a declared wiring/context morphism. G_P and H_Q are the two free boundary colimits of the actual joint cylinder.

**Joint naturality theorem.** X,R,U are functors B→K, and b,h are natural transformations, pointwise M_0 and E_0 respectively.

Proof: a context arrow is covariant in preparations and contravariant in tests. Define U on it by the induced positive map on G and reversed negative map on T. Naturality of u and the raw pairing gives pairing compatibility. Functoriality holds componentwise. The squares for b are precisely naturality of u and identity on T; those for h are identity on G and naturality of v. END.

This already gives commuting mixed squares containing both context change and normalization. It is not necessary, and generally incorrect, to replace simultaneous enlargement of both axes by a single covariant context arrow.

## 2. Main theorem: coherence in spans of context bifunctors

Choose a small declared context base B=Prep×Test^op (or the stated subcategory/reindexing of it). In K^B mark natural transformations E_0 or M_0 when they have that class pointwise. Mixed pullbacks are computed pointwise and their induced maps are natural. Therefore the earlier mixed-span construction gives the bicategory

    Span_(M,E)(K^B).

The functor U and natural transformations (1) constitute a single comparison span in this bicategory, not an unrelated list of fiberwise spans.

Local context selections must be supplied as reindexing functors, separately covariant on preparations and contravariant on tests. Precomposition preserves the pointwise polarities and mixed pullbacks. A fixed-port network operation applies F_N pointwise; its previously proved separate class preservation and mixed-pullback preservation consequently hold in the functor category. Thus both reindexing and raw network assembly lift to these span bicategories.

The proof below shows that normalization substitution isomorphisms are natural transformations of the entire context family. They therefore give actual isomorphisms of spans in Span_(M,E)(K^B), where associativity and unit coherence are checked jointly, not one fiber at a time. Wire objects and their selected duals are fixed throughout these reindexings. A varying wire map is not silently sent covariantly to its dual: dualization is contravariant, so such variation would require specified coherent isomorphisms, an indexed-dual construction, or additional equipment not proved here.

For a second description, use the standard span double-category construction, stated explicitly here. Objects are objects of K, vertical arrows are ordinary K-arrows, horizontal arrows are spans, and a square is a map between their apices whose triangles commute with the specified vertical boundary arrows. Vertical pasting is composition of maps; horizontal pasting uses the pullback universal property. Associators and units are the canonical pullback isomorphisms. For small C, pullbacks in I(C) use positive presheaf pullbacks and negative copresheaf pushouts.

Equation (1) assigns a horizontal comparison span

    X(P,Q) ←[M_0] U(P,Q) →[E_0] R(P,Q)

to each context and an ordinary double-category square U(k) to each correctly variant context arrow k. Identities and compositions are respected because U is a functor. This is a span of natural transformations, or equivalently a horizontal natural comparison between the vertical context functors X and R.

Now apply a raw fixed-port network functor F_N. The lifted tensor preserves E/M separately, so it assembles local compatible comparison spans; their preparation/test equations remain natural in B. As proved in `isbell_comparison_span_coherence.md`, mixed pullbacks are preserved and normalization yields the pointwise isomorphism

    C_(F_N(X_v)) ≅ F_N(S_v) ; C_(F_N(Y_v)).           (2)

**The missing joint check:** these isomorphisms are natural in the context parameter, not merely separately given at each parameter. For any context arrow k, compare the two routes around its naturality square. They are maps from the same source apex to the same target apex, with the same exterior boundary maps. The target comparison has a left M_0 leg and right E_0 leg. Its right leg's invertible positive component uniquely determines the positive component of any such apex map; its left leg's invertible negative component uniquely determines the negative component. Therefore the two routes agree.

The same uniqueness argument makes all context/substitution associativity and unit diagrams commute. The raw carrier flattening isomorphisms are likewise natural because they only permute/reassociate the specified factors. Thus (2) is a natural comparison of the **whole two-variable context family**, compatible with network substitution in this span double category.

This proves a joint context/wiring/normalization law without assuming a Beck–Chevalley condition. It uses actual context maps and keeps their two variances visible. It does not yet assert a single ordinary-span 2-cell after replacing simultaneous enlargements by horizontal mixed-corner spans.

## 3. What happens when both enlargements are collapsed to spans

Write old=(P,Q), new=(P',Q') with both contexts enlarged. Let

    g:G_P→G_P',   x:X_P→X_P',
    k:H_Q→H_Q',   t:T_Q→T_Q'.

Naturality gives x u_P=u_P' g and t v_Q=v_Q' k. Compare the two horizontal-span paths from X(old) to R(new):

    L-path: C_old ; (canonical context span),
    R-path: (raw context span) ; C_new.

Computing their pullback apices in I(C) gives

    L = (G_P, T_Q ⊔_[H_Q] H_Q'),
    V = (X_P ×_[X_P'] G_P', T_Q').                    (3)

The pairings are the induced pullback/pushout pairings; the formulas include the actual exterior legs. The ordinary-span interchange would need a map L→V or V→L commuting with those legs. Neither direction is automatic.

There is, however, a canonical common mixed apex

    J=(G_P,T_Q')=U(P,Q').

It has maps

    J→L: positive identity;
         negative [t,v_Q']:T_Q⊔_[H_Q]H_Q'→T_Q';      an E_0 map,
    J→V: positive (u_P,g):G_P→X_P×_[X_P']G_P';
         negative identity;                          an M_0 map.

Naturality ensures these maps exist, preserve pairings, and commute with both exterior legs. Thus

    L ←[E_0] J →[M_0] V                              (4)

is a legitimate span of apex maps over the fixed exterior endpoints. It is not, in general, an ordinary map of the two spans in (3). Its left leg is invertible precisely when the displayed v-square gives the required pushout; its right leg is invertible precisely when the displayed u-square gives the required pullback. The port-wiring hypotheses do not force either condition.

Equation (4) is a useful explicit controlled comparison when one chooses to collapse both context axes. It becomes an actual 2-cell in the richer, explicitly constructed bicategory below, not an ordinary map of spans.

## 4. A coherent bicategory for the collapsed comparisons

Here is the dimension convention. Define Span_2(K) as follows:

- objects: objects of K;
- 1-cells A→B: ordinary spans A←L→B;
- 2-cells L⇒V: **isomorphism classes** of spans L←J→V in the category of cones over the fixed endpoints A,B. Every map commutes with both exterior legs.

Thus each hom-category is the ordinary category of spans in that cone category, with isomorphic apex spans identified. Vertical 2-cell composition uses pullbacks over the intermediate apex. Horizontal composition uses the pullbacks defining 1-cell composition. The interchange isomorphism is obtained by reordering the same finite pullback constraints; both sides are limits of the same diagram. After passing to isomorphism classes it is equality. Associativity and units follow by the same finite-limit uniqueness. This constructs a bicategory of 2-spans; it is not simultaneously claiming to retain maps between 2-cell apices as additional 3-cells.

One may restrict the 2-cells to polarized spans L←[E_0]J→[M_0]V. They are closed under vertical composition by the mixed-pullback formula. Horizontal composition preserves these polarities: its positive components use presheaf pullbacks, which preserve isomorphisms of diagrams; its negative components use copresheaf pushouts, which likewise preserve isomorphisms. The restrictions therefore give a well-defined class of 2-cells closed under the bicategory operations.

A polarized 2-cell is equivalently a pair of covariant component maps

    alpha:L+→V+,       beta:L-→V-,
    xi_V(beta(l-),alpha(l+))=xi_L(l-,l+),             (5)

with the required exterior-endpoint compatibility. To construct it, take J+=L+, J-=V- with pairing xi_J(v-,l+)=xi_V(v-,alpha(l+)); its left map has positive identity and negative beta, while its right map has positive alpha and negative identity. Conversely any polarized 2-span is isomorphic to this form. Hence it is determined by alpha,beta. Vertical composition composes alpha and beta: the mixed pullback retains the first positive part and the last negative part.

For (4), these covariant components are exactly

    alpha=(u_P,g):G_P→X_P×_[X_P']G_P',
    beta=[t,v_Q']:T_Q⊔_[H_Q]H_Q'→T_Q'.

**Context-composition coherence.** For P_0⊂P_1⊂P_2 and Q_0⊂Q_1⊂Q_2, use the already proved context-span compositor isomorphisms to identify the composite source and target 1-cells with their direct-context versions. Pasting the two polarized 2-cells has positive component into X_0×_[X_2]G_2 whose projections are u_0 and g_02. Its negative component out of T_0⊔_[H_0]H_2 restricts to t_02 and v_2. Pullback and pushout universality force these to be the direct alpha and beta. By (5), the pasted 2-cell is the direct one. Identity context changes give identity alpha and beta. Longer coherence follows in the same way. Thus the collapsed mixed comparisons form a coherent generally noninvertible naturality family in Span_2(K), with direction C_old;D_R ⇒ D_X;C_new.

This is a second precise formulation alongside §2. It does not assert that every wiring functor F_N lifts to all of Span_2(K): that would require preservation or comparison data for arbitrary pullbacks, beyond the mixed pullbacks proved earlier. The fully joint network/normalization/context law of §2 avoids that extra claim by retaining the variance-aware functor family and its pointwise polarized normalization spans.

## 5. Finite actual-wiring counterexample with distinguishable outcomes

Let C have one object I and endomorphisms {0,1}, with composition and tensor both Boolean conjunction and identity 1. This is a small strict symmetric monoidal category; I is its own dual with cup and cap 1. Its compact trace is the identity on scalars. Put y=C(-,I), also writing y for the corresponding covariant representable when a sign is understood.

Use two primitive cylinders, each with discrete preparation and test labels {0,1} and entries delta_pq (1 when labels agree, 0 otherwise). Their independent parallel wiring has four preparation pairs and four test pairs, with pairing

    delta_(p1,q1) delta_(p2,q2).

This is actual tensor wiring of the primitive scalars, not an inferred global table. The fixed raw carrier W is the tensor of their local free middles. Its signed presheaves are each 4 copies of y, indexed by the four label pairs.

Choose old joint preparations and tests {(0,0)}, and new joint preparations and tests {(0,0),(1,1)}, using their actual inclusion maps into the fixed primitive-product contexts. The new joint observation table is the two-by-two identity table, so the added preparation/test genuinely distinguish an outcome. The raw local contexts and raw carrier remain fixed.

The canonical old middle has signed presheaves (y,y), and the new one (2y,2y). The maps u and v include the selected labelled copies into 4y. Formula (3) becomes

    L=(y, 4y⊔_y2y) ≅ (y,5y),
    V=(4y×_[4y]2y,4y) ≅ (2y,4y),
    J=(y,4y).

There is **no compatible apex map L→V**. Compatibility with the left exterior raw carrier forces its negative component 4y→5y to be the inclusion of the four raw-test copies. Compatibility with the right exterior new canonical middle would then identify the new test's extra pushout copy with the distinct (1,1) raw-test copy. They are different coproduct summands, so equality fails, already at their identity elements.

There is **no compatible apex map V→L** either. The right exterior positive equation would require the identity on 2y to factor through the inclusion of the old single y copy. The identity element in the new preparation copy cannot do so. Allowing scalar 0 in an equivariant presheaf map cannot evade either contradiction: coproduct labels remain distinct even at zero.

Thus actual port wiring and natural context maps do not force exact collapsed interchange; they do not even force a lax or oplax ordinary-span map in either direction. The canonical common-apex comparison (4) still exists: its negative map identifies the extra new-test copy with the corresponding raw-test copy, while its positive map includes the old preparation copy into the two new ones.

## 6. Consequence for the fuller target

The coherent statement now available is stronger than separate wiring and context pseudofunctors: their normalization comparisons are natural over Prep×Test^op and coherent with raw network substitution as double-category squares. Specified interventions remain subject to the actual port/context maps and admission conditions of the preceding theorems.

An overstrong alternative is ruled out: after turning simultaneous two-sided enlargement into one horizontal span, one cannot in general demand an ordinary-map interchange with normalization. One must either keep the two context directions visible, retain the explicit span of apex maps (4) in Span_2(K), or prove additional exactness in a particular model. No extra exactness condition is used in the positive variance-aware theorem, and no undefined feedback, missing joint context, or physical intervention is licensed by this formal comparison.

# I1: exact correlated cuts, tree transport, and interface reflection

31 October 2026. Companion to `framing.md`, `twisted_normal_forms_draft.md`, and the independently presented refinement-coherence theorem. The assertions here concern literal coefficient-labelled, fully typed actual cut trees and retained tuples thereof. They do not identify proofs merely because their total composites agree, and do not supply a syntactic path-coherence theorem by themselves.

## 1. Fixed skeleton and the actual source

Fix the old graph calculus P, one actual fully typed finite cut tree T (or a tuple/forest of these), including every intermediate operation, full ordered profile, graph, partition, interface arrow and repeated occurrence position. Empty input occurrences are retained, but have no coefficient. Every active input occurrence of a vertex is represented by an edge; an edge above a branching vertex is one shared edge, not separately chosen for its children. All assertions below are fibrewise over this entire old record. In the selected ordered-partition calculus a nonempty graph cannot be partitioned into only empty inputs, and nullaries occur only at the empty graph. Consequently every active edge has an active final descendant in every finite actual cut tree.

Let A be a monoid, B a monoid, and α:B→Aut(A) an action, with α_bd=α_b∘α_d. Write C=A⋊α B with (a,b)(c,d)=(aα_b(c),bd). The chosen cyclic group examples satisfy these assumptions. B projection is a monoid map; A projection generally is not. Inversion action with a of order ≥3 gives π_A((1,s)(a,1))=a^−1 rather than a.

For every active edge e label it (a_e,b_e). Let β_e be the ordered product of the b-labels on edges strictly above e, with empty product 1. Define

    t_e=α_(β_e)(a_e).

For a root-to-final-active-leaf path e_1,…,e_k, expansion of the semidirect product gives

    product_C (a_e,b_e) = ( t_e1 … t_ek, b_e1 … b_ek ).                 (1)

Thus, for a prescribed ACTUAL root coefficient tuple (x_l,y_l), the map

    ((a_e,b_e))_e ↦ (((t_e))_e,((b_e))_e)

is a bijection

    W_C(T,(x,y)) ≅ W_A(T,x) × W_B(T,y),                              (2)

where W denotes exact branch-product solutions on this fixed tree and source. Its inverse first uses the ENTIRE B tree to compute each β_e and then sets a_e=α_(β_e)^−1(t_e). No choices are made per child for a shared edge. This is a twisted, B-dependent coordinate bijection, not a pair of calculus projections. In particular the ordinary A-coordinate arrays of the original factors are not the A witness on the right of (2).

For one cut, with shared outer (a_i,b_i) and inner (c_ij,d_ij), this specializes to

    x_ij=a_i α_(b_i)(c_ij),  y_ij=b_i d_ij;
    outer A=a_i, inner A=t_ij=α_(b_i)(c_ij).

These equations hold simultaneously for every j. Conversely any exact B cut and exact transported A cut at x determine the unique joint cut. Proof of (1) is induction on path length, using the action law and multiplicativity of each α_b. Proof of (2) is then pointwise inversion of α_(β_e), with every intermediate factor retained. The selected old geometry ensures that every active edge lies above an active final leaf; empty nullary positions carry no coefficients.

## 2. Retained intermediate entries, insertion, and flattening

For a subtree with incoming ancestor B product γ, its intrinsic t-coordinates are computed with prefix reset to 1; the coordinates in the ambient tree are α_γ of all these intrinsic A-coordinates. Its original intrinsic composite is recovered, not discarded, by applying α_γ^−1 to each ambient composite A label. The intrinsic B composite is unchanged. This applies separately to EVERY retained forest entry, including intermediate operations with repeated positions. The tree plus both full edge arrays therefore recovers the complete original factor record and all intermediate composites, not merely the root operation.

**Insertion.** Suppose an edge label (a,b) is refined to a subtree whose intrinsic composite at that occurrence is (a,b). With ancestor prefix γ, apply α_γ to every intrinsic transported A label of that subtree. Its path products are α_γ(a), exactly the old transported edge label. The inserted B path products are b. All prefixes below insertion are consequently unchanged. The same γ is used for every descendant. Insertions at disjoint occurrences commute because their records are disjoint; nested insertions commute because α_γ α_δ=α_(γδ). This is a constructive naturality proof, not a claim that insertion is coordinatewise without twisting.

**Contraction/flattening.** Contract two successive active labels (a,b),(c,d) to (aα_b(c),bd). If the ancestor prefix is γ, their transported A labels multiply as

    α_γ(a) α_(γb)(c)=α_γ(aα_b(c)),

and B labels multiply to bd. Hence contraction agrees with ordinary multiplication in the transformed arrays. Branching contraction uses the SAME first factor for every child. Associativity of A and B makes any parenthesization give the same arrays. Nullary/inactive boundaries simply retain the old empty positions and the intermediate factors required by the actual record; no final label is invented.

A flattening map may intentionally forget an internal factorization; it is not injective. Naturality means the corresponding square commutes, NOT that intermediate factors may be omitted from the comparison invariant. To compare retained certificates, apply (2) to every retained entry and demand agreement on every common edge/operation, using the prefix-reset formula above. Two literal coefficient certificates match iff these entire compatible arrays match over the identical old certificate. Any quotient of proof paths additionally needs the independent presented-coherence theorem.

**Quotient observations.** Exact B edge records and exact common skeleton suffice to untwist A matches. If B is observed only through a class, the retained A predicates must be invariant under all action differences allowed by that class, and joint shared-parent choices must still match. Separate existential matches do not imply a common joint witness. Nothing here asserts coarsest-repair reflection via π_A or numerical/multiplicity transfer after quotienting.

## 3. Embedded modules: preservation versus filtered reflection

An injective monoid map i:D→C preserves every actual cut/refinement record entrywise and reflects equality of records whose factors all lie in i(D). Consequently

    W_D(T,z) ≅ {w∈W_C(T,i(z)): EVERY retained factor label lies in i(D)}. (3)

The inverse applies i^−1 to every factor. This is exact all-local-factor filtered reflection; it does not exclude other mixed witnesses from the ambient calculus. A declared module-pure syntax must retain membership provenance, especially when the two images overlap. Membership tags certify a specified factor is allowed from a specified module; forgetting tags or projecting support is not a proof of purity.

Unrestricted fullness is false already for the semidirect group case: the A-local unit has ambient factorization (1,s)(1,s^−1). For a nontrivial A, the B-local unit likewise has (a,1)(a^−1,1). In repaired M_m=A_m∪{u}, the A-local p has ambient cut p=cu, but u∉A_m. These are actual unary cuts, extendable through the old graph calculus at any nonempty color.

A sufficient and, for unrestricted binary unary cuts, necessary extra condition is factor closure:

    xy∈i(D) ⇒ x,y∈i(D).                                            (4)

Binary induction gives fullness for every finite actual cut tree here, since every active edge has an active final descendant. This statement uses the selected ordered-partition geometry; in a different calculus permitting erased active edges, factor closure alone would not constrain the erased labels. Formula (3) does not need factor closure.

Old label-blind existence is preserved and reflected independently: any allowed old skeleton has a decorated witness at every prescribed root tuple by putting unit labels on internal edges and the prescribed labels at final active leaves. Forgetting coefficients maps any decorated witness back to its actual old witness. This statement does not say all ambient labelled witnesses are local.

## 4. Interface maps: explicit finite algebra and geometry tests

For coefficient maps f:A→A′ and g:B→B′, the pair F(a,b)=(f(a),g(b)) is a semidirect homomorphism provided

    f(1)=1, f(ac)=f(a)f(c), g(1)=1, g(bd)=g(b)g(d),
    f(α_b(a))=α′_(g(b))(f(a))  for every a,b.                         (5)

For finite tables these are finite explicit tests. They are also necessary for a pair map to be a homomorphism, by evaluating pure-channel products and (1,b)(a,1). Thus equivariance is not an optional naturality assumption. For a family of interface arrows, additionally check identities and composition on coefficient maps. On the old calculus check each generator's full source/target profile, ordered occurrence map, active/empty status and grade/interface geometry, and check every defining old relation and restriction/substitution square. A proposed coefficient restriction cannot repair a failure of the old geometry square.

If (5) and the old squares hold, F preserves products, cut equations, insertion, and all retained entries. Its compatibility with transported coordinates follows from fα_β=α′_(gβ)f. Preservation alone does not reflect cuts.

**A finite lifting test stronger than just binary factor lifting.** For any finite monoid map h:D→E and target outer factor q∈E, define for each x∈D and r∈E satisfying h(x)=qr

    L(q;x,r)={p∈D : h(p)=q and there exists v∈D,
                            h(v)=r and pv=x}.

At a shared-parent cut with root tuple (x_j) and prescribed target inner factors r_j, an exact lift exists iff

    intersection_j L(q;x_j,r_j) is nonempty.                        (6)

Necessity and sufficiency follow by choosing the single p in the intersection and then each v_j. This is the exact correlated condition, not independent nonemptiness of the individual L sets. Because there are at most |D||E| different pairs (x,r), arbitrary arity requires only finitely many distinct intersections per q. No coefficient condition is needed at empty/nullary occurrences in the selected calculus. Trees lift recursively: first choose the outer label and roots of the child entries by (6), then lift each child's prescribed target cut at that chosen source root. Hence these finite tests imply all finite-tree lifting, with every intermediate factor retained. Conversely failure of an intersection supplies the corresponding finite star counterexample whenever that star is allowed in P. For restricted graph arities, use exactly the realizable tuples; the all-tuples test is a finite sufficient test without pretending every star is geometrically realizable.

For interfaces with nontrivial old restrictions, coefficient lifting must be combined with an actual old fixed-source cut lift and compatible ordered active occurrence maps. An old isomorphism has this automatically. A noninvertible geometry map needs its own lifting result; it is not licensed merely by (5). Factorwise injectivity gives uniqueness/reflection of equality, not existence. These distinctions replace any unproved assertion that an arbitrary comparison is invertible.

**Useful noninvertible positive case (groups).** If h:G→H is a surjective group homomorphism, every set L(q;x,r) above equals the full nonempty fibre h^−1(q): for any p in that fibre choose v=p^−1x, which satisfies h(v)=q^−1h(x)=r. Thus every shared-parent intersection passes, for every arity and fixed source. Recursive tree lifting gives existential cut reflection without assuming invertibility; lifts need not be unique. For the inversion semidirect groups, if d divides n then reduction f:C_n→C_d and g=id_C2 satisfy (5) and give such a surjection C_n⋊C_2→C_d⋊C_2. This is a genuine noninvertible positive interface coefficient restriction when d<n, combined with an old geometry isomorphism. It preserves all intermediate target labels through chosen lifts, but does not identify different lifts, prove proof-path injectivity, or preserve arbitrary module-membership tags automatically. More generally a homomorphism between groups has unrestricted coefficient cut lifting at every fixed source iff it is surjective: necessity follows from the target unit factorization 1=q q^−1 at source 1 for each q∈H.

**Positive nontrivial transport.** In the repaired M_m family, any permutation σ of ordinary coordinates [m], fixing *,z, induces hσ(y_S)=y_(σS), fixing 0,1,e,c,u. This is induced by conjugating the actual partial maps on the boundary {*,1,…,m}⊔{z} by the permutation fixing *,z. It is a monoid automorphism, checked directly from the displayed multiplication table, with inverse h_(σ^−1). For the general pushout Q_I of the companion theorem it carries the collapsed ideal {y_S:S⊆I} to {y_T:T⊆σI}, and hence induces an isomorphism Q_I→Q_(σI), again bijective on all literal cut records. Along any old full-profile geometric isomorphism it yields literal cut/tree bijections. In semidirect examples, group automorphisms f,g satisfying the finite equivariance table give the same result. For A=C_n, B=C_2 with inversion, f(a)=a^k for gcd(k,n)=1 and g=id satisfy (5), including nonidentity f when available. Merely choosing arbitrary group homomorphisms does not suffice: for C_3 inversion, f=id and g:C_2→C_2 trivial fail (5) at (s,a), since a^−1≠a. Repair g to id or choose an actually equivariant f.

## 5. Sharp coordinate-deletion boundary in the repaired bare pushout

Distinguish the interface parameter of the pushout theorem from the following coordinate restriction J⊆[m]. Let M_J be the same repaired partial-map monoid on ordinary coordinates J. The map

    h_J:M_m→M_J, y_S↦y_(S∩J), fixing 0,1,e,c,u,

is a surjective monoid homomorphism. This is restriction of these actual partial maps to the subinterface {*,elements of J}⊔{z}; the identity goes to the identity of that smaller interface. Intersections commute with restriction; all mixed products with e,c,u are independent of S, so every multiplication-table case is respected. Equivalently no map in this particular palette travels through a deleted ordinary coordinate to another retained point. This last property is special to this palette, not a generic theorem that arbitrary partial-map restriction preserves composition. Restrictions compose strictly: for K⊆J⊆[m], h_(K⊆J)h_J=h_K, by (S∩J)∩K=S∩K and equality on the other generators. They preserve the common C embedding d↦p, fixing c,e,0 and sending identity to the smaller identity. Thus this is an actual coefficient-boundary interface change preserving cuts, not an informal renaming.

If J is proper, choose k∉J. The source y_{ {k} } is not p but its image is p. The target has cut p=cu. Since h_J^−1(c)={c} and h_J^−1(u)={u}, its only candidate lifted factors multiply to cu=p, not y_{ {k} }. Therefore even unary binary cut lifting fails at this specified source. In particular **unrestricted all-root cut lifting holds iff J=[m]**, including m=0. Sufficiency is the identity; necessity is the deleted-singleton counterexample. More generally every nonempty fully erased S gives the same failure at y_S. This proves the advertised all-root criterion; it does not assert a full classification of restricted-root or quotient-observation lifting.

Repair options are explicit: retain all coordinates (permutations remain allowed); restrict transfer to the forward direction or to a verified liftable cut language; or change the source/target specification with permission. Replacing y_S by its support restriction while silently demanding all target cuts lift is not a repair. In particular it conflates equation preservation with existential cut reflection and destroys the module-purity information relevant to (3).

Coefficient-boundary maps here are distinct from the old graph-grade/interface category. One may hold the old P geometry fixed (identity old parameter functor) while changing this partial-map boundary; all nonidentity old interfaces remain shared and act as already specified in P. Combining both changes requires the separate old geometry squares of §4, not an identification of the two notions of interface.

## 6. Deliverable boundary

Established here: source-fixed exact twisted tree bijection; correlated shared-parent equations; retained-entry insertion and contraction naturality; faithful all-local-factor reflection with foreign-cut counterexamples; finite equivariance and shared-parent lifting checks; nontrivial positive interface automorphisms; exact coordinate-deletion failure and repair. The separate refinement worker must identify these literal retained records with the independently generated presented refinement category before claiming full proof-path coherence. No unrestricted D2/E descent, optimality theorem, or arbitrary interface cut reflection is inferred.

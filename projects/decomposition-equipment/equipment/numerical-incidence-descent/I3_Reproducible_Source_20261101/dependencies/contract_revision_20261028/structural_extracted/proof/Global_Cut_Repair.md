# All degree exact cuts and the repaired rooted module

Author proof, 25 October 2026. Editorial delivery copy: current mathematical scope and review status are in [ScopeAndStatus.txt](../../../../../../../foundations/witnessed-cut-coherence-proofs-and-sources/ScopeAndStatus.txt). Original and delivered hashes are recorded in SourceManifest.txt. Preliminary-target, companion-proof and status references have been normalized; mathematical proof content is unchanged. This proves two DIFFERENT structures and their explicit action comparison. It does not put arbitrary nonexact root operations into one simplicial object by inventing unavailable outer restrictions.

Inputs are the concrete graph-span-globalM virtual equipment; the induced-upward activation quotient Q_I; and the original ordered induced-restriction identity. The quotient/finite local scheme and memory-bound proofs are in GraphDependent_Quotient_and_Cut_Memory.md. Parameters are N>=6, an arbitrary finite commutative M, and any induced-upward set I of ordered graphs through size N. Interface sets are FIXED under groupoid morphisms. Actual endpoint-preserving span bijections, not support-equivalence isomorphisms in Q_I, are the isomorphisms used for cut certificates.

## 1 Exact interval records in every degree

For n>=0, an object of X_n consists of:

* a list of finite interface sets A0,...,An;
* an ordered graph G of size at most N and an ordered partition (U1,...,Un) of its vertices, with empty blocks allowed;
* for every 0<=i<=j<=n a finite span S_ij:A_i->A_j, with S_ii the chosen diagonal identity span I_(A_i);
* for every i<=j<=k an endpoint-preserving BIJECTION

      psi_ijk : P(S_ij,S_jk) -> S_ik.

The repeated-index maps are the actual canonical unit maps: psi_iij(a,s)=s, psi_ijj(s,a)=s, and psi_iii(a,a)=a. For every i<=j<=k<=l require

    psi_ikl(psi_ijk(x,y),z)
      = psi_ijl(x,psi_jkl(y,z)),                        (1.1)

on every compatible triple, with the canonical tuple reassociation understood. This is a literal equation on functions. The graph attached to interval ij is the induced graph on U_(i+1) union ... union U_j, in increasing coordinates; it is not independent data.

A morphism fixes ALL A_i, G and the actual U_i. It is a family of endpoint-preserving span bijections h_ij, h_ii=id, such that

    h_ik psi_ijk = psi'_ijk P(h_ij,h_jk).              (1.2)

Composition is componentwise. Hence X_n is a groupoid. There are no interface-bijection morphisms. Every coefficient triangle has scalar 1. Arbitrary M remains in the ambient equipment and in the outer cells of Section 6.

For n=0, the zero-block partition forces G empty, so X_0 is the DISCRETE groupoid of finite interface sets. For n=1, X_1 is the groupoid of a retained ordered graph and a finite span, with actual endpoint-preserving span bijections.

## 2 Every face and degeneracy, with strict simplicial laws

Let alpha:[m]->[n] be ANY monotone map. Put

    V = union_{alpha(0)<r<=alpha(m)} U_r,
    G' = G|V,
    U'_j = i_V^(-1)(union_{alpha(j-1)<r<=alpha(j)} U_r),
    A'_j = A_(alpha(j)),
    S'_(ij) = S_(alpha(i),alpha(j)),
    psi'_(ijk) = psi_(alpha(i),alpha(j),alpha(k)).       (2.1)

The weakly increasing triple indexing in Section 1 ensures that (2.1) remains meaningful when alpha repeats vertices. Its unit and associativity equations are inherited verbatim. Morphisms are restricted by the same indices.

For alpha the inner coface omitting i, formula (2.1) merges the adjacent graph blocks and retains the corresponding longer-interval span. For the first or last coface it removes the exterior graph block, takes the induced graph on the remaining vertices, and retains the proper-interval spans. These are actual OUTER face definitions. A codegeneracy repeats A_i, inserts an empty graph block and the diagonal span I_(A_i), and uses the specified unit bijections.

If beta:[l]->[m], the selected vertex subset for beta after alpha is the inverse image under increasing enumeration of the subset selected by alpha beta. The original induced-restriction identity says

    (G|V)|W = G|i_V(W),
    i_(i_V(W)) = i_V i_W.

Thus the graphs and ordered partitions obtained in the two ways are literally equal. Span and psi indices compose literally. Consequently X(beta) X(alpha)=X(alpha beta), and identities act as identities. This proves ALL simplicial identities, including repeated endpoint degeneracies and constant maps. There is no truncation in degree.

## 3 The all triangulation 2 Segal theorem

Fix a triangulation T of the polygon with vertices 0,...,n. Its target comparison groupoid L_T is the homotopy fibre product of one copy of X_2 per triangle over the shared copies of X_1, with endpoint data in X_0. Concretely its objects are triangle records together with specified actual span isomorphisms identifying common diagonal edges. Graph/interface matching is literal because those parts of the morphisms are discrete. Its morphisms are compatible families of the triangle-record isomorphisms. Restriction defines

    R_T:X_n -> L_T.                                    (3.1)

We prove (3.1) is an equivalence for every n and every T.

First the graph part has an explicit unique gluing procedure. The unique triangle adjoining the long edge (0,n) has third vertex k. Its whole graph is the retained G and its two blocks divide the vertices into U_left,U_right. The two subtriangulations carry cuts of the INDUCED graphs on those actual subsets. Inductively reconstruct their ordered subpartitions and lift them through the increasing inclusions. Concatenating gives the unique full ordered n-block partition. Cross-edges between the two subsets are retained in the root triangle's G and are never reconstructed from the pieces. This is the standard graph restriction-species reconstruction, here given explicitly rather than assuming cross-edge recovery.

For the coefficient part, consider any X_n object and set P_ij=P(S_(i,i+1),...,S_(j-1,j)). Iterating psi along a left comb gives a bijection d_ij:P_ij->S_ij. Equation (1.1), by induction on interval length, makes it independent of rebracketing, including unit intervals. Thus an X_n object is isomorphic to the canonical interval record formed from its principal spans by taking S_ij=P_ij and all psi to be tuple flattenings. A family of principal-span isomorphisms extends UNIQUELY to all interval spans, by

    h_ij = d'_ij P(h_(i,i+1),...,h_(j-1,j)) d_ij^(-1). (3.2)

Now start with an object of L_T. Use its given shared-edge isomorphisms to transport triangle data to common representatives for shared diagonals; this is an isomorphism in the explicit homotopy fibre product, not an assumption that different spans were equal. Induction on the root triangle (0,k,n) constructs comparison bijections from the flat principal-span composites to every triangulation edge. The root triangle's psi defines the comparison on (0,n), and the two subtriangulations supply the comparisons on its sides. These comparisons give an isomorphism from the restriction of the canonical full interval record to the specified triangle data. Hence R_T is essentially surjective.

A morphism between two such restrictions is determined on every diagonal by its values on the principal edges, since each triangle has an invertible psi. Induction on the same triangulation gives this determination. Formula (3.2) then extends it uniquely to a morphism of full interval records. Thus R_T is fully faithful. This proves (3.1).

For unitality, let e_i:X_(n+1)->X_1 select its i-th principal edge and let u:X_0->X_1 select (empty graph,I_A). The degeneracy s_i gives an equivalence

    X_n -> X_(n+1) times^h_(X_1) X_0.                 (3.3)

Indeed an object of the right side has that graph block empty and a SPECIFIED endpoint-preserving isomorphism of its edge span to I_A; the interface endpoints are the same literal A. Delete the repeated boundary and use this isomorphism with the adjoining psi maps to compare the object to the inserted-unit record. All other interval maps are uniquely transported by (1.1). The reverse deletion/insertion comparisons are inverse by the unit formulas and (3.2). This proves the unit comparison for every position, including the endpoints. Equations (3.1) and (3.3) establish the claimed unital 2-Segal groupoid.

The graph gluing and span representability/coherence used here are baseline mathematics. The nonbaseline quotient claim is not that their product was newly discovered; it is the precise failure and minimum repair of their cut data under graph-activated thinning.

## 4 Original discrete finite typed recovery

Fix the original finite K and faithful tagged F. In X_n take S_ij to be the graph span of F(h_j...h_(i+1)) for an actual composable path h_1,...,h_n in K. Take every psi to be the unique endpoint-compatible composite graph-span bijection. This gives a simplicial map from the original M=1 graph-cut object to X.

All faces agree: inner faces compose the actual K arrows, outer faces retain the corresponding subpath and induced graph, and degeneracies insert actual identity arrows and empty blocks. A morphism of graph spans fixing the endpoints must be the identity on its left-coordinate witness; hence every automorphism in this slice is trivial. If two original paths produce the same span data, tagged interfaces agree and faithfulness of F recovers every arrow. Thus the map is degreewise fully faithful and its image is discrete, with exactly the original graph-cut witnesses.

For fixed N and finite K, each such degree has finitely many graphs, ordered block assignments and arrow strings. Degenerate degrees are unbounded, but each degree is finite. This is an all-degree mathematical recovery statement; it does not replace any separately mandated finite exhaustive verification or acceptance process.

## 5 Exact operations represented by X and the action domain

Let E_ex be the normalized coefficient-exact typed calculus: components are single graphs with finite spans; an operation is a full graph-cut partition with an ACTUAL coefficient bijection and scalar 1. Substitution preserves bijectivity and the normalization, so E_ex is a genuine typed nonsymmetric calculus. Its morphism groupoids allow actual endpoint-preserving span bijections, fixing graph/interface data. We do not call its graph cut cells equipment-opcartesian: cross-edge assemblies need not be universal.

An X_n record gives an exact operation by iterating its psi to the full coefficient map P(principal spans)->S_0n. Conversely, an exact operation extends to a full X_n record by choosing every proper interval span to be its flat principal-span composite and transporting the root maps through the given full bijection. Equations (1.1) hold by tuple associativity. Formula (3.2) proves that the groupoid of these extensions is contractible. Thus X is an all-degree coherent presentation of THESE exact operations, not an unrelated comparison object.

The full quotient Q_I, including all global scalar values and all nonexact coefficient classes, is a right module over E_ex by its original occurrence-wise substitution: substitute the supplied actual exact operations, then apply Q_I. This action is well-defined because Q_I is a substitution quotient. The next sections lift this action to the retained cut groupoids and specify every tree map.

## 6 Repaired factorization groupoids over arbitrary outer cells

Fix a full quotient operation a with source path p=(P1,...,Pn), retained partition (U1,...,Un) of G, output (G,S_R), outside boundary maps and scalar m. Let T be a finite planar rooted tree with that full occurrence-indexed frontier. Every internal edge v determines a consecutive LEAF RUN, possibly empty at a specified boundary occurrence. Its graph is forced to be G|U_v, where U_v is the union of the corresponding actual leaf blocks. The inner graph partition is the canonical pullback of its ordered child subsets.

An object of D_T(a) assigns a finite span S_v to every proper internal edge and an ACTUAL endpoint-preserving coefficient bijection

    beta_v:P(children spans)->S_v                      (6.1)

to each nonroot vertex, scalar 1. Leaves carry the fixed original spans. The root carries a quotient coefficient class gamma of scalar m whose composite with the inner cells is a. At inactive G_v, beta_v is already present in the quotient cell; at active G_v it is the added certificate. The root's forgotten map is NOT restored. Morphisms are tuples of actual endpoint-preserving bijections h_v, identity at leaves and root, with

    h_v beta_v = beta'_v P(h_children)                 (6.2)

at every proper vertex, and the quotient root equation. All scalar morphisms are 1.

There is an explicit canonical object: use the flat leaf-subpath composite for each S_v; use tuple flattening for beta_v; and use a composed with root tuple flattening for gamma. This is independent of the representative of a: an inactive root retains its map, and an active root identifies all available coefficient maps with that same partition and scalar.

Given any object, recursively invert its beta maps to obtain an endpoint-preserving bijection delta_v:S_v->P(leaf subpath). Its formula is

    delta_v = flatten . P(delta_children) . beta_v^(-1),

with the canonical one-leaf and empty-run conventions. These delta_v satisfy (6.2) and carry the object to the canonical one. The root equation follows from the stipulated flattened composite being a. Conversely (6.2), with the leaves fixed, forces delta_v inductively. Thus every object has a UNIQUE isomorphism to the canonical object. D_T(a) is nonempty and contractible.

This argument retains every old empty/repeated occurrence and does not confuse the root scalar m with inner unit labels. It works for every m in any finite commutative M, including nonunits. It does not say that factorizations with arbitrary nonunit INNER labels are unique.

## 7 Actual contractions, splittings, rotations and units

If a proper child vertex v of w is contracted, replace its slot at w by its entire ordered child list and discard S_v. When w is nonroot replace its coefficient map by

    beta_new,w = beta_w T_(...,beta_v,...),             (7.1)

where T is the actual tuple-substitution map. It is a bijection. At the root use the quotient class of gamma T_(...,beta_v,...). On morphisms discard h_v. Equation (6.2) and functoriality of tuple substitution prove the remaining compatibility equations. Thus this is an actual functor c_*:D_T(a)->D_(T/v)(a).

For a reverse split of a selected consecutive child run, insert its canonical tuple-composite span, the identity/flattening inner bijection, and adjust the parent's map by the inverse tuple regrouping. This is a functor s_*. Contract-then-split and split-then-contract have the explicit comparison at the new edge given by its retained beta_v; all other edge comparisons are identities. These are mutually inverse natural comparison isomorphisms, by (6.2). In particular each c_* is an equivalence.

Unary insertion uses the same span and its canonical one-factor tuple bijection. Genuine nullary-unit insertion uses the EMPTY RUN at its named boundary, the diagonal span I_A, graph empty, and its identity coefficient. It is not the deletion of an arbitrary empty-graph component or arbitrary nullary primitive. The parent map is adjusted by the tuple unit bijection; contraction reverses it.

Two nested contractions compose the same tuple-substitution function, as do two disjoint contractions. The original induced-restriction identity gives the identical vertex-subset lifts. Therefore all contraction composites agree after the explicitly prescribed tuple reassociations. The same calculation proves the contraction/insertion unit laws. A rotation is the specified zigzag that contracts the middle edge of either bracketing to their common flatter tree and applies the canonical split on the other side. Its natural comparisons are the retained beta maps just described.

Every finite diagram of such rotations, contractions, splittings and genuine unit insertions commutes: the constructed comparison at each object is a morphism satisfying (6.2), and such a morphism is unique once its leaves and root are fixed. This uniqueness is used only AFTER all functors and their actual comparisons have been constructed. It is not an argument that unspecified higher operations exist because a groupoid is contractible. In particular it proves pentagon and higher associahedral coherence in every arity and depth.

## 8 Exact graft action and its compatibility with X and Q_I

Let b_i:q_i->P_i be normalized exact operations with ACTUAL coefficient bijections. Choose any fully exact factorization trees for them; these include their actual root bijections, not merely root quotient classes. Graft these trees at the corresponding DISTINCT leaf occurrences of an object of D_T(a). All former leaves P_i become proper internal edges; their new maps are exactly the supplied bijections for b_i. All new proper inner maps are actual bijections, and the outer root class remains the original gamma. The composite quotient operation is a[b_1,...,b_n]. This defines a functor

    D_T(a) times product_i E_(T_i)(b_i)
      -> D_(T[T_i])(a[b_i]),                           (8.1)

where E_(T_i)(b_i) is the fully exact factorization groupoid of the fixed exact operation b_i. Morphisms glue their actual span isomorphisms; the matching P_i boundary is retained, not guessed from equality of a component name.

Associativity of (8.1) is ordinary occurrence-wise tree grafting together with tuple-substitution associativity. The graph coordinate equality is the exact identity for iterated induced restrictions. Unit grafts are the identity operation, with the canonical unary tree, and the nullary unit case is handled by the actual empty-run convention of Section 7. Thus (8.1) supplies an actual coherent rooted right-module action.

By Section 5 every exact b_i and its coherent factorization data are represented by X, with contractible choices of full interval extension. Replacing one such extension by another changes (8.1) by its unique explicit compatible span isomorphism. Consequently the action is the action of the exact cut object X in its operation presentation; A and B are not independent products placed side by side.

Forgetting the certificates and flattening sends (8.1) to the original Q_I substitution EXACTLY. Contracting inside a grafted tree before or after grafting produces the same quotient operation and the same coefficient composite; its certificate comparisons are those of Section 7. This gives the promised cut/graft/quotient compatibility in every finite tree.

## 9 Arbitrary nonexact grafts and the direction of their comparison

Here occurrence-wise grafts are GLOBULAR at each original leaf: every child full profile has exactly that occurrence's endpoint interfaces. Nonidentity interface changes are the separate operation of Section 10. Now let b_i be arbitrary such Q_I witnesses, possibly with nonunit scalar n_i and nonbijective or forgotten coefficient map. Each has a canonical coefficient factorization in the concrete model: first cut into its new source blocks with intermediate span equal to their flat tuple composite and coefficient identity, then a unary comparison to its old output span with the supplied coefficient class and scalar n_i. The first cell is normalized exact. The second need not be invertible.

Given an old factorization object over a, construct the new normalized factorization over a[b_i] by replacing each proper intermediate span with the flat composite of the REFINED leaf spans below it. Its inner maps are tuple flattenings. There are comparison maps pointing

    k_v : NEW flat refined-subpath span -> OLD S_v.    (9.1)

At an old leaf, k_i is the coefficient of b_i. Inductively at an old proper vertex,

    k_v beta'_v = beta_v P(k_children).                (9.2)

Here beta'_v is the new canonical bijection, so (9.2) defines k_v. Its scalar is the product of the n_i below that occurrence. The root equation in Q_I is

    gamma_new = gamma_old P(k_children(root)),        (9.3)

with scalar m times product_i n_i. This is a commuting witness diagram, not an assertion that (9.1) is an isomorphism.

If an active b_i has no retained actual representative, choose one only to calculate (9.1); its QUOTIENT class is independent of that choice. Indeed every ancestor graph containing that active induced child is active, so every affected ancestor coefficient map is also forgotten. At inactive children the map is already uniquely specified. Thus (9.1)-(9.3) are canonical quotient comparisons. They are not canonical ACTUAL witness maps without the extra representative data.

For two successive graft refinements, the composite of the corresponding k maps equals the map obtained by the single composed graft, after the fixed tuple regrouping. This follows by induction from (9.2), functoriality of P, associativity of the beta substitution, and multiplication of the retained scalars. The root equality follows from (9.3). Repeated equal leaves remain separately indexed throughout. Hence the construction is coherent for arbitrary generated refinement forests and agrees with their actual occurrence-tuple composition, not merely their endpoint operations.

The supplied graft tuple remains PART OF THE ACTION AND COMPARISON DATA: every child full profile, local scalar, empty-run label and occurrence index is retained. Normalizing the resulting cut object can act nonfaithfully on these tuples. Equality of normalized root operations, or equality of the aggregate product of scalars, does NOT imply equality of refinement arrows. The old-tuple conservation theorem is a separate statement and is not inferred from normalization.

The maps in (9.1) are AMBIENT TYPED DIAGRAM COMPARISONS, not morphisms inside D_T(a): the graft changes the leaf profile and generally the root operation, and their scalar products need not be 1. An actual PREQUOTIENT unary comparison is invertible exactly when its representative span map is bijective and its scalar is a unit. Even then a nonidentity unit scalar does not turn it into a morphism of the scalar-1 groupoids D_T defined here. The exact graft action (8.1) applies to the normalized scalar-1, actual-bijection case. Extending D_T to a scalar-gauge doctrine would require a separately stated construction.

An active quotient support-isomorphism alone does not supply the actual bijection required by a cut certificate. These invertibility tests concern the SUPPLIED comparison maps and base-indexed diagrams, not the mere existence of an abstract equivalence between fixed D fibres. Indeed every functor between two nonempty contractible groupoids is an equivalence; that categorical fact cannot recover a lost witness or make a nonbijective k_v invertible. This is the precise boundary between the exact action (8.1) and the general lax comparison (9.1).

## 10 Noninvertible interface change and cut transport

First let the source path have length n>=1, and let f_i:A'_i->A_i be finite maps along it. Reindex each source span at its two endpoints. There is a canonical map

    c_f : P(reindexed source spans)
       -> reindex_(f_0,f_n)(P(source spans)),          (10.1)

which forgets the chosen lifts of the intermediate interface values. A target witness tuple with internal values a_1,...,a_(n-1) has fibre

    product_(0<i<n) f_i^(-1)(a_i),                    (10.2)

provided its endpoint lifts are the specified ones. Thus (10.1) is bijective exactly when EACH FEASIBLE tuple has exactly one compatible lift. For n>=1, empty support and empty INTERNAL products are included; no surjectivity converse is asserted when the feasible support is empty. The nullary case is different and is handled next.

For n=0 there is one interface map f:A'->A and the comparison is

    I_(A') -> (f,f)^* I_A,
    x |-> (x,x),                                      (10.3)

whose target apex is A' times_A A'. Over an endpoint pair (x,y) with f(x)=f(y), its fibre is a singleton when x=y and EMPTY otherwise. Thus (10.3) is bijective exactly when f is injective, including the empty-domain case. There is no 'empty product of internal fibres' shortcut for a nullary path: the two lifted endpoint coordinates need not coincide. Noninjective changes therefore fail to preserve nullary/unit certificates even when there is no internal interface to check. Even if the empty graph is active, this diagonal is NOT a quotient support-isomorphism unless f is injective: the off-diagonal endpoint pairs lie in the target support but not the diagonal source support.

For a tree use the n>=1 construction at every nonempty interval/run and the separate diagonal comparison (10.3) at every nullary unit. Here a node's child spans are the ACTUAL COMPOSITE spans determined by its subtree. The quantifier ranges over every relevant interval composite and its full feasible assignments, not merely over adjacent pairs of the original primitive spans. Primitive-pair-only checks do NOT suffice.

For example let A0=A3=1 and A1=A2={0,1}; let the three primitive spans each have one witness following the path 1 -> 1 -> 1 through the two internal interfaces. Let both f1 and f2 select 0, and leave the outside endpoints unchanged. Each length-two comparison is empty-to-empty after its exterior internal endpoint is restricted to 0, so both primitive adjacent-pair tests are vacuously bijective. The full length-three target composite still has its original witness, while the composite of all individually restricted spans is empty. Its comparison is empty-to-singleton and fails. Testing the actual composite child spans at the next tree node, or directly testing the full feasible interval, detects the failure. It is computable from the actual span-leg tables and retained occurrence assignments. Restriction of an actual beta is a bijection, but the composite-of-restrictions comparison (10.1) may not be. If every local comparison needed by a tree is bijective, INCLUDING every nullary diagonal comparison (10.3), the restricted beta maps composed with these comparisons are actual bijections, so all certificate objects and morphisms transport. The commuting equations follow by explicit tuple projection. Two successive interface changes forget the intermediate lift coordinates in either order and give the same map; when these maps are bijective their inverses give the same certificate transport. This proves its all-tree coherence and compatibility with the exact action on precisely this admissible class. Any claim of compatibility with all unit insertions/degeneracies must also satisfy (10.3); a noninjective interface map is not automatically admissible simply because all nonempty-path support checks pass.

All finite maps still admit ambient cartesian restrictions. We have NOT declared (10.1) invertible for all of them. Moreover Q_I's support-level invertibility at an active graph is weaker than (10.2): it only asks for some lifted witness over every supported external endpoint pair, not a lift of each individual old tuple. Therefore that quotient isomorphism does not transport a retained actual beta.

A concrete mixed negative control uses three singleton graph blocks and a whole graph with one cross-edge joining the first and third blocks. The whole graph is active for contains-an-edge, while the first-two-block induced graph is inactive. Start with singleton spans and singleton interfaces; reindex their shared first internal interface along 2->1. The corresponding first-two-block composite comparison is 2->1, so it is neither bijective nor an isomorphism at the inactive intermediate. At the active WHOLE the comparison has the same nonempty endpoint support and becomes invertible in Q_I. Thus root-level quotient exactness does not imply the inner-cut certificate can be transported. A required theorem must test the actual intermediate cut graphs, not merely the observed whole.

## 11 Relation to the sharp memory theorem and information preservation

The naive groupoid C_T(a) of GraphDependent_Quotient_and_Cut_Memory.md omits beta_v exactly at active proper nodes but RETAINS ACTUAL prequotient span-isomorphism arrows. It is NOT the intrinsic isomorphism groupoid of Q_I: at an active graph, Q_I identifies parallel coefficient maps, including distinct actual span automorphisms. Thus the S_n obstruction and the repair bound concern this expressly retained-symmetry/provenance doctrine. An intrinsic thin quotient may admit a different coherent factorization theory by forgetting that information; no impossibility claim about every conceivable cut theory is made. Upward activation makes active nodes root-connected. Its actual-isomorphism stabilizer is the product of the endpoint automorphism groups of those active proper spans. D_T(a) restores precisely the missing beta_v and imposes (6.2) everywhere. Sections 6–8 prove that this is a GLOBAL coherent repair, not only a way to kill the automorphisms of one isolated object.

In the stated finite equivariant-certificate model, the product-factorial bound in GraphDependent_Quotient_and_Cut_Memory.md is attained by these exact beta choices. In the family with one active graph slot, an n-point coefficient apex and d empty-unit slots, the left comb requires (n!)^(d-1) certificate states while the empty-first right comb needs none at proper active nodes. The coherent D system transports the certificates through the actual rotation functors. We do not present this as an algorithmic bit-complexity lower bound for arbitrary encodings.

X is constructed in the SINGLE-GRAPH span model. Its degenerate edge is (empty graph, identity span). It is not asserted to be the nerve of the free term equipment or the unnormalized graph-word envelope, where the old one-entry empty-graph word remains distinct from the fresh tensor unit. The semantic comparison can identify a new unit with an old component; conservation above concerns the specified OLD profiles, not injectivity on every enlarged component.

The section schemes defining Q_I currently name arbitrary finite-span horizontals, including doubled-apex spans. Such components are not automatically proved to lie in the image of the C5-only free virtual envelope. The concrete quotient/repair theorem alone does not establish that presentation bridge. An explicitly EXTENDED generator presentation is now proved in Extended_Local_Presentation.md. Generation of those additional spans and span maps by the smaller C5-only free envelope remains unproved.

Every graph-geometric intermediate remains the original whole's INDUCED graph. No ordinary formal graph-word assembly is inverted. The ordinary-envelope comparison maps a formal word to that induced graph by the retained, generally nonuniversal graph cut; it is merely a comparison cell. Consequently this repair does not identify cross-edge-different old whole components by new isomorphisms. The original M=1 discrete slice and the original whole distinctions are preserved.

## Status

Independent review status is recorded in ScopeAndStatus.txt. Output A is a genuine unital simplicial groupoid and original discrete recovery. Output B is a genuine rooted tree-cut module with contractions, units, rotations, exact graft action and coherent nonexact/interface comparison maps. It is deliberately NOT a full simplicial object of arbitrary thinned outer maps. No original F/I/E obligation is declared accepted merely by this submission, and no novelty claim is made for the standard graph/span nerve infrastructure.

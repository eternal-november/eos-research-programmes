# I4: retained-diagram cut/refinement interchange

31 October 2026. Final author theorem for the scoped target in `frozen_output.md`, selected at 20:25:39 UTC, corrected by approved exact-skeleton clarification v1.1 at 20:35:39 UTC, and with final boundary-factorization precision independently checked at 20:41:41 UTC. Conditional mathematical proof/scope review passed; computational evidence, exact prior-art comparison and acceptance are recorded separately. No unrestricted symmetric, causal or arbitrary-root simplicial extension is claimed.

## 1. Quantifiers and the compared object

Fix a finite ordered graph bound N, an induced-closed graph family, a finite interface category K, and finite actual span carriers where the established CUT extension is used. Original C5 is the discrete graph-span-of-faithful-K slice. The positive original quotient slice has M=1 and the F3 R/E permutation families; the explicit classification below uses ordered disjoint unions of contiguous cliques and their within-clique permutation groups. In the ambient extension scalar labels lie in a supplied finite commutative monoid M. No claim that arbitrary M gives an all-degree cut nerve is made.

**Separation of branches.** Theorem A is the labelled finite-span comparison theorem: graphs, vertex placements and all coefficient tables remain actual data. Theorem B is ONLY the original F3 M=1 orbit branch with the faithful K graph-span decoration, whose canonical coefficient maps depend on the actual grade path and not on a choice of vertex placement. The existing R/E proof therefore supplies the needed original quotient descent. Arbitrary ambient finite-span coefficient tables are NOT admitted under H-representative replacement in Theorem B. Combining such tables with orbit quotients would require an additional equivariance/descent theorem, which is not asserted or needed here. The shared structural formulas do not remove this separation.

The object compared is the **whole retained diagram**: every original occurrence, leaf replacement forest INCLUDING the individual coefficient map at each of its vertices as a named stage (not only its evaluated composite), every named proper cut component and its actual coefficient certificate, all boundary lifts, and the root equation. Invertibility means a componentwise inverse of the EVALUATED coefficient natural transformation over this fixed provenance record, not just invertibility of its root coefficient, equivalence of two contractible cut fibres, or existence of some other representative. It does NOT mean an inverse of the forest-bearing horizontal arrow. The forgetful evaluation from forest-bearing arrows to coefficient transformations may send a noninvertible refinement to an isomorphism: a binary split of an empty/id singleton span is the simplest example. Its inverse coefficient map does not contract its retained two-occurrence forest. The strict normalized exact subdoctrine requires scalar 1; the ambient comparison doctrine permits unit scalars and their explicit inverses. These are different conclusions.

A horizontal comparison points NEW -> OLD on coefficients, opposite to the direction old -> refined in the occurrence-refinement category. Vertical arrows contract cut trees. Crossings are candidates in the input language; a nonparallel crossing receives an obstruction, not an invented permutation arrow.

## 2. Primitive combinatorial test

A candidate consists of the following finite data.

* Actual ordered vertex partitions U=(U_i) and V=(V_j) of one retained whole G, with all induced embeddings, occurrence names and complete interface/grade profiles. Theorem A uses these ACTUAL labelled partitions and supplied coefficient tables; no vertex-orbit replacement is made in its ambient span branch. The separate original quotient branch of Theorem B uses its two orbit records and only the original faithful K graph-span coefficients specified there.
* Actual finite apex sets and leg tables for every atomic span, and the coefficient tables of every supplied leaf-refinement witness. Retained proper cut certificates beta are actual bijections, independently checked.
* Every requested boundary map f:A'->A, and every named composite run or nullary unit on which transport is requested. If all regroupings/units are claimed, quantify over every contiguous run and all named nullary-unit positions, not just adjacent primitive pairs.
* Retained scalar of each named leaf-refinement cell. An unknown forgotten table is marked missing, not filled by an arbitrary representative.

The following tests use only these tables and occurrence data.

**O: ordered parallelism.** Form C_ij=U_i intersect V_j and retain its pair tag whenever nonempty. Its support must contain no pair (i,j),(i',j') with i<i' and j>j'. The row-major and column-major tagged lists must have identical complete typed profiles. Empty original occurrences remain explicit tagged slots. A zero intersection may be omitted only as a designated genuine empty/id unit, under the specified common unit-insertion/deletion comparison. An arbitrary empty-graph component or empty nonidentity-arrow occurrence cannot be erased. Thus the chain-support check alone is not a claim about empty-slot or interface parallelism.

**W: individual witness recovery at fixed interfaces.** Each tested coefficient map is endpoint-preserving over the SAME interface objects on its source and target. With a specified interface change, first perform the declared cartesian reindexing and use the induced endpoint-preserving coefficient map in that fixed reindexed fibre. The separate comparison between composite-of-restrictions and restriction-of-composite is B, not part of this endpoint-preserving map. For each supplied elementary leaf-refinement coefficient table t:D->S (one per retained forest vertex/stage, including its occurrence address) and every s in S, compute

    n_t(s) = |{d in D : t(d)=s}|.

Require n_t(s)=1 for every s. Here D is the actual domain carrier of the named fixed-interface map: for an original refinement it is enumerated as compatible tuples of the supplied fine atomic apex/leg tables; for a reindexed coefficient it is the declared pullback of that old domain, not silently the composite of individually reindexed fine spans. Those two carriers are related by the separately tested c_f. This includes empty apex cases: empty->empty passes, empty->nonempty and nonempty->empty do not define/pass a total bijection. Require the scalar of every such named leaf comparison to be a unit for ambient invertibility, and to equal 1 for the normalized exact action. Do not test only the product of their scalars or their aggregate root map.

**B: boundary recovery.** For every named nonempty composite run, enumerate its feasible old witness tuples with specified lifted exterior endpoints. For each such tuple with internal interface values a_r compute

    L(tuple) = product_internal_r |f_r^{-1}(a_r)|.

Require L(tuple)=1 for every feasible tuple. A target with no feasible tuples passes vacuously. For every named nullary unit, require its map f injective; this is the separate diagonal comparison x |-> (x,x) into A' times_A A'. Do not replace it by an empty internal product.

**R: retained certificates.** Each actual coefficient table and occurrence/grade label used above must be present OR uniquely recoverable from the retained finite data. For a missing table, enumerate the finite endpoint-compatible functions/bijections satisfying all retained equations: zero candidates makes the input invalid, one recovers that table, and multiple candidates requires a supplied choice or full marked lift record. A quotient may supply an intrinsic comparison without supplying an actual comparison: if forgotten data have several possible actual lifts, an actual retained-diagram assertion requires the chosen lift or the explicit full lift record. Theorem B has its own original F3 orbit records; they are not permission to replace an ambient labelled-span diagram by an arbitrary orbit representative. Arbitrary ambient coefficient tables can depend on vertex placements and have no proved H-descent here.

### Theorem A (exact criterion and all-tree extension)

Within this declared actual-diagram class, the cut/refinement mixed comparison is defined and componentwise invertible exactly when O, W, B and R pass, with the stated scalar convention. All supplied cut records must first satisfy their defining coefficient/grade equations over the SAME retained flattened operation; this is a decidable validity check on the input, not an extra invertibility test. Once these local tests pass at every named elementary operation, their comparison extends coherently to arbitrary finite trees, iterated cuts, composed occurrence refinements and admissible interface changes. The resulting comparisons lie in the concrete double category of §5. If R has multiple possible lifts, the test reports `actual comparison not determined`, not a theorem that every possible chosen lift fails. If O fails, it reports `nonparallel`, not a nonbijective function between nonexistent parallel operations.

This statement separates typeability from invertibility. The test is a finite fibre computation on primitive tables and actual paths, not the circular hypothesis that the desired mixed map is invertible.

## 3. Proof of Theorem A

### 3.1 Order and graph coordinates

Two total orders on the distinct pair tags coincide iff they disagree on no pair. Row-major and column-major disagree precisely on an inversion as in O. A chain support has each fixed row and each fixed column as a consecutive run: if two tags have the same row (respectively column), every intervening tag in the common order has that same coordinate. Consequently both groupings are legal planar substitutions of one common atom frontier. Conversely a common ordered frontier refining both named ordered partitions must put every tag in both its prescribed row and prescribed column order; an inversion makes this impossible. This uses tags even when component types coincide, so repeated equal types cannot conceal the obstruction.

The graph on a cell is the induced graph G|C_ij. Every grouped graph is the induced graph on the corresponding union. For nested restrictions the increasing-enumeration equation e_U e_W=e_(e_U W) makes both grouping routes literally equal. Cross-edges are retained in the old whole and corresponding grouped whole; they are never reconstructed from cell graphs. Full type checking and the retained empty tags supply exactly the remaining planar parallelism conditions.


### 3.1A Full frontier-word and empty-slot algorithm

The input includes, for every nonempty cell, its ordered atomic source word, actual endpoint objects and grade arrows, plus the original occurrence IDs. It also includes two explicit lists of **named empty slots**, each with the exact row/column boundary position at which its original cut inserted it, its span/component, grade and whether it is the designated nullary unit. No unrecorded choice of an empty slot's boundary is inferred. Generate the row word by visiting rows in increasing i, within each row occupied columns in increasing j, expanding each cell's atomic word, and inserting each named empty slot at its recorded boundary position (ties use the retained original occurrence order). Generate the column word by the transposed visitation rule and its recorded empty-slot positions. Compare the resulting lists of (occurrence ID, component, left interface, grade arrow, right interface) entry by entry, and compare each retained segmentation map to its specified original profile. This is the full typed part of O.

When a comparison explicitly inserts/removes a genuine nullary unit, first execute only those named canonical unit maps and run the same word comparison on the residual list. Their source/target boundary must be the same named A with identity grade and the diagonal span. An empty nonidentity-arrow component fails that test and stays in the word. An unspecified empty-slot position makes the candidate incomplete, not admissible. Thus the condition is algorithmic, including repeated types and empty runs, rather than the placeholder 'assume profiles agree'.

### 3.2A The actual independent-cut/substitution mixed map

Write the common typed atom word supplied by O as z_1,...,z_q. For each row i let P_i be the flat tuple carrier on its consecutive atom run; for each column j let Q_j be the flat tuple carrier on its consecutive run. Let P_all=P(z_1,...,z_q). Row grouping gives an explicit bijection

    rho:P(P_1,...,P_r) -> P_all,

and column grouping gives

    chi:P(Q_1,...,Q_s) -> P_all.

Both are tuple flattening with the SAME atom names/order. The mixed grouping map is explicitly chi^(-1) rho, not an arbitrary isomorphism between equicardinal sets. If row cut nodes have supplied actual certificates r_i:P_i->R_i, and column nodes c_j:Q_j->C_j, transport it to their retained carriers by

    Xi = P(c_j) chi^(-1) rho P(r_i^(-1))
       : P(R_i) -> P(C_j).

If their root coefficients are gamma_R and gamma_C, validity as cuts of one retained operation says exactly gamma_C Xi=gamma_R. The root can be nonbijective. The formula does not cancel it.

Now replace each atom z_a by its supplied occurrence refinement, with tuple map t_a:P(new atoms at a)->S_(z_a). The two routes 'perform these refinements within rows then change cut' and 'change cut then perform them within columns' are the two sides of

    Xi_old K_rows = K_columns Xi_new.

Substitute the displayed Xi formulas and the recursive equations for the K maps. On each fine tuple, both sides apply the SAME t_a to the SAME named atomic subtuple, then the SAME old column c_j; flat regrouping only changes parentheses. Hence the equality is pointwise, with scalar products and actual grade composites equal in their retained occurrence order. This is the mixed cut/substitution comparison. It is not merely ordinary associativity at an unlabelled root. W describes when all named t_a comparisons in this entire square are invertible, B when its boundary-change companions are invertible, and O when Xi is a typed planar map at all. If a boundary factor fails, the original grouping Xi may still be a bijection; the full requested retained mixed diagram is not invertible. That distinction is intentional.

### 3.2 Actual coefficient formula and fibres

Write P for the canonical flat compatible-tuple composite of spans. On an old cut tree every proper vertex has its retained beta_v:P(S_children)->S_v. After leaf refinement take ANY supplied new exact proper diagram with carriers S'_v and actual bijections beta'_v on the refined atomic leaf spans. Such a diagram always exists by choosing flat composites and tuple-flattening; this is an optional canonical construction, not a mandatory replacement of an already supplied diagram. At each original leaf use its supplied map t. Recursively set

    k_v = beta_v P(k_children) (beta'_v)^(-1).

At the root define the new outer coefficient by gamma_new=gamma_old P(k_children), so the root component of k is the identity on the unchanged output span. This is exactly the required naturality square, not a root-cancellation argument. Scalars at an old proper edge are the products of supplied refinement scalars below it.

W says exactly that every leaf map has a unique inverse on its actual apex, preserving endpoints because the original maps preserve endpoints. At FIXED interface objects, P of endpoint-preserving bijections is a bijection: its inverse is the componentwise inverse, which preserves the equalities of shared endpoints. This argument does not apply to a bijection merely covering a noninjective change of endpoint objects. Induction in the displayed formula therefore gives every proper k_v invertible. Leaf scalars that are units give inverse scalar labels throughout; scalar-1 leaves give the normalized exact subaction. Conversely a componentwise inverse of the retained diagram includes inverses on its named leaves AND every retained elementary forest-stage comparison, so each n_t(s) is 1 and each leaf scalar has an inverse. If one requests only the evaluated map of a whole multi-vertex forest, W is sufficient but not necessary: distinct nonbijective stage maps can compose to a bijection. This is precisely why the theorem retains/tests every stage. An internal product can hide an empty-support failure or a noninvertible individual map, but it cannot supply an inverse of the retained failing leaf. This explains why the theorem names the entire diagram.

### 3.3 Boundary formula

A tuple of separately reindexed spans consists of one old compatible witness tuple, fixed lifted exterior endpoints, and a choice of lift of every old intermediate value. The comparison to the reindexed old composite forgets those internal choices. Its fibre is precisely the product in B. Thus its bijectivity is equivalent to B, including empty feasible support. At arity zero the source is the actual diagonal A', while the target is A' times_A A'; the diagonal is surjective iff f is injective and is always injective. This proves the separate nullary clause.

Restriction preserves any actual beta bijection, but composite-of-restrictions contributes this extra map. Testing the actual child-composite span at every vertex detects exactly every new obstruction. For closure under all rotations, test all contiguous runs, as stated. Necessity follows by reading each such comparison as a named component of the retained mixed diagram; no global root test substitutes for it.

### 3.3A Required boundary factorization and order of operations

The mixed boundary construction has a specified factorization. For a coefficient map t:P(S_1,...,S_n)->S over old interfaces A_0,...,A_n, and declared maps f_i:A'_i->A_i, form the actual cartesian reindexed spans S'_i=(f_(i-1),f_i)^*S_i and S'=(f_0,f_n)^*S. The transported cell is the composite

    P(S'_1,...,S'_n)
      --c_f--> (f_0,f_n)^*P(S_1,...,S_n)
      --(f_0,f_n)^*t--> S'.

Both arrows now preserve the fixed new external endpoints. The c_f arrow is exactly the B comparison, with the fibres in §3.3; the reindexed t arrow is the fixed-interface coefficient comparison on which W or W_sem is tested. Restricting a supplied old endpoint-preserving bijection gives a bijection on these pullback carriers, but conversely its restriction may omit an old failure. Therefore state whether the retained diagram includes the OLD comparison as well: test old W too only if that old arrow is among the requested retained components. The principal requested changed-boundary diagram tests the actual reindexed coefficient arrow and the named c_f separately. Their composite can mask a failure if only that composite is observed; no such root/composite-only necessity claim is made.

A map of apices h:S_new->S_old merely covering boundary maps f is not itself a fixed-interface coefficient map. First factor it through the actual pullback:

    S_new --h_bar--> (f_left,f_right)^*S_old -> S_old,
    h_bar(x)=(left_new(x),h(x),right_new(x)).

Test h_bar, not the raw apex function h, by W, and use B for every requisite composite-of-restrictions comparison. If the candidate omits the needed factorization/reindexing data or its covering equations fail, it is not a well-typed instance of this theorem. In particular a raw apex bijection covering noninjective boundary maps is not sufficient to infer invertibility of P(h), and no such inference is used. Successive changes and tree/graft comparisons in §3.4 use these specified pullback factorization arrows in this order.

### 3.4 Composition and arbitrary depth

For two successive refinements use their retained forest substitution, never just equality of the flattened output. At a leaf the map of their composite is ordinary tuple substitution. If k and l are the two comparison families, the recursive naturality equation yields

    (k_v l_v) beta''_v
      = beta_v P(k_children l_children).

Thus the composite family is exactly the family computed from the composed forest. Induction proves the statement at arbitrary depth. Disjoint grafts preserve their separate occurrence positions; nested grafts compose their actual subset embeddings and grade arrows. For an identity forest BETWEEN THE SAME supplied diagram, the recursive equation gives identity families, even if that diagram is noncanonical. Applying canonical normalization to an existing diagram instead gives its explicit normalization isomorphism, not its identity. Empty forests are valid only at their original empty/id profiles.

Contraction substitutes two adjacent beta maps; applying the displayed k equation twice gives the same equation for their composite. Hence contraction before or after the comparison gives the same actual function and labels. Nested and disjoint contractions agree by tuple substitution and the induced-restriction identity. A normalized split introduces a flat carrier and flattening beta; contraction after split is identity. Split after contraction has the explicit comparison given by the old retained beta. Every comparison in a fixed exact cut factorization is forced recursively by its fixed leaves and root. Therefore two composites of these already constructed comparisons coincide; this proves pentagon and all higher finite regrouping diagrams, not existence inferred from contractibility.

Two successive boundary changes forget exactly the same two levels of lift coordinates in either order. Their comparison maps therefore agree literally in flat tuple coordinates. When B passes, their inverses agree as well. The same argument applied to a graft tuple proves the boundary/graft and boundary/contraction equations. This completes the all-tree proof.

## 3B. Original semantic refinement versus fully staged provenance

The theorem has two explicitly distinguished versions. The raw original refinement carries its leaf-indexed presentation forest; its full staged output retains each vertex, and Theorem A's per-stage W is exact for that output. The semantic B3 refinement carries an occurrence-indexed tuple (b_i) of evaluated operations, not a chosen primitive presentation of each b_i. For THIS original semantic output replace W by the following exact test W_sem, without adding a stronger retention requirement:

At the fixed interfaces specified in W (after the declared cartesian reindexing when present), for each original occurrence i evaluate its supplied b_i coefficient map on compatible fine atomic tuples, retaining its complete source profile and segmentation. Count every fibre of that composite map. If it is supplied through a tree of primitive tables, the counts are calculated from those tables by

    N_v(s) = sum_(compatible child tuple u with t_v(u)=s)
                 product_(children c) N_c(u_c),

starting with N_leaf(x)=1 for each actual fine atomic witness x. Each tuple in a fibre makes one and only one choice at every tree vertex, so this recursion counts it exactly; endpoint compatibility is imposed in the sum. Require N_root_i(s)=1 for every old source witness s, for each original occurrence separately. Test its evaluated scalar and retain its full semantic operation b_i, not its arbitrary factorization. The all-tree proof of §3 uses precisely these maps as k_i and is unchanged. Thus W_sem, O, B and R are necessary and sufficient for the evaluated full cut diagram over the original semantic tuple. A forest can fail per-stage W but pass W_sem. No assertion that a semantic B3 arrow remembers those failed stages is made.

For example singleton -> two-point -> singleton with first map selecting one point and second the collapse has bijective composite but neither stage is bijective. The semantic one-occurrence coefficient comparison passes W_sem; the fully staged comparison fails W. An even further collapse to the root coefficient alone may hide failure of W_sem at one old occurrence through empty compatible products or a nonfaithful root map. The theorem for the retained occurrence tuple does not apply to that still weaker root-only observation.

### Named directional procedures and exact-skeleton encoding

For a cut tree T of a, define CS(T,b) ('cut then substitute') by grafting the supplied actual b_i forests into the distinct old leaf occurrences and retaining the old intermediate carriers and coefficients. Define SC(T,b) ('substitute then cut') by first forming the actual composite a[b_i], then cutting its fine source occurrences along the lifted runs of T, with new intermediate carriers their flat tuple composites and normalized exact cut maps.

The literal grafted CS tree can have nonexact proper nodes. It is NOT falsely declared an object of the frozen exact-proper double category. Its faithful representation there is the pair **(old exact cut skeleton T, full external graft forest b)**: that pair reconstructs the literal grafted tree and every coefficient by ordinary tree grafting, so nothing is normalized away. SC is represented by the new exact skeleton with its refined leaf bundles. The corresponding horizontal arrow carries the full forest as its prescribed provenance label. Thus both procedures have explicit retained outputs, although a nonexact graft is represented by a labelled arrow rather than by a new exact-cut object.

The directional coefficient comparison lambda_(T,b):SC(T,b)->CS(T,b), in this encoding, has at each old cut edge exactly k_v of §3.2. At each old leaf its component is the evaluated original occurrence map b_i from that leaf's refined bundle to its old carrier. It is over the identity on the fixed root span, with gamma_new=gamma_old P(k). This is the actual comparison whose invertibility in the coefficient-diagram image is characterized by W_sem, O, B and R. The forest-bearing arrow itself is not claimed invertible.

For the raw fully staged variant, the retained external forest record has its own explicit evaluated comparison: at each forest vertex v map the flat fine-descendant carrier to its retained carrier recursively by k_v=t_v P(k_children) flatten^(-1). These are actual named finite maps, not extra exact-proper objects. All these k_v are invertible iff the per-stage W test passes: sufficiency is induction, while necessity solves t_v=k_v flatten P(k_children)^(-1). The old root is excluded from this calculation and need not be invertible. This additional staged comparison is recovered from the stored forest, never assumed to be remembered by the semantic B3 tuple. No change to the frozen object class is needed.

For a second independent cut V, O identifies the two fine ordered words, and Xi of §3.2A is the explicitly supplied change of grouping between their row/column cuts. The equation Xi_old K_rows=K_columns Xi_new says exactly that lambda is compatible with this independent cut change. Iterating this equation along contractions/splits gives the all-tree independent-cut/substitution coherence, and §5 supplies its double-pasting laws. Nonparallel crossing inputs have no such Xi; the obstruction is not remedied by normalizing CS.

## 4. A computable original-quotient theorem beyond the actual intersection test

Let G=K_(r_1) disjoint-union ... disjoint-union K_(r_b), in the original ordered contiguous-clique class. Two F3 orbit cuts are exactly occupancy matrices A_bi and B_bj, with row sums r_b. Keep the actual whole, full K paths and occurrence indices. Define cumulative intervals

    I_bi=[sum_(k<i) A_bk, sum_(k<=i) A_bk),
    J_bj=[sum_(l<j) B_bl, sum_(l<=j) B_bl),
    C_bij=|I_bi intersect J_bj|.

### Theorem B (intrinsic quotient planar-refinement criterion)

For the original M=1 faithful K graph-span decoration ONLY, subject to the full type/empty-slot part of O, an orbit common refinement whose atom frontier refines both ordered cuts exists iff the union of supports {(i,j): some b has C_bij>0} is a chain in the product order. When it exists its joint orbit is unique and is exactly C. Its cut and refinement comparisons commute with the actual F3 quotient and independently presented B3 occurrence-refinement comparison. This is an intrinsic orbit result, not a unique-original-lift claim.

**Proof.** In any nonnegative integer joint table with the two prescribed marginals and chain support, the mass in the rectangle i<=p,j<=q equals min(a,b), where a is the first p row mass and b the first q column mass. Otherwise there is simultaneously positive mass in the upper-right and lower-left complementary rectangles, giving an inversion. Taking successive two-dimensional differences forces C_bij to be the interval-intersection formula. This holds independently in each clique. Therefore any planar joint orbit must equal C, and the union-support condition is necessary. If that union is a chain, split each clique into cells of these cardinalities, put the cells in the common tag order and take the orbit. Its marginals are A and B. Within-clique permutations identify any two labelled realizations of C; hence the resulting orbit is unique. It has precisely the required graph and occurrence profiles when the separate type check passes.

Substitution of occupancy matrices replaces a column by its supplied per-clique inner row, inserting zeros in absent clique rows. Taking a cut sums the selected consecutive columns. The joint table is therefore the same array whether the atom cells are first substituted within rows or first regrouped within columns, whenever the tagged order is parallel. Iterated sums/replacements are literally associative and preserve all occurrence lengths. The F3 R/E theorem establishes representative independence and its actual original binary equations; B3 maps retain exactly each occurrence's matrix operation and full profile. Consequently these equalities are equalities of actual refinement tuples in the stated B3 comparison, not inferred merely from equality of their final composite. This verifies the required quotient/interface connection on the original recognized class.

**Sharp representative distinction.** On K_2, the two actual cuts U=({1},{2}) and V=({2},{1}) have inverted intersection support and admit no common ordered refinement preserving their names. Their F3 quotient cuts have the same occupancy (1,1); Theorem B has diagonal joint table and a common orbit refinement. It has changed the permissible representative, not manufactured an actual permutation of input slots. Thus the original labelled and intrinsic orbit verdicts are intentionally different. Any theorem identifying them would be false.

## 5. Concrete double-category realization and law check

Use exactly the objects and directions frozen in `frozen_output.md`. A skeleton leaf carries a bundle of atomic occurrences and its flat composite span, so horizontal composition is well typed even after a second refinement. The full forest relating each new bundle to the old bundle is retained. Different forests with the same evaluated table remain different horizontal data.

Horizontal arrows are ALL actual natural coefficient families on the supplied source and target exact-proper diagrams, with their composable forest data and leaf maps equal to the evaluations of those forests. The proper-node naturality equations force their internal maps recursively by §3.2 for these actual source and target beta maps. In particular source and target may be the SAME noncanonical diagram; literal identities are included. The optional canonical-source construction of §3.2 is a designated family of comparisons, not the whole arrow class. Their composition and identity are those of §3.4. Vertical arrows contract specified inner edges and evaluate their vertex composites. A square is the commuting actual coefficient diagram obtained by contracting a horizontal comparison; its bottom is the induced comparison, with unchanged occurrence forest. This defines sets of actual squares, not freely generated symbols.

Horizontal pasting composes each k_e and substitutes its forests; the §3.4 equation proves that its boundary is the derived comparison for that composite. Vertical pasting contracts the union of the successive surviving edge sets, tracking edges by their original identities. The resulting maps are the same vertex composites, so it is again an actual square. Empty contraction sets and identity forests give the two units. Function composition and tree contraction are associative; forest substitution and flat tuple substitution are associative; therefore both square compositions are associative and unital. Finally for every surviving edge e,

    restriction_u(l k)_e = l_e k_e
                         = (restriction_u l)_e (restriction_u k)_e.

At a contracted vertex the same equality is the naturality equation for the composite beta proved in §3.4. Forest labels agree by their identical occurrence-wise substitution. Hence the two double pastings have identical four boundaries and identical internal tables/labels: middle-four interchange holds strictly in canonical flat coordinates. These statements construct a concrete strict double category for contractions; the explicit split/rotation comparisons extend it coherently, not by falsely declaring every split a strict inverse.

The row and column trees of a grid have the same atomic frontier exactly under O. Each contracts to its common flattened corolla. Their actual beta comparisons give the mixed regrouping zigzag, and §3.4 proves compatibility with every horizontal refinement square. When O fails there are two distinct frontiers; this construction leaves the crossing candidate nonparallel. No double square has been silently added to permute it.

The original scalar-1 K-graph slice is closed under contractions and its actual original refinements. Separately its original R/E orbit quotient has the descended operations proved in Theorem B; this is not a descent assertion for arbitrary ambient span coefficients. A canonical flat split lies in that slice up to the specified endpoint-preserving graph-span bijection P(F(h_1),...,F(h_n)) -> F(h_n...h_1); transport the split along this supplied bijection to obtain its literal original K-graph representative. Thus arbitrary choice of tuple apex is not asserted to be literally an original span. The ambient finite-span model also carries the supplied arbitrary root labels; only its proper normalized exact nodes enter cut regrouping. The arbitrary root has not been given nonexistent outer simplicial faces. Interface changes enter via their actual lax comparisons and the B-admissible invertible subfamily, with their composition laws already established in §3.4.

## 6. Nontrivial positive families and independent sharp failures

**Positive, unbounded overlap.** For each m choose 2m+1 distinct atom occurrences in one common order, arbitrary induced whole graph from the allowed family, and two interval partitions of that order whose boundaries alternate. Adjacent blocks overlap without inclusion but their intersection support is a chain. For instance U=({1,2},{3}) and V=({1},{2,3}) has support (1,1),(1,2),(2,2). Choose any composable K grade path, finite spans whose coefficients are the tuple-flattening bijections, and boundary bijections (or non-surjective maps whose feasible values each have a unique lift). O/W/B pass for every depth. Repeated equal span/component types are allowed because the atom names remain distinct. Within-clique orbit matrices give nontrivial witness identification while retaining which clique contributes to each occurrence; Theorem B computes their intrinsic common refinements.

**Planar obstruction.** A full 2x2 nonempty intersection grid has tags (1,2) and (2,1), so no named parallel planar comparison exists regardless of coefficients or boundary quality. This includes the operational crossing example; its stable-merge operational transport is not this planar cut theorem.

**Actual witness-forgetting obstruction.** Let a proper intermediate span have n>=2 equal-endpoint apex elements. Forget its beta table while retaining actual endpoint-preserving permutations. There are n! possible actual bijections, and no canonical retained comparison is determined. Restoring the chosen beta restores §3.2. At the root a support-thinning quotient can identify a two-to-one map with a support isomorphism; W still reports fibre size 2. Graph and external support alone do not decide the coherence.

**Boundary obstruction invisible at the whole.** In the established CUT example, three singleton graph blocks have a cross-edge between the first and third, making the whole active while the first-two induced graph is inactive. Duplicate the first internal singleton interface by 2->1. The first-two composite has lift fibre 2, so B fails even when the active whole quotient reports support-level invertibility. Retaining intermediate actual witnesses detects it. The nullary analogue is the missing off-diagonal element of A' times_A A' for any noninjective f.

**Primitive-pair shortcut fails.** For the three-span path through internal value 1 in {0,1}, restrict both internal interfaces to {0}. Adjacent pair comparisons have empty exterior-restricted targets and pass vacuously, but the full three-span target has its old witness and no lift. The required full composite-run test fails. This is why no adjacent-pair-only criterion is claimed.

**Decoration normalization obstruction.** The original scalar memory theorem gives lifts parametrized by H^r at positive proper nodes for a unit subgroup H. Their actual D(g) gauges are unique between fixed marked lifts. Forgetting marks does not preserve a specified normalized factorization. In particular a nontrivial h in C2 cannot be produced from the same scalar-1 factors merely because the quotient identifies its root with 1. The ambient unit-gauge comparison permits h and h^-1; the normalized scalar-1 subaction does not. This is an actual witness-decoration distinction on the same graph, not a graph-only test. The scalar marked construction is imported, not used to assert a new arbitrary-M 2-Segal nerve.

## 7. Scope, residual evidence and attribution

Theorem A is the exact retained-diagram branch with finite-table witnesses, Theorem B is the explicit original R/E cluster quotient branch. They are not a classification of all abstract witnessed calculi. Both are unbounded in tree depth/arity and graph-size parameter; finite tables are inputs, not a fixed toy example. All-span signature completeness from original C5 is neither used nor claimed.

This proof reuses CUT's actual rooted module, span fibre formula and coherent repair, SCALAR's marked gauge theorem, and F3's quotient/presentation/B3 integration. Those are supplied prior results, not new discoveries here. The additions are the explicit double-category output with checked variance and pasting, the separated grid/typed/witness/boundary criterion, and the intrinsic orbit monotone-coupling criterion with its actual-lift boundary. The generic diagram-double-category construction, tuple composition and noncrossing-coupling uniqueness themselves are standard mechanisms; no originality claim is made.

Still required before a complete I4 disposition: independently replayable finite C tests covering every §6 control, non-author mathematical and scientific-scope audit, and exact direct comparison against Baez–Dolan/free-operad comodules and directed hereditary species. The latter must identify the occurrence quotient and boundary-witness conditions that are additional to their reused baseline. This mathematical theorem alone does not discharge P+C or acceptance. The independent proof/scope audit and final boundary-typing check have passed for this declared target; the remaining evidence gates are not inferred from that result.

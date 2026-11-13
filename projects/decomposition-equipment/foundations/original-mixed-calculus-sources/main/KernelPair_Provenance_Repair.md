# Kernel-pair provenance repair for noninvertible changes

This is a precisely changed semantic doctrine, not a proof that noninvertible changes preserve the original discrete-span cut certificates. It is complementary to the original-generator analysis.

## Plain-language abstract

A change of interface can give several new names to the same old boundary value. Demanding one uniquely correct new name is then the wrong test for a representation-independent cut. One alternative is to keep all names and explicit certificates that two names denote the same old value. Cutting and reconnecting must retain these certificates. This repairs duplication, including empty components, but cannot repair an old value for which there is no new name. It also does not justify forgetting a graph partition, a physical witness, or an occurrence's scalar. The resulting theorem is a coherent groupoid-valued repair, not an equality quotient or a new claim of novelty for descent theory.

## 1. Fixed original data and the impossibility boundary

Use the actual graph-span-global-M model in the earlier dossier. A cell has full ordered occurrence profile, actual induced-graph partition pi, endpoint-compatible coefficient map phi, and scalar m. Finite ordered graphs, all empty/repeated occurrences, and arbitrary finite commutative M remain unchanged. Original graph-arrow horizontals are included by their actual graph spans. Original cells and original refinement tuples are discrete labels throughout the following construction.

For f:A'→A define K_f to have objects x∈A', exactly one arrow x→y when f(x)=f(y), and no arrow otherwise. Projection p_f:K_f→A_discrete sends x to f(x). It is fully faithful; it is essentially surjective exactly when f is surjective. More generally it is an equivalence to the discrete image of f.

In the OLD doctrine, the nullary comparison is Δ:A'→A'×_A A'. Its bijectivity forces f injective. Thus any demand of strong transport of all old discrete units already forbids every noninjective f. Adding equality quotients cannot repair the absent off-diagonal endpoint support while retaining the old spans and cartesian universal properties. The terminal-restriction retract obstruction additionally prevents identifying distinct old graph cuts by calling their duplicated-interface restrictions equal. These are separate obstructions: missing unit support versus forced old-cell equality.

Our repair changes discrete interfaces to K_f and uses weak matching at seams. It is not a loophole in either no-go theorem.

## 2. Actual witness groupoids, no quotient of old witnesses

For an old span S=(A←E→B) and maps f:A'→A,g:B'→B, define R(S;f,g):
- objects (x,e,y), with f(x)=l(e), g(y)=r(e);
- one arrow (x,e,y)→(x',e',y') iff e=e', f(x)=f(x'), g(y)=g(y').
The legs to K_f,K_g remember x,y. Every morphism fixes the ACTUAL old witness e. Distinct e are never isomorphic.

Compose a path by weak pullback over each K_f. An object includes each edge triple and a seam arrow from the previous right lift to the next left lift. That arrow exists exactly when the two old values agree and is unique. Thus an object is an old feasible witness tuple, independent choices of lifts at all incident half-edges, and the forced seam certificates. Morphisms fix every old edge witness and change lifts. There is no choice of an isomorphism between distinct old witnesses.

For an old tuple w, the fibre groupoid of the forgetting projection is an indiscrete groupoid on the product of the required lift sets. It is empty if a required lift set is empty; otherwise it is contractible, however large its cardinality. Consequently:

**Theorem 1 (exact criterion in the repaired doctrine).** The projection from weakly composed reindexed spans to the old tuple groupoid is fully faithful and has essential image precisely those tuples all of whose required interface values lie in the corresponding map images. It is an equivalence iff every old feasible tuple satisfies that image condition. This includes external endpoint lifts if they have not already been fixed. For surjective interface maps it is an equivalence for every finite path, independently of fibre cardinality.

Proof: distinct old tuples have no arrows on either side; any two lifts of the same tuple have exactly one arrow. Nonempty fibre is equivalent to the stated finite conjunction of image-membership tests. This proves fullness, faithfulness, and the exact essential image, without choosing sections. The groupoid does NOT merely retain each edge's marginal support; the shared old tuple and all seam constraints remain in each object.

## 3. Nullaries: the changed unit is essential

Reindexing the old identity span gives the groupoid with objects (x,y) such that f(x)=f(y), and a unique arrow between any two pairs with the same old value. The identity span on K_f has apex K_f. The diagonal functor x↦(x,x) is fully faithful and essentially surjective: (x,y) is isomorphic to (x,x). The diagonal is therefore an equivalence for EVERY f, not a bijection of object sets. At specified endpoints x,y, use the homotopy fibre, whose connecting datum is the unique K_f-arrow x→y; the strict set fibre would repeat the old failure.

This includes A'=∅. It repairs comparison with the reindexed old identity, not coverage of old values outside im(f). Comparison back to the entire old identity is an equivalence only when f is onto.

This is the exact price: different lift names for the SAME old value become isomorphic. If those names represent distinctions that the application insists must remain observationally discrete, this repair is inadmissible. Graph partitions, coefficient witnesses, local scalar labels, and old component identity do not become isomorphic merely because their boundary names do.

## 4. Trees, refinement and coherent changes

A finite rooted planar occurrence tree is represented by a single global record containing:
(i) the actual old witness at every vertex/edge, all coefficient-map evaluation equations, full partition and induced-subset data;
(ii) the scalar of each specified semantic cell separately, with the root aggregate obtained by the original monoid product (not a placement of decorator nodes in raw syntax);
(iii) one lift name at each incidence and the seam arrow for each connected pair;
(iv) genuine nullary occurrences with their named boundary and K_f connector.
Morphisms fix (i),(ii), the occurrence tree, and all old boundary values; they vary only lift names. The fibre over each old global record is again empty or contractible. Therefore Theorem 1 applies to arbitrary finite trees by the SAME image-support condition on all incidences, not only pairwise primitive-span tests.

Cutting a record retains the shared edge and its old witness and seam data. Gluing is weak fibre product over that shared record. Restriction to subtrees followed by gluing recovers the same global record up to the unique lift-change isomorphism fixing all old data. Contraction uses the actual C5 tuple-substitution/coefficient-composition function and exact induced-restriction identities; graph partitions are never reconstructed from leaf graphs. For repeated occurrences, coordinates are indexed by occurrences, not component names. For scalar-bearing refinement forests, the full vector of local scalars stays part of the supplied refinement arrow, even when products agree. Evaluation to a contracted operation may forget that vector: it is not claimed faithful. Coherent exact cut equivalences here use the established normalized convention of scalar-one inner cells and arbitrary root scalar. Arbitrary scalar-bearing grafts retain their arrow records and yield ambient comparison diagrams, not new invertible cut morphisms.

Associativity of gluing is flattening of the SAME finite tuple of vertex data and seam arrows. Both sides have the same coordinate projection to every original vertex; seam arrows are unique when their old values agree. Hence associativity, disjoint and nested contractions, and unit insertion diagrams commute after the specified tuple reassociations. This proves coherent weak transport of the already defined semantic operations, not existence of additional original syntactic generators. No uniqueness-of-isomorphisms argument is used to invent an operation: every operation is the displayed record restriction, weak gluing, or original evaluation.

### Successive changes retain the first comparison groupoid

For B'' --g→ B' --f→ B, the two-stage lift groupoid has objects (z,x) with g(z)=x. Its morphism (z,x)→(z',x') exists uniquely iff f(x)=f(x'), fixing every old coefficient/graph witness. It is NOT defined by x=x' or g(z)=g(z'). In categorical terms its groupoid structure is pulled back from K_f along g, rather than recomputed independently as K_g. Forgetting x is a literal isomorphism to K_(f∘g): both objects and arrows are identified by the displayed formulas.

A minimal diagnostic is f:{0,1}→{*} constant and g=id. Naive K_g is discrete with two objects and is wrong; the provenance-aware two-stage groupoid has the unique arrow between its two objects, exactly as K_(f∘g) does.

For the weak-record variant, allow objects (z,x) with f(g(z))=f(x), without requiring g(z)=x. There is exactly one arrow (z,x)→(z',x') iff f(g(z))=f(g(z')), again fixing the old witness. Forgetting x is fully faithful and essentially surjective to K_(f∘g), since x=g(z) supplies an object over every z. This is an equivalence, not necessarily an isomorphism of object sets.

For an arbitrary chain A_d --f_d→ A_(d-1)→...→A_0, strict records (x_d,...,x_0) satisfy f_i(x_i)=x_(i-1). There is exactly one arrow between two records iff their x_0 values agree. Projection to x_d identifies this groupoid with K_(f_1...f_d). Every partial flattening drops an explicitly specified set of intermediate coordinates. All composites of flattenings agree on objects AND arrows, since they drop the same coordinates and the retained old-value equality is unchanged. This proves associativity and the identity-change law for all chains. Apply this at each named interface occurrence of the global tree record; the same statement holds after fixing all old coefficient, graph and scalar data.

If intermediate representatives are retained only up to equality of their OLD A_0 values, give the weak-record groupoid the same old-value-fixed arrow rule. Its projection has contractible nonempty fibres, and the analogous flattenings are equivalences. Their canonical comparisons are the unique morphisms fixing old data, and coherence follows from the already specified coordinate-forgetting maps. Independently recomputing kernel pairs at each stage would invalidate this theorem.

## 5. Noninjective positive family and the honest scope

Take any actual ordered whole graph G, any partition into induced blocks, repeated empty slots, and any actual old span tuple/evaluation map. At each interface value a choose an arbitrary finite nonempty set L_a. Set A'=coproduct_a L_a with f(a,l)=a. Fibre sizes may vary and grow without bound; there is no balanced-cover assumption. All changes are surjective and generally noninjective. The repaired transport is an equivalence for every tree and every arity, including nullaries. It preserves the chosen whole graph and all cross-edges, actual occurrence-indexed partitions and coefficient witnesses, and individual local scalar labels. Thus it is not restricted to independent component state dynamics or a graph-connectivity discovery trick; it concerns the actual witness calculus. It is nevertheless standard descent infrastructure, not an architecture-identification theorem.

For nonsurjective f, define the context-admissible record class by requiring every boundary value USED BY THAT GLOBAL RECORD to lie in im(f). This class depends on the actual graph cut and coefficient witnesses, not solely on an interface's cardinality. Theorem 1 is exact on this class. It is closed under cuts and contractions only when all exposed/internal incidence records are retained; forgetting a contracted internal value and then admitting fresh records can enlarge the class improperly. Thus the correct object is the provenance-bearing record category, not a root-only operation predicate. Arbitrary old operations outside it have an explicit missing-value obstruction. No repair can conjure a lift for a value outside the map image.

## 6. Equality-quotient and original-presentation guardrails

This construction does not identify any two distinct old pi, phi, m, or refinement tuples. Original data form a discrete base; the projection fibres change only duplicated interface names. In particular the K_(r,r) cuts (U,V) and (V,U) in TerminalRestriction_NoGo remain in different connected components after every surjective lift. There is no equality a^A=b^A to which a cartesian return context could be applied.

It also does not provide a classification of all quotient kernels of the original mixed calculus. To descend through a proposed quotient of old witness data, that quotient must separately preserve every defined context and the shared record maps. A quotient that merges the old base records loses the information just protected. The result lives in the concrete span semantics on original C5 image cells plus the explicit groupoid-interface extension. Generation of every such extended object by ORIGINAL C5 rules is not asserted. The main agent's source-level theorem must decide which portion is expressible there.

## 7. What is new relative to the previous dossier

The earlier Global_Cut_Repair §10 demanded bijective fibre comparisons for transport of retained actual set bijections. This note changes the transport target, supplies the nullary comparison as an equivalence, handles arbitrary finite nonempty fibres uniformly, and proves that only missing values remain as transport obstructions in that doctrine. It is a coherent positive repair, not an improvement to the old bijectivity theorem and not a novelty claim for kernel-pair descent. Whether this change of doctrine fits the original contract is a separate decision.

## 8. Direct check against the original seven equations

Source inspected: `research/workstream_A/rewrite/A3_LOCAL_COMPARISON.md` §§1–6. The original generators are C (binary actual induced cut), U_A (nullary empty/id), and D(W,m). Their equations are R, UL, UR, D0, DA, DL, DR. On original graph-span images a semantic operation has pi, its forced endpoint-compatible coefficient, and aggregate m.

R transports the SAME original triple of induced blocks and tuple witnesses through reassociation; our weak seam coordinates flatten to the same old tuple. UL and UR delete only the U_A nullary connector, using the diagonal groupoid equivalence of §3, not deleting an arbitrary empty component. D0 and DA leave witness/lift coordinates alone and use 1 and multiplication in M. DL and DR leave those coordinates alone and move a scalar to the semantic output via the original scalar multiplication law. Thus the repair interpretation respects every declared original equation. Decorator placement is NOT retained as an extra invariant of semantic cells. Distinct scalars of different supplied refinement children ARE retained until that arrow is evaluated, just as in original B3.

These checks establish a sound interpretation of the original presentation in the enlarged groupoid witness setting. They do not prove fullness or freeness of that interpretation, nor generate all new kernel-groupoid spans from C,U,D. In particular they must not be misreported as the missing original-to-extended-generation theorem.

## 9. Compatibility with marked unit-scalar redistribution

This paragraph combines the boundary repair with the scalar repair only after its marked domain is specified. It is not a free-envelope presentation theorem.

Coordinate convention: the h_v below are cumulative EDGE marks. In `Original_Cut_Scalar_Memory.md` §2, h_v instead names a NODE scalar label. The two H^r parametrizations are canonically related: our edge mark is the product of the positive node labels in its subtree. The displayed division by child edge marks recovers that node's label. Thus the formulas below agree with that note; they do not impose a different scalar repair.

Fix an actual rooted cut tree T, its original whole graph, all induced partitions/occurrences, actual coefficient witnesses and their evaluation equations, and an ACTUAL root aggregate m∈M. Fix H≤M^×. For each proper internal edge v with nonempty graph choose a mark h_v∈H; use h_v=1 on empty-graph internal edges and fixed leaves. At each proper vertex set its scalar to

    s_v = h_v (product of h_w over its internal children w)^(-1),

and at the root set

    s_root = m (product of h_w over its internal children w)^(-1).

(Only marks in H are inverted, never m.) All vertex scalars multiply to m by telescoping. These are normalized, unit-generated scalar factorizations; this does NOT cover arbitrary factorizations involving nonunit inner scalars. An empty root has only empty descendant graphs and all marks are1, while its root scalar remains the supplied m.

Changing marks h_v to h'_v is recorded by the explicit unit gauge t_v=h'_v h_v^(-1), with t=1 on empty edges. Its local scalar effect is s'_v=t_v s_v (product_child t_w)^(-1) and s'_root=s_root (product_child t_w)^(-1). Hence root m is literally fixed even when m is noncancellative. These are arrows in a MARKED redistribution groupoid, not equalities of different original scalar-labelled refinement forests. The C5 DA/DL/DR rules justify evaluation of the redistributed tree to the same root operation; they do not erase the individual forest entries before evaluation.

Let S_T(m) be that marked scalar groupoid and let B_T(f) be the boundary-lift groupoid over the fixed old coefficient/graph witness record from §§2–4. The combined record groupoid is literally

    S_T(m) × B_T(f).

Objects are a scalar mark assignment and a lift assignment; a morphism is its gauge together with its old-witness-fixed lift-name morphism. Scalar equations use only marks/m, and boundary matching uses only coefficient/endpoint data, so there are no extra cross constraints. The action (t,identity) commutes strictly with (identity,boundary-arrow). This is the precise independence needed for the product claim. It is over the fixed NONSCALAR old witness skeleton and root m, not over fixed per-vertex scalar values, which gauges intentionally redistribute.

Interface changes preserve graph grades, actual scalar marks and their root aggregate. Provenance-aware iterated boundary transport therefore acts as identity on S_T(m). Any established scalar contraction/rotation functor acts on its marked factor while the boundary functor applies actual tuple projection/weak gluing. These maps commute because each leaves the other factor's coordinates unchanged, apart from the common explicitly specified tree reindexing. Consequently the scalar coherence diagrams and the boundary coherence diagrams combine componentwise. For a tree transformation, use the scalar repair's actual functor and its declared normalized domain; this paragraph does not manufacture one from contractibility. Nullary insertion introduces an empty mark1 and the K_f unit connector, so the two unit comparisons likewise commute.

Thus the two repairs can be combined without identifying graph-distinct wholes, different original partitions, or original local scalar forests as equal. One has explicitly enlarged the morphisms between *marked presentations* of the same retained root data. If the application insists on retaining every local scalar forest as a discrete object with no redistribution morphisms, S_T(m) must instead remain discrete and no scalar-groupoid cut-equivalence conclusion follows.

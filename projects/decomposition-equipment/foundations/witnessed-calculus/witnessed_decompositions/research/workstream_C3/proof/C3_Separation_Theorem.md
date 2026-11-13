# C3 — separation, exact fibres and local observational loss

Evidence P and X. Submitted for independent review; this document does not
self-accept an obligation. Contract v0.1 unchanged, SHA256
`47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e`.
Frozen target SHA256
`88ea710752d99cd83d10c85740f825b1c543d58c0f475615c667020bc1aa2825`.
Parent released the attempt after non-author depth review on 25 October 2026.
The branch is M-positive: the asserted theorem proves specified failures of
reconstruction, rather than offering an obstruction instead of the obligation.

## 1. Parameters, equality, maps and dependency boundary

Fix any finite category K, with literal objects and actual arrows. The proofs
work for any small category; the contractual family is the finite one. Write
[m]={0,...,m-1} and U_m={{x,y}:0<=x<y<m}. An ordered simple graph G=(m,E) has
E subset U_m. Equality is equality of m and E, not graph isomorphism. A component
is (A,B,G,a) where a:A->B is an arrow of K. A path retains every intermediate
object and arrow, as well as the ordered graph components at its occurrences.

For B subset [m], epsilon_B:[|B|]->[m] is the increasing enumeration. The
ordered induced graph G|B has vertex count |B| and edges
{r,s} precisely when {epsilon_B(r),epsilon_B(s)} belongs to E. C1 proved the
canonical restriction identities and all-arity lawful substitution, including
empty blocks. We use that construction, not a newly defined quotient.

An arity-k ordered partition B=(B_0,...,B_(k-1)) is pairwise disjoint and has
union [m]; empty entries are retained. A total cut witness is

    w=(G,a,p,B),  p=((G|B_i,a_i))_i,  a=a_(k-1) ... a_0,

with the full typed composable arrow string in p. Write Cut_K for the disjoint
union of these witnesses over all finite m,k and outputs. Its actual maps are

    Whole:Cut_K -> components,              w |-> (G,a),
    Leaves:Cut_K -> typed ordered paths,    w |-> p,
    Blocks:Cut_K -> finite block tuples,    w |-> B.

For k=0 the only partition has m=0, p is empty at A and a=id_A. An empty block
inside a nonempty path need not have identity grade; none of our arguments
deletes that arrow. The optional bound m<=N from C1 is closed under cut
substitution, but arity/depth remain unbounded. All main graph theorems below
quantify over unrestricted finite sizes and arities.

Let S_bin be C1's actual typed binary-cut plus designated-nullary signature.
Let T_K be the disjoint union of its finite raw typed presentations over their
whole components. The identity presentation is an external edge/leaf, not a
nullary primitive node. A2/C1 supply the strict evaluation

    Ev_G:T_K -> Cut_K.

Define Out(T) to be its root component; Front(T) the complete ordered typed
frontier; Shape(T) the planar tree retaining internal arities and external
leaves but erasing all labels; Lab(T) the finite partial function on internal
planar vertex addresses taking the actual primitive value at that address.
The shape distinguishes a nullary internal node from an external leaf. These
are object maps, not a claim about faithfulness of a category functor.

For C2, fix an arbitrary family of finite carrier sets X_i. Components are
(i,j,R) with R subset X_i x X_j. Its containment fibre at (p,W) is a singleton
if the path composite C(p) is contained in W, and empty otherwise; the exact
fibre instead requires equality. A total semantic cell retains p and W.
Primitive symbols and realizing tuples for existential composition are NOT
extra data of this thin semantic cell. Sections 6–7 name the particular
interpretation and observation maps used here.

Dependencies are accepted A1–A3/B1–B2 and the locally verified C1/C2 model
constructions. Full C1 remains OPEN for C5/F2, and full C2 for D2/E. Their
pending use gates are not missing assumptions of their local theorems. No
new B3/B4, presentation completeness, equipment, 2-Segal or G/I theorem is used.

## 2. Anchored graph restriction fibres — arbitrary finite size

Fix m,k and an ordered partition B of [m]. Define

    I_B = union_i {{x,y}: x,y in B_i, x!=y},
    X_B = {{x,y} in U_m: x and y belong to different blocks}.

Disjointness/exhaustivity of B gives the disjoint union U_m=I_B disjoint-union
X_B: every pair has either the same unique block label or two different ones.
The sets of pairs inside distinct B_i are also disjoint. Let Graph_m=P(U_m).
The actual anchored restriction map is

    rho_B:Graph_m -> product_i Graph_|B_i|,   E |-> (G|B_i)_i.

The partition is a FIXED INDEX of this map, not returned in its codomain.

**Theorem 2.1 (full anchored fibre, both inverses).** For every tuple of
ordered simple graphs H_i=(|B_i|,F_i), there is a bijection

    rho_B^(-1)((H_i)_i) <-> P(X_B).

In particular every such tuple is realizable. The forward map sends G to
E_G intersect X_B. Define its proposed inverse on C subset X_B by

    E(H,B,C) = C union union_i
       {{epsilon_Bi(r),epsilon_Bi(s)} : {r,s} in F_i}.       (2.1)

Proof. Each epsilon_Bi is injective, so the lifted pairs are distinct-vertex
pairs; they lie in U_m and within B_i. Thus (2.1) defines an ordered simple
graph on the prescribed [m]. No C-pair has both endpoints in B_i. No lift
from B_j, j!=i, has endpoints in B_i. Consequently restricting (2.1) to B_i
and pulling back along epsilon_Bi yields exactly F_i. This proves the inverse
lands in the specified fibre, including empty blocks and empty edge sets.

For C subset X_B, intersecting (2.1) with X_B returns C, since all lifted
within-block pairs lie in I_B. Conversely take G in the fibre. For any pair
e in U_m, if e belongs to X_B, (2.1) includes it exactly when G does. Otherwise
its two vertices lie in a unique B_i, and unique preimages r,s under epsilon_Bi
give e in E_G iff {r,s} in F_i, by the fibre condition. Hence (2.1) recovers
every bit of E_G. Extensionality gives G back. These are both inverse laws;
the assertion is a full fibre classification, not only a family of examples.
QED.

**Corollary 2.2 (cardinality and exact injectivity boundary).** Every fibre has

    2^q elements,     q=|X_B|=sum_(i<j) |B_i| |B_j|.        (2.2)

For i<j, the map (x,y) |-> {x,y} from B_i x B_j is injective: disjoint block
membership recovers which endpoint belongs to which block. Its images for
different unordered pairs of block indices are disjoint, and together exhaust
X_B. This proves the count of q; the powerset count and Theorem 2.1 give (2.2).

The map rho_B is injective iff X_B is empty, equivalently at most one B_i is
nonempty. If X_B is empty, all fibres are singletons. If it contains e, then
the inverse images of C=empty and C={e}, for ANY prescribed H, are distinct
but have the same rho_B-image. Finally X_B is nonempty exactly when there are
two nonempty blocks: choose one vertex in each for one direction, and use the
two block labels of a cross pair for the other. This includes m=0 and k=0.

**Corollary 2.3 (uniform nonreconstruction).** If at least two blocks are
nonempty, there is no map r from the ordered block-graph tuple to Graph_m
with r(rho_B(G))=G for every G in Graph_m. Indeed the two distinct graphs just
constructed have one image, so one value r(H) cannot equal both. More
strongly, for EVERY prescribed block tuple the ambiguous data are exactly q
independent binary choices, not merely one missing edge. For arbitrarily large
families take two blocks of sizes s,t>=1 and any internal graphs; the fibre
has 2^(st) elements. Other blocks, categories and composable grades can be fixed
arbitrarily. This is the unrestricted simple-graph claim required by C3.

## 3. The actual leaf-only map, forgotten placements and exact repair

Theorem 2.1 knows the ambient blocks B. The map Leaves on total cut witnesses
does NOT retain those blocks. We now compute its different, larger fibre.

Fix any typed composable finite path

    p=((H_0,a_0),...,(H_(k-1),a_(k-1))),

where H_i has n_i vertices, and put m=sum_i n_i. For k=0, p includes its single
interface and the composite arrow is its identity. Let Part(n) be all ordered
partitions B of [m] satisfying |B_i|=n_i. Write Cut_K(p)=Leaves^(-1)(p).

**Theorem 3.1 (full unanchored leaf fibre).** There is an explicit bijection

    Cut_K(p) <-> disjoint-union_(B in Part(n)) P(X_B).      (3.1)

Its cardinality is

    m! / (product_i n_i!) * 2^(sum_(i<j) n_i n_j).          (3.2)

Proof. For any witness with leaves p, partition exhaustivity forces its whole
graph to have m vertices. Its whole arrow is forced to be comp(p), including
the precise endpoints. Its actual Blocks value belongs to Part(n). Sending
it to (B,E_G intersect X_B) is therefore well-defined. Conversely, given this
pair, use (2.1) for the graphs H_i and give its whole the arrow comp(p). The
profile is exactly p by Theorem 2.1; the supplied B is exhaustive and disjoint.
Thus this is a valid C1 total witness. The two inverse laws follow from those
of Theorem 2.1 and retaining the SAME B on both sides. No graph isomorphisms
or unordered block identifications are used.

To count Part(n), take permutations of [m], cut each into consecutive lists
of lengths n_0,...,n_(k-1), and forget each list's internal order. Every desired
ordered partition is reached. Exactly product_i n_i! permutations reach it,
because the within-list orders can be chosen independently. Therefore Part(n)
has m!/product_i n_i! elements. Every summand in (3.1) has the common size
2^(sum_i<j n_i n_j) by (2.2), proving (3.2). Empty factors use 0!=1. With k=0
we have m=0, one empty partition and one empty cross-edge subset, giving the
unique valid nullary over the empty identity-graded whole. QED.

Formula (3.2) counts WITNESSES. It does not count distinct whole graphs after
forgetting B: different summands may give the same graph. In particular,
permuting two singleton blocks can leave the whole unchanged. Theorem 2.3
already proves failure to reconstruct even the whole on an anchored subfamily;
removing B cannot repair that failure. Conversely whole equality need not
recover the witness even when p is fixed, as Section 4 shows.

**Theorem 3.2 (exact data repair and its negative controls).** The map

    Repair:Cut_K -> records, w |-> (Leaves(w), Blocks(w), E_G intersect X_B)

is injective. A left inverse on its image is the explicit construction (2.1)
and whole grade comp(p); its values lie in Cut_K by Theorem 3.1. Indeed two
equal records give equal p,B and cross-edge sets, hence equal G and grade,
so all witness fields agree. It is a bijection onto the admissible records
described in (3.1), not onto arbitrary ill-typed triples.

This is a precise positive repair, with precisely scoped failures when data
are removed. Fix any B with a cross pair e and any H. The two witnesses
constructed with C=empty and {e} have the same record when cross-edge data
are deleted, and even when only that particular cross-edge bit is deleted.
Thus neither the reduced record nor a decoder that omits e is injective on
this full anchored family. To delete B instead, use the two witnesses of
Section 4: they have the same p and same cross-edge set {{0,1}}, but different
B. This also shows failure if B is retained only as an unordered block family.
These are actual maps on supplied domains. We make no lower-bound or minimal
repair claim for arbitrary observational models (the separate G/I workstream).

## 4. Same whole/profile/shape does not mean same witness or label

Use K=[2], the category with objects 0,1,2 and one arrow i->j iff i<=j. Let
H be the ordered two-vertex graph with its edge {0,1}, grade id_1. Let Q be the
one-vertex edgeless graph, also graded id_1. Define two C1 binary witnesses

    u=((H,id_1), [(Q,id_1),(Q,id_1)], ({0},{1})),
    v=((H,id_1), [(Q,id_1),(Q,id_1)], ({1},{0})).             (4.1)

Both are valid: both ordered tuples partition [2], each induced graph is Q,
and id_1 composed with id_1 is id_1. They have equal Whole and equal Leaves.
They are DISTINCT because their first blocks differ. Both cross-edge sets
are {{0,1}}. This verifies all assertions about (4.1) used in Section 3.

S_bin includes separate primitive values g_u,g_v for these different supplied
cuts. Let U and V be their corollas with identity leaf children. Then
Out(U)=Out(V), Front(U)=Front(V), Shape(U)=Shape(V), but their root labels
differ, so Lab(U)!=Lab(V) and U!=V. Evaluation gives u and v by the unit law,
hence Ev_G(U)!=Ev_G(V). Thus a graph model can distinguish these primitive
labels even though tree shape, whole and profile cannot. The label distinction
is not an extra arbitrary decoration: it is the retained partition itself.

**Theorem 4.1 (faithful full syntax encoding).** For every typed signature,
including S_bin, Enc(T)=(Out(T),Shape(T),Lab(T)) is injective on finite trees.

Proof. Given a valid encoding, reconstruct by induction on the shape. If it
is an external leaf, the only possible tree is the identity edge at Out(T).
This is why the root component is retained when there are no primitive labels.
If it is an internal vertex of arity r, the value of Lab at the empty address
specifies its primitive g, including output and its full ordered input path.
Its r children therefore have uniquely specified output component types.
For child j, the child shape is supplied by Shape, and its internal labels are
the restriction of Lab to addresses starting with j, with that first index
removed. Apply the induction to each such child using its prescribed output.
The root g and recovered children give the unique node. For r=0 there are no
children, so this recovers a nullary primitive, NOT an external leaf. Finite
structural induction terminates and shows two equal encodings give the same
tree at every node. All typing constraints hold because we reconstruct from
an encoding in the image; no existence claim for arbitrary inconsistent codes
is needed. QED.

Deleting Lab from Enc loses injectivity by U,V. Deleting Out also cannot work
uniformly: identity trees at different components have the same empty label
function and external-leaf shape. These are explicit negative controls for
the actual positive injection, not assertions that shape is itself injective.

## 5. The mixed six-vertex certificate and its full cross-edge family

Keep K=[2]. Put

    E_G={01,12,13,24,34,45},
    B=({0},{1,3},{2,4},{5}),
    (A_0,...,A_4)=(0,1,1,1,2).

Notation ij means the unordered pair {i,j}. Use the unique arrow A_i->A_(i+1)
on each block, and its composite 0->2 on G. B partitions [6]. The two middle
induced graphs are BOTH H from Section 4, since 13 and 24 are edges. Their
grades are BOTH id_1. Therefore they are identical nonempty component types,
but occupy distinct positions 1 and 2 in the full four-leaf path p. The two
outer leaf graphs are the one-vertex graph with grades 0->1 and 1->2.

Let T_bal have shape ((B_0 B_1)(B_2 B_3)) and T_right have shape
(B_0(B_1(B_2 B_3))). To define their actual typed primitive labels, at each
node take G induced on the union of its descendant blocks, standardized in
increasing order; cut it into the two child unions in those local coordinates.
The node arrow is the composite of its descendant leaf arrows. Each internal
cut is a valid S_bin generator: the two child unions partition the node set,
canonical restriction identifies the child graphs, and path composition gives
the node arrow. This describes complete trees, not just informal parentheses.

Explicit coordinates remove any possible ambiguity. T_bal's root blocks are
{0,1,3} and {2,4,5}; their child partitions are ({0},{1,2}) and ({0,1},{2}).
T_right's root blocks are {0} and {1,2,3,4,5}; the right child's local blocks
are ({0,2},{1,3,4}); the final pair in {2,4,5} again uses ({0,1},{2}). The
root grade is 0->2 in both trees. T_bal's inner grades are 0->1 and 1->2;
T_right's successive right inner grades are 1->2 and 1->2. All intermediate
objects and leaf grades are exactly those of p.

Evaluating a node substitutes its children's blocks through the increasing
enumerations of its two supplied blocks. For T_bal, the left child yields
{0},{1,3}, and the right child yields {2,4},{5}. For T_right, the right child
first splits into {1,3} and {2,4,5}, and the last cut splits the latter into
{2,4},{5}; the first external block is {0}. Thus BOTH evaluate to the FULL
witness w=(G,0->2,p,B), not merely to p. They are different raw trees: the root
left child is an internal binary node in T_bal and an external leaf in T_right.
Consequently both Front and Ev_G are noninjective even at fixed whole, mixed
interfaces and four nonempty leaves. A1 retains this difference; no syntax
equation was silently imposed to erase it.

At the middle occurrence B_1 choose u from (4.1), and at B_2 choose v. At the
outer occurrences choose identities. This is an actual tuple

    f=(1_(p_0), u, v, 1_(p_3)).                            (5.1)

The first middle replacement has local order ({0},{1}), so lifts to {1},{3}.
The second has local order ({1},{0}), so lifts to {4},{2}. The refined full
blocks are therefore ({0},{1},{3},{4},{2},{5}); the refined path is
0->1->1->1->1->1->2. In particular the originally identical component values
receive DIFFERENT valid substitutions. Collapsing occurrences by component
would force one order to be reused: using u twice gives
({0},{1},{3},{2},{4},{5}), while using v twice gives
({0},{3},{1},{4},{2},{5}). Neither is (5.1)'s result. This is not exchange;
the differing orders are supplied primitive cut data at specified positions.

For these blocks, the only possible within-block pairs are 13 and 24, which
are both fixed present. There are 15-2=13 cross pairs. Theorem 2.1 therefore
gives the COMPLETE 8192-element family obtained by choosing each of the other
13 pairs independently, while fixing those two internal edges. Every member
has the same p and repeated middle components, and every graph with those
restrictions is a member. G and G union {05} are two explicit members, with
different wholes. The proof of equal evaluation of the two groupings and the
occurrence calculation work for every member: their internal whole graphs
change as needed, and they retain those graphs at every primitive node.

For comparison, if B itself is also forgotten while p is fixed, Theorem 3.1
gives 6!/(1!2!2!1!) * 2^13 = 180*8192 = 1,474,560 TOTAL cut witnesses.
This larger number is not an enumeration claim about distinct whole graphs.
The finite certificate exhausts the anchored 8192 family; the full unanchored
formula is an all-size P consequence, with separate exhaustive m<=4 checks.

## 6. Relational separation: thin cells do not erase whole indices

For arbitrary C2 parameters, two containment semantic cells with the SAME
entire p and SAME W are equal, because the fibre is empty/singleton. Therefore
any two parallel presentation trees admitted by an interpretation into M_le
have equal evaluations: strict profile preservation and output typing place
them in that same fibre. This does not assert equality of trees or primitive
symbols. It also does not assert equality of cells whose W differ.

Here is a fully typed nondegenerate instance. Take three distinct interface
labels 0,1,2 with carriers X_0={0,1}, X_1={0,1,2}, X_2={0,1}. Define

    R:X_0->X_1 = {(0,0),(0,1),(1,2)},
    S:X_1->X_2 = {(0,0),(1,0),(2,1)},
    D:X_0->X_2 = {(0,0),(1,1)},
    W:X_0->X_2 = X_0 x X_2.

Existential composition R;S=D: input 0 reaches 0 and 1 in X_1 and both go
only to 0; input 1 reaches only 2, which goes only to 1. Each diagonal pair
is realized, and no off-diagonal pair is. Thus D is nonempty and D is a proper
subset of W. The cell a in M_le([R,S];W) exists and is NOT exact.

Define a signature S_rel on this actual relation quiver with two distinct
binary symbols alpha and beta, each with output W and full input path [R,S].
Assign both to a. A2 and C2's public calculus construction give the unique
strict map Ev_R:F(S_rel)->M_le with this assignment. Its alpha and beta
corollas have equal shape, whole and frontier but different primitive root
labels, hence different raw trees, whereas their Ev_R values are both a.
All typing and validity are explicit; no syntax quotient declares alpha=beta.

The same frontier [R,S] also admits the exact cell a_D with whole D and the
nonexact cell a_W with whole W. They are different TOTAL semantic cells,
because their retained whole components differ. Within the fixed-frontier
family the possible whole relations are exactly D union A with
A subset (X_0 x X_2) minus D: containment is the sole validity condition.
This last observation follows in both directions by set difference/union;
it illustrates C2 nonreconstruction without imposing equality semantics.
It is not a D2 interface-change theorem.

No existential realizing tuples are being counted as cells: for (0,0), for
example, intermediate values 0 and 1 are two realizations but still only one
membership fact and one cell at fixed (p,W). This distinction is essential to
the stated domain of Ev_R.

## 7. A named local observation, its entire support fibre and boundary

Fix any two finite sets X,Y (possibly empty). Use the C2 component fibre
Rel(X,Y)=P(X x Y) as the semantic-object domain. Define actual functions

    Truth:Rel(X,Y)->{0,1}^(X x Y),  Truth(R)(x,y)=1 iff (x,y) in R,
    Obs:Rel(X,Y)->P(X) x P(Y),       Obs(R)=(dom R, ran R).

The interfaces are fixed and retained by the choice of domain. Obs is merely
the specified local endpoint-support observation; it is not asserted to be a
calculus morphism, an adequate probe family or a general semantics/observation
identification theory. Truth is injective by extensionality of subsets: equality
of all membership bits is exactly relation equality.

**Theorem 7.1 (support-fibre description and sharp singleton boundary).** For
D subset X and Q subset Y, Obs^(-1)(D,Q) consists EXACTLY of the relations
R subset D x Q having no empty row indexed by D and no empty column indexed
by Q. It is empty if exactly one of D,Q is empty; if both are empty it is
the singleton {empty}. If both are nonempty it is nonempty, and is a singleton
iff min(|D|,|Q|)=1. If both cardinalities are at least two it has at least
two elements.

Proof. If Obs(R)=(D,Q), each pair in R has its first coordinate in D and second
in Q. Every element of D occurs in some pair by domain equality, and every
element of Q occurs by range equality: these are exactly the row/column
conditions. Conversely these conditions force dom R=D and ran R=Q. If one
support is empty, R has no pairs, so the other support must also be empty.
Both empty supports force R=empty, which has those supports.

For nonempty D,Q, the full rectangle D x Q has both required supports, so the
fibre is nonempty. If D={d}, the nonempty column at each q forces (d,q) in R;
hence R=D x Q. If Q has one element, the analogous row argument forces the
same conclusion. If both have at least two elements, choose distinct d0,d1
in D and q0,q1 in Q. Both D x Q and (D x Q) minus {(d0,q0)} have full supports:
the affected row still contains (d0,q1) and affected column still contains
(d1,q0), and all other rows/columns are unchanged. They are distinct. This
proves every case and both directions of the singleton criterion. QED.

Thus Obs on the ENTIRE Rel(X,Y) is injective iff |X|<=1 or |Y|<=1. In the
forward direction each existing support fibre is singleton by Theorem 7.1
(including empty carriers); in the reverse direction take D=X,Q=Y with both
sizes at least two. This is a property of this chosen observable only.

For a sparse unequal-cardinality counterexample use X=X_0={0,1}, Y=X_1={0,1,2}
from Section 6 and the two relations

    R0={(0,0),(0,1),(1,2)},
    R1={(0,0),(1,1),(1,2)}.

Both have domain {0,1} and range {0,1,2}; they differ on (0,1) and (1,1).
Therefore equal Obs values do not imply equal semantic components, while
Truth distinguishes them. Converting the full truth table into mere support
sets is an executable negative control that destroys the positive injectivity.
It does not show that every possible observation loses information.

## 8. Separation matrix with actual map domains

Every equality implication below concerns the displayed domain. Equality of
an object always implies equality of its images under functions; the content
is which converses fail and what data restore an injective representation.

| Distinction | Domain and actual map(s) | Proved conclusion and certificate |
| --- | --- | --- |
| Same frontier / same tree | T_K; Front:T_K->typed ordered paths | Tree equality implies frontier equality. Converse fails even at fixed Out: T_bal!=T_right have Front=p (Section 5). Enc restores the full typed tree (Theorem 4.1). |
| Same shape / same primitive labels | T_K; Shape:T_K->planar arity trees and Lab:T_K->address-labelled primitive functions | U,V in (4.1) have equal shape, output and frontier but different root labels. Enc=(Out,Shape,Lab) is injective; erasing Lab is not (Section 4). Shape alone never purports to remember primitive values. |
| Same leaf types / same whole | Cut_K; Leaves and Whole | For each B and fixed H, Leaves is fixed along the entire 2^q family, whereas Whole distinguishes every anchored graph (Theorem 2.1). G and G+05 in Section 5 give an explicit mixed example. The entire Leaves fibre including unknown B is (3.1), not just P(X_B). |
| Same whole / same witness | Cut_K; Whole:Cut_K->components (and its restriction to Cut_K(p)) | Whole equality fails to determine witnesses even at fixed p: u!=v of (4.1). Graph whole equality does not specify ambient ordered blocks. Repair is injective and explicitly invertible on admissible records (Theorem 3.2). |
| Same evaluated witness / same presentation | T_K with Ev_G, and F(S_rel) with Ev_R | Presentation equality implies evaluation equality. Converse fails for T_bal/T_right with equal FULL graph cut (Section 5), and alpha/beta with equal relational cell (Section 6). Graph evaluation nevertheless separates U,V; C2 is thin only at fixed (p,W). No syntax congruence is silently equated with these kernels. |
| Same observation / same semantic object | Rel(X,Y), fixed interfaces; Obs to endpoint supports | R0!=R1 have equal Obs (Section 7). Exact fibres and singleton boundary are Theorem 7.1. Truth is injective; its support-only reduction is not when both carriers have at least two elements. |

Rows 3 and 4 are not logical converses of each other: they compare different
projections from the same total-witness domain. Row 5 is a further projection
from presentations to witnesses. In particular all of the following coexist:
different wholes with identical leaf types; different witnesses with identical
whole and leaf types; and different raw presentations with identical entire
evaluated witness. Treating any two of these maps as one is refuted by the
displayed examples. The table makes no unsupported universal yes/no claim
about unspecified models or observations.

## 9. Exact B2 interpretation linkage and occurrence caveat

For each fixed whole c, B2 constructs Ref(M,c) with objects all M operations
of output c and arrows a->a' given by full occurrence-indexed tuples (b_i)
with a[b_i]=a'. Their entry profiles and lengths remain arrow data. Applying
the accepted B2 interpretation construction to the strict Ev_G yields

    Ref(Ev_G,c):Raw(S_bin,c)->Ref(Cut_K,c),
    T |-> Ev_G(T),     (F_i)_i |-> (Ev_G(F_i))_i.            (9.1)

The entry indices are the actual original leaf occurrences, transported by
the accepted full-profile/leaf equivalence, not keys given by component value.
Ev_R yields the identical formula with M_le. These are actual established
functors: A2 gives strict substitution/identity preservation and B2 supplies
the category and tuple-composition proof. We are instantiating those proved
maps, not assuming a new quotient category or completion theorem.

The raw middle-branch corollas for u,v are valid forest entries above either
four-leaf presentation in Section 5. Under (9.1) their evaluations occupy the
distinct middle positions exactly as in (5.1); the other entries evaluate to
identities. The functor's target object is the refined full cut calculated
there. In particular it retains u!=v at these entries, whereas deduplicating
by identical input component would give the wrong tuple and wrong target.

The object map of (9.1) is not injective by T_bal,T_right. B2's sufficient
operation-injectivity criterion for reflecting object equality therefore does
not apply. This is NOT failure of categorical faithfulness: raw refinement
hom-sets are subsingletons by accepted B1, so every raw-source functor is
injective on each fixed hom-set. Distinct objects can have one image even for
a faithful functor. Nor do the two different-target refinements computed in
Section 5 alone prove nonthinness at a fixed target. No new fullness,
nonthinness classification, refinement-fibre recovery or B3/B4 claim follows.

Likewise Ev_R's alpha/beta object collapse concerns (9.1)'s object map.
The thinness of M_le(p;W) is not a license to erase entry profiles or occurrence
segmentation in a semantic refinement arrow. Such erasure would change B2's
arrow definition and is expressly excluded.

## 10. Evidence limits, finite scope and mathematical credit

All-size assertions in Sections 2–4 and 7 are complete P proofs by explicit
inverse maps, finite counting, structural induction and elementary set
arguments. Their X certificates are fully typed in Sections 4–7. The fixed
graph and relation calculi and general interpretation laws are already
verified dependencies. No new Lean theorem is asserted by this document;
rebuilding inherited Lean evidence checks those inputs, not these P proofs.

Separate finite C evidence enumerates every ordered graph on m=0..4 and every
ordered partition [m]->[k] for k=0..5, retaining absent labels as empty blocks.
It is exhaustive only in THAT finite domain, not in the infinitely many
arities available even at m=0. Arrow strings of [2] can be checked separately
because graph membership/restriction/cross-edge reconstruction never inspects
grades, while typing/composition in the chain never inspects edges or block
memberships. For each k the same graph/partition domain pairs with all weakly
increasing strings of k+1 objects. Its endpoints and each arrow are uniquely
determined by that string; the whole grade is their composite. Equality of
full witnesses is equality of those independent fields. This is the precise
product justification, not a deletion of empty-graph arrows. Physically
executed cases and represented typed products are reported separately.

The six-vertex checker must independently build/evaluate the actual trees and
test all 8192 anchored variants. The observation checker enumerates all relation
matrices of sizes a=0..2 and b=0..3. Neither finite run proves an unrestricted
theorem; independently implemented C and mathematical P reviews are distinct.
Negative controls must execute the lossy maps or incorrect reconstructions,
not simply assert an expected-failure flag. Fresh source reproduction and
preservation of all 578 baseline files are separate verification gates.

The fibre theorem is an elementary coordinate decomposition of a simple-graph
edge set; support fibres are elementary relation facts; syntax encoding is
structural reconstruction. These are necessary, precise C3 information-loss
results on the shared models, not claimed discoveries or standalone major
novelty. C4 literature comparisons, G/I observation/recovery, and the integrated
presentation/refinement bundles are not discharged. C1/C2 downstream gates,
A4/B3/B4/C5 and all other workstreams retain their existing status. Agent-managed
review has correlated-model limitations and is not external human certification.

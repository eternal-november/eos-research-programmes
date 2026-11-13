# C1: the ordered graph-cut calculus, uniformly in size and category

Contract v0.1, unchanged SHA-256
`47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e`.
Target `../C1_Targets.md`, SHA-256
`7a5d4bb8dd3aa0715c82b73b8c169def2935b98f41addfd0eaaf03a606be244e`.
Evidence level: P (complete mathematical argument submitted for independent
review), with a separately itemized L fragment and C certificates. Branch M,
positive only. No C5 completeness, B3 comparison-completion, or F2 simplicial
claim is made. Full C1 acceptance remains OPEN pending C5/F2 use.

## 1. Parameters, carriers, equality and retained information

Fix any small category K. Its objects and each hom-set are sets; composition
is a function and obeys the category axioms at equality, not up to additional
2-cells. Finite K is the contractual subfamily, meaning finitely many objects
and arrows. No thinness, cancellativity, invertibility, or unique factorization
is assumed. Work in sets with literal ordered graph equality.

Write [m]={0,...,m−1}. An ordered simple graph is a pair G=(m,E) with
E⊆{{x,y}:x,y∈[m],x≠y}. Equivalently its adjacency is a symmetric irreflexive
Boolean function on [m]². Both m and every adjacency bit are graph data.
For objects A,B put J(A,B)={(G,h):h∈K(A,B)}. A component c includes its source
A, target B and this pair. Optionally require m≤N, for any fixed natural N.
Equality of components compares endpoints, m, adjacency and the actual arrow;
isomorphic but differently labelled graphs and distinct parallel arrows are
not identified.

A profile p is the entire finite composable sequence
((G₀,h₀):A₀→A₁,...,(Gₙ₋₁,hₙ₋₁):Aₙ₋₁→Aₙ), including all intermediate objects
and actual arrows. It is exactly a `Quiver.Path` for quiver J in the accepted
A library. Its slots are ordered occurrences, not a set of component values.
For an empty path n=0 there is one endpoint A₀. Define comp(p) as the composite
of its arrows in their traversal order, with comp(empty_A)=id_A. Parentheses
may be fixed to the accepted snoc convention; all changes use category laws.

An ordered partition B of [m] of arity n is a tuple (Bᵢ)ᵢ∈[n] of subsets,
pairwise disjoint with union [m]. Empty blocks are permitted and RETAINED.
Thus the number and positions of empty blocks are retained. Exchanging equal
empty entries does not create new tuple data; their slot indices nevertheless
remain distinct occurrences. The sequence need not follow ambient vertex order. Each individual block
has its inherited increasing order.

For B⊆[m], let ε_B:[|B|]→[m] be its unique increasing bijection onto B. Define
G|B on [|B|] by E_(G|B)(x,y)=E_G(ε_B(x),ε_B(y)). Graph symmetry and
irreflexivity are inherited. In particular G|[m]=G and G|∅ is the empty graph.

**Definition (full flat cut).** For a fixed output c=(G,h):A→B,
`FlatCut.Op c` consists of a profile p:A→B and an ordered partition (Bᵢ) of
[m], indexed by its actual slots, subject to

* at slot i the graph of pᵢ is literally G|Bᵢ;
* comp(p)=h.

The equality proofs are constraints, not additional distinguishing witness
values. This is an independently defined graph/partition carrier, not a tree
carrier or quotient by all semantic equalities. Its fibre at prescribed p is
`FlatCut.Operation c p`. A total witness is (c,p,(Bᵢ)); its whole c retains all
cross-block edges and the whole arrow. Its input leaf at i stores only
(G|Bᵢ,hᵢ), not Bᵢ, ε_Bᵢ, the other leaves, or the whole graph. The witness stores
those ambient blocks and the FULL typed arrow string via p. It may therefore
have the same leaves as another witness without equalling it. Output indexing
is storage of the whole in a dependent index, not deletion of the whole.

## 2. Canonical restriction lemma

For U⊆[m] and V⊆[|U|], write U[V]=ε_U(V). Then |U[V]|=|V| because ε_U is
injective. Both ε_(U[V]) and ε_U∘ε_V are increasing bijections from [|V|]
onto U[V]. A finite increasing enumeration is unique: its first value is the
least element of the image, and removing it reduces to the same argument on
the remaining ordered set. This induction includes the empty domain. Hence

    ε_(U[V]) = ε_U ∘ ε_V.                             (R1)

For x,y∈[|V|], applying the two graph restriction definitions gives

    E_((G|U)|V)(x,y)
      = E_G(ε_U(ε_V(x)),ε_U(ε_V(y)))
      = E_(G|U[V])(x,y).

Vertex counts agree, so

    (G|U)|V = G|U[V]                                  (R2)

as actual ordered graphs. No graph isomorphism quotient is used. For
W⊆[|V|], (R1) also gives equality of subsets and embeddings

    (U[V])[W] = U[V[W]],
    ε_(U[V])∘ε_W = ε_U∘ε_V∘ε_W.                     (R3)

The displayed domains on both sides are [|W|]. This explains all later
coordinate transports, including noncontiguous U and reversed block order.

## 3. Path-composition lemma

If p:A→B and q:B→C are profiles, comp(p·q)=comp(q)∘comp(p).
Proof: induction on the snoc construction of q. For q empty the equality
is the right endpoint identity law; for q=q' followed by arrow k, induction
and associativity give k∘(comp(q')∘comp(p))=
(k∘comp(q'))∘comp(p). Now if each slot i of p is replaced by a composable
path qᵢ with the same endpoints and comp(qᵢ)=hᵢ, repeated application gives

    comp(expand(p,q)) = comp(p).                      (P1)

This induction works for empty p and for empty qᵢ. An empty qᵢ forces its
endpoints to be equal and hᵢ=id, so dropping it creates no endpoint mismatch
and removes precisely an identity factor. In nonthin categories this statement
compares actual arrows, not only endpoint pairs.

## 4. Substitution is defined on every prescribed occurrence family

Let w=(c,p,(Bᵢ)) be an operation. Independently for EACH slot i of p, choose
vᵢ=(pᵢ,qᵢ,(Cᵢⱼ))∈FlatCut.Op(pᵢ). Here Cᵢⱼ are in [|Bᵢ|], j ranges over
slots of qᵢ, and comp(qᵢ)=hᵢ. Define w[v] to have:

* unchanged whole c=(G,h);
* profile expand(p,q), concatenating the entire qᵢ in order;
* block Bᵢ[Cᵢⱼ] at position (i,j), in lexicographic order.

The formal slot of this position is the inverse of A's `Path.slotExpand`
equivalence from expanded slots to pairs. An empty qᵢ contributes NO position;
an empty Cᵢⱼ still contributes ONE position. This difference is data, not a
convention erased after composition.

**Well-definedness.** Each new block is a subset of Bᵢ. Blocks from different
i are disjoint; for the same i, injectivity of ε_Bᵢ sends disjoint Cᵢⱼ to
disjoint subsets. Their union within i is ε_Bᵢ([|Bᵢ|])=Bᵢ. Thus their total
union is [m]. This remains true when qᵢ is empty: its partition constraint
forces |Bᵢ|=0. By (R2), the graph of the jth input of vᵢ is
(G|Bᵢ)|Cᵢⱼ=G|Bᵢ[Cᵢⱼ], so it is precisely the graph of the new block. The actual
arrow profile is qᵢ, with correct boundary at each concatenation; (P1) gives
whole composite h. All constraints of FlatCut.Op c hold. The new advertised
profile is exactly expand(p,q), not merely a path with equal endpoints.

The identity operation 1_c has profile [c] and the single block [m]. It
exists also when m=0 and when h is nonidentity. It is a unary operation,
not a primitive nullary and not a category identity arrow assumption.

## 5. Full calculus laws

**Right unit.** Substitute 1_(pᵢ) at each slot of w. Its local partition is
([|Bᵢ|]), so the resulting slot (i,0) has block
ε_Bᵢ([|Bᵢ|])=Bᵢ, arrow hᵢ, and graph G|Bᵢ. Singleton expansion identifies the
ordered profile with p, and the unchanged whole is c. Thus w[1]=w as a full
flat witness, under the canonical singleton-profile equality.

**Left unit.** In 1_c the only outer block is [m] and ε_[m] is the identity.
Substituting arbitrary w of output c gives its same profile and every same
block. The whole is still c. Thus 1_c[w]=w, including nullary w.

**Associativity.** Choose w, vᵢ as above, and an arbitrary operation zᵢⱼ at
every slot (i,j) of w[v]. Write its profile rᵢⱼ, and its blocks Dᵢⱼₖ in
[|Cᵢⱼ|]. Typing at this point is legitimate because (R2) identifies the
whole graph of zᵢⱼ whether that input is viewed inside vᵢ or w[v].
The left substitution (w[v])[z] has, at its occurrence ((i,j),k), block

    ε_(Bᵢ[Cᵢⱼ])(Dᵢⱼₖ).

The right substitution w[(vᵢ[zᵢ,*])ᵢ] has, at occurrence (i,(j,k)), block

    ε_Bᵢ(ε_Cᵢⱼ(Dᵢⱼₖ)).

(R1) equates these subsets. Both orders visit precisely the same triples
(i,j,k) lexicographically; regrouping pairs changes no order, does not merge
equal component values, and inserts or removes no empty block. Their full
arrow strings consist of the same innermost rᵢⱼ in the same order, with the
same intermediate interface objects. Their whole remains c. These are all
data fields, so the two full witnesses are equal after the canonical profile
associator `Path.expand_assoc`; `Path.slotExpand_assoc` identifies the actual
slot transports. Graph typing follows (R2) iterated, and whole
arrow grading follows (P1); neither requires cancellation in K. If an outer,
inner, or final arity is zero, its triple-index fibre is empty and the same
argument applies without exceptions. This proves associativity for every
finite occurrence family, not just binary substitutions or a finite sample.

Consequently FlatCut is an actual path-profile nonsymmetric multicategory.
In the accepted Lean API, `Collection.Op`, `profile`, `CalcData.identity`,
`profile_identity`, `subst`, `profile_subst` are the definitions and proofs
in §§1,4; `Calc.subst_identity`, `identity_subst`, `subst_assoc` are exactly the
three laws above. `CalcData.innerFamily` is the pullback from expanded slots
to (i,j), and `composeFamily` is the family used on the right of the
associativity proof. The argument therefore fills each actual `Calc` field;
it does not replace its arbitrary-profile quantifier by a structural recursion
only available for trees. This construction is P, not claimed fully L.

## 6. Nullaries, bounds, and finiteness

A zero-ary partition has union ∅. Hence a nullary operation over c=(G,h):A→B
exists iff m=0, A=B, and h=id_A. Necessity follows separately from partition
coverage, the type of an empty path, and comp(empty_A)=id_A. Sufficiency is
the empty block tuple and empty path. When it exists it is unique in this
undecorated model. This does NOT identify 1_(empty,id_A), with one empty block,
with the nullary operation, which has zero blocks and no leaf occurrence.
An empty graph with a nonidentity loop arrow or unequal endpoints has no
nullary operation, although it always has its own unary identity operation.

For any N, let J_N contain graphs of at most N vertices and let FlatCut_N
have the same operations with outputs in J_N. Every graph appearing in a
profile or a nested substitution is a restriction of its retained whole,
so has at most m≤N vertices. Identities and all substitutions remain in J_N.
There is no bound on arity, number of empty blocks, tree depth, or path length.
This proves the claimed closure for every N, particularly N=6. It is not a
truncation of operation composition.

For finite K and fixed n, all bounded total witnesses are finite in number:
there are Σ_(m=0)^N 2^(m(m−1)/2) possible ordered graphs; a partition into n
labelled blocks corresponds to a function [m]→[n], of which there are n^m
(with the usual unique empty function when m=0, including n=0). There are
finitely many n-arrow composable strings in K. Their composite determines
the whole arrow. Empty n=0 is treated as one empty string at each object.
These bounds prove fixed-arity finiteness. They do NOT assert a finite total
operation carrier across all arities; arbitrarily many empty blocks exist.

## 7. Connection to accepted A1–A3 and B1–B2

Use quiver J_N from §1. A primitive signature S_bin (finite when K is finite) has:

* for each G≤N, ordered bipartition (U,V), and composable arrows
  a:A→B, b:B→C, a generator with output (G,b∘a) and input path
  ((G|U,a),(G|V,b));
* for each A, one nullary generator with output (empty,id_A).

Each field of A's `Signature` is now supplied; there is no generator for a
mere identity tree. Assign each binary/nullary generator to its indicated
FlatCut_N operation. Graph/arrow typing is proved in §§1–4, including each
primitive's exact input path. A2's `Tree.extend` gives the unique strict
calculus homomorphism Ev:`Tree.freeCalc S_bin`→FlatCut_N extending this
assignment. Its map on trees is the recursive semantics: identity leaves map
to identities and each node substitutes its evaluated children into its
primitive cut. Its profile is the full `Tree.frontier`; strict substitution
preservation is part of A2, not assumed from the word “evaluation”.

For the selected A3 check, declare the following parallel templates only:
rotation of a three-block cut and left/right elimination of the designated
nullary unit. A rotation starts with G, ordered triple partition (U,V,W),
and arrows a,b,c. One tree groups U∪V then W; the other groups U then V∪W.
Inner blocks are pulled back by the increasing enumeration of the grouped
support. (R2) identifies the three input graphs, category associativity
identifies the output arrow, and the entire input path is the SAME. For a
unit equation the empty side has grade id and no external leaf; the other
side retains the original input path and whole. Thus these are valid
`Presentation.Equations` templates, not equations between merely equal-length
or equal-endpoint profiles. Their evaluations agree as full witnesses by
§§4–5: rotation gives (U,V,W) and the same actual arrows; the unit templates
give the original singleton full cut. A3's `Presentation.extend` therefore
factors Ev through the least parallel substitution congruence generated by
these declared equations. This is soundness and universal factorization,
NOT a claim of completeness or a C5 semantic-presentation theorem.

The C1 binary groupings in §8 are connected by the rotation template with
its third identity leaf substituted by the remaining binary subtree, so this
is an actual use of A3's substitution closure. Both outputs and all external
input graphs/interfaces remain parallel. It follows independently from the
explicit flat calculation that A2/A3 support the example.

B1 constructs actual raw leaf-indexed refinement arrows; its forest addresses
separate the two equal middle colours. B2 applied to the strict Ev gives the
semantic refinement functor: it maps a raw tree to its full cut and a graft
forest to the tuple of evaluated inner cuts, with their individual profiles.
Its identity/composition laws are the accepted B2 laws for arbitrary Calc.
The explicit different refinements below occupy separate tuple entries. We
claim no new fullness/faithfulness theorem, quotient-category identification,
semantic nonthinness classification, or chronological-history reconstruction.
The existing accepted B2 example, not C1's opposite splits alone, supplies its
previously required nonthinness test.

## 8. Frozen six-vertex certificate for independent L/C checking

Take K=[2], the three-object chain 0≤1≤2, N=6. Let G have edges
{01,12,13,24,34,45}. Set B₀={0}, B₁={1,3}, B₂={2,4}, B₃={5} and interface
sequence (0,1,1,1,2). These blocks partition [6]. Both B₁ and B₂ induce the
same ordered two-vertex graph with one edge, and both grades are id₁.
They are literally identical nonempty component colours, not merely
isomorphic graphs with distinct type labels.

At the B₁ occurrence choose the binary cut with local blocks ({0},{1}); at
the B₂ occurrence choose the binary cut ({1},{0}). Both have grade sequence
(id₁,id₁), but their ordered local partitions differ. Since both leaf graphs
are one-vertex graphs, these are parallel DISTINCT witnesses with the same
whole and profile. The occurrence family may choose them independently.
Keeping outer occurrences as identities yields ambient blocks
({0},{1},{3},{4},{2},{5}). If component equality were used to identify the
middle occurrence choices, one would instead repeat a single local order,
producing a different full cut. Refinement validity follows §4 even though
the second inner block order reverses the local vertex order; this is
supplied partition data, not exchange in the planar calculus.

Let T_bal=((B₀ B₁)(B₂ B₃)) and T_right=(B₀(B₁(B₂ B₃))). Every internal cut's
whole is the induced subgraph on its descendant union, standardized by ε.
For T_bal the top blocks are {0,1,3} and {2,4,5}; the inner partitions in
their canonical coordinates are ({0},{1,2}) and ({0,1},{2}). For T_right the
top blocks are {0} and {1,2,3,4,5}; its right child's blocks, in coordinates
of the latter, are ({0,2},{1,3,4}), and the final pair on {2,4,5} again has
coordinates ({0,1},{2}). Arrows at internal edges are the composites of
their descendant arrows. Applying (R1) gives flat blocks (B₀,B₁,B₂,B₃) in
both cases, with the same G and the same full path. The raw trees differ:
the root's left child is binary in T_bal and a leaf in T_right. This structural
difference is not removed in A1/B1 but their evaluations agree by A2/A3.

Let G⁺ add edge 05. It differs from G, and edge 05 meets B₀ and B₃, so none
of the four induced block graphs changes. Thus ordered leaf graphs and
arrows agree while the wholes and total cut witnesses do not. This is the
specified C1 information-loss example; no classification of all fibres, C3
acceptance, or failure of any 2-Segal law follows from it. The whole-retaining
model itself never discards 05 when evaluating a tree.

Boundary checks include empty blocks, empty identity leaves, true nullaries,
invalid partitions and invalid composable strings. The supplementary category
[2]×C₂ has arrows (a≤b,e), e∈{0,1}, composition by addition modulo 2. At
object 1 the arrow (1≤1,1) is a nonidentity loop: its empty graph has no
nullary, while (1≤1,0) does. This ensures the nullary grade check is nonvacuous.

## 9. Baseline credit, scope and stopping statement

The graph restriction/ordered-layer construction is established infrastructure,
not a claimed invention. Gálvez-Carrillo, Kock and Tonks, *Decomposition spaces
and restriction species* (arXiv:1708.02570), §2 graph example and §5 restriction
species, provide the baseline setting. The present argument proves the stated
ordered, arrow-typed set-level calculus directly. It does not import their
all-degree theorem as evidence for F2, nor claim novelty for adding interface
grades. Existing A4 local graph-rewrite artifacts are reused where explicitly
indexed; no extra research credit is assigned to redeveloping their elementary
model laws.

This theorem establishes the P part of the AUTHORIZED LOCAL C1 milestone.
Its L/C evidence and non-author reviews must be attached before LOCAL_VERIFIED
can be recorded. Full C1 remains OPEN because required C5/F2 uses are not
performed here. A1–A3/B1–B2 retain their previously accepted scope; A4 and all
later work retain their existing gates. Gate 1 can assess foundational
viability once the exact examples and comparisons above are independently
verified; it cannot certify whole-program, novelty or integration completion.

# A graph and finite span virtual equipment

## Results and scope

For every nonnegative integer N and finite commutative monoid M, the construction below gives a virtual equipment V(N,M) with vertical category finite sets and functions. Its horizontal arrows retain both a whole ordered graph with at most N vertices and a finite span. Its cells retain an actual ordered graph partition, an actual map of span witnesses, and one global M-value. Restrictions are cartesian for every source arity. The chosen nullary units are opcartesian in every surrounding horizontal context, not merely weakly opcartesian or solutions of unit equations.

For every finite category K, the full original graph-and-arrow calculus D(N,K,M) embeds into the identity-boundary part of this equipment, bijectively on each operation fibre over original horizontal profiles. The embedding separates entire retained wholes, repeated occurrences, nullaries, and scalar values. The model is generally not horizontally representable: for the full family of ordinary finite graphs, a horizontal path has a universal composite exactly when at most one of its graphs is nonempty. With at least two nonempty graphs and an adequate vertex bound, the obstruction is the choice of cross edges, not a scalar degeneracy or missing pullback.

This is an author-level P proof of a concrete ambient model and its exact comparison with the original core. It is standard construction-level infrastructure. It is not a construction of the free virtual-equipment envelope, not a fullness theorem for such an envelope, and not acceptance of E1–E5 or I4. The last section records the precise conditional equation-separation consequence that a subsequently proved free-envelope theorem could use.

## 1 Parameters and conventions

Fix N ≥ 0. Use the same ordered graph convention as the original core: a graph G has a vertex set [r] = {0,...,r−1}, r ≤ N, and equality includes its complete edge relation. For a subset U ⊆ [r], let i_U:[|U|]→[r] be its increasing enumeration and let G|U be the induced graph. The required identities are

    i_(i_U(V)) = i_U i_V,
    (G|U)|V = G|i_U(V).                                      (1)

These follow by uniqueness of increasing enumeration and by taking the inverse image of the edge relation. The empty graph is denoted 0. The equipment construction uses only induced restrictions. The nonrepresentability classification in Section 7 additionally uses the full ordinary graph family, in which an edge between two distinct prescribed blocks can independently be absent or present. This applies, for example, to simple undirected graphs and to directed graphs with the corresponding chosen directed edge. If a different hereditary graph class is supplied, Sections 1–6 still apply, but Section 7 requires that cross-edge hypothesis.

Let M be a finite commutative monoid with identity 1. Commutativity is used in the simultaneous-substitution associativity law. Finiteness is needed for local finiteness statements, not for the existence of the equipment.

Work with finite sets in a fixed universe, retaining actual sets and functions, not their isomorphism classes. This permits distinct tagged finite sets to represent distinct original interfaces. A horizontal span

    S:A ←[l] E [r]→ B

has an actual finite apex E and actual leg functions. Spans are not identified under apex bijection. Thus an apex automorphism remains genuine cell data.

A finite path p=(H_1,...,H_n), with interfaces A_0,...,A_n and spans S_i:A_(i−1)←E_i→A_i, has the boundary-marked compatible-tuple set

    P(p) = { (a_0,e_1,a_1,...,e_n,a_n) |
             l_i(e_i)=a_(i−1), r_i(e_i)=a_i for every i }.     (2)

Its endpoint maps are π_0 and π_n. For n=0, P(())=A_0, both endpoint maps are the identity, and the sole tuple coordinate is a_0. For n=1, the projection ρ_H:P(H)→E is a specified bijection with inverse e↦(l(e),e,r(e)).

Formula (2), rather than an arbitrarily parenthesized sequence of pullbacks, is used in every cell fibre. It is a finite limit model of the path of spans. Subpaths are extracted by retaining the relevant consecutive coordinates. Concatenating compatible subpath tuples identifies their common endpoint coordinate. If a subpath is empty, its tuple is the boundary coordinate itself. For three or more consecutive pieces, both possible concatenation procedures give exactly the same ordered tuple. This proves the associativity and unit coherence of every tuple regrouping used below. No assertion that nested ordered pairs are literally equal is required.

## 2 Objects horizontal arrows and cells

The objects and vertical arrows of V(N,M) are finite sets and functions, with ordinary strict function composition.

A horizontal arrow H:A⇒B is a pair (G,S), where G is an ordered graph of size at most N and S:A←E→B is a finite span. The graph is not a graph on the interface set or the span apex. These are independent data.

For a horizontal path p=(H_1,...,H_n) from A_0 to A_n, an output H=(G,S):B_0⇒B_1, and vertical boundaries

    f:A_0→B_0,       g:A_n→B_1,

a cell α:p⇒H with boundaries (f,g) is a triple (U,φ,m), as follows.

1. U=(U_1,...,U_n) is an ordered partition of the actual vertex set of G. Blocks may be empty. They are pairwise disjoint, their union is the full vertex set, and the graph of H_i equals G|U_i exactly.
2. φ:P(p)→E is a function satisfying

       l φ = f π_0,        r φ = g π_n.                     (3)

3. m∈M is one global cell value.

All data, including the ordered block list, function φ and scalar m, participate in equality. In particular, equal horizontal types at two positions do not identify those positions. An absent compatible tuple does not remove an occurrence or a block.

For n=0, the empty block list partitions G only when G=0. A nullary cell at a source object A therefore consists of a map φ:A→E over its specified vertical boundaries f:A→B_0 and g:A→B_1, and a value m. It need not have identity boundaries, and it need not target a unit span. This is exactly the allowed general nullary shape in a virtual double category. The original core's narrower identity-boundary nullaries will be recovered in Section 6.

Each fixed cell fibre is finite: there are finitely many partitions of a finite vertex set, finitely many functions between the relevant finite sets, and finitely many scalar values. There is nevertheless no bound on source arity, tree depth, number of empty slots, or number of vertical objects.

## 3 Composition and the virtual double category laws

Let α:(H_1,...,H_k)⇒H have boundaries f,g, graph blocks U_i, tuple map φ, and value m. For each i choose a cell β_i:q_i⇒H_i. Arrange these in a composable row: the source paths q_i run consecutively between finite sets C_(i−1),C_i, and their vertical sides are shared functions

    h_i:C_i→A_i                 (0≤i≤k).

An empty q_i requires C_(i−1)=C_i, but does not require h_(i−1)=h_i. Write β_i=(V_i,ψ_i,n_i). The expanded source q is the ordered concatenation q_1...q_k, with every original position retained.

Given z∈P(q), extract z_i∈P(q_i), and let c_i be its boundary coordinates. The equations for β_i imply that

    T_β(z) = (h_0(c_0), ψ_1(z_1), h_1(c_1), ...,
              ψ_k(z_k), h_k(c_k))                         (4)

belongs to P(H_1,...,H_k). In particular, the right leg of ψ_i(z_i) and the left leg of ψ_(i+1)(z_(i+1)) are both h_i(c_i). If q_i is empty, ψ_i is evaluated at c_i; its resulting apex witness is retained in (4).

Define α[β_1,...,β_k] to have

- graph blocks i_(U_i)(V_(i,j)), listed in lexicographic order (i,j);
- tuple map φ T_β;
- value m ∏_i n_i;
- boundaries f h_0 and g h_k.

The lifted blocks partition G. Equation (1) gives the required induced graph for every expanded input. Equation (3) follows from (4), so this is a well-typed cell. If k=0, the composable upper row consists of a vertical map h_0:C_0→A_0 and no cells. Set T_β=h_0:P(())=C_0→A_0, retain the empty graph partition, and retain the scalar m. This explicitly includes vertical precomposition of nullary cells.

The identity cell on H=(G,A←E→B) has boundaries id_A,id_B, single graph block [|G|], tuple map ρ_H:P(H)→E, and scalar 1.

**Identity laws.** Substituting identity cells at the source positions leaves every block unchanged. In (4), each ψ_i returns the original e_i and each h_i is an identity, so T_β is the identity function on the fixed source tuple set. The scalar remains m. Substituting an arbitrary cell into the identity cell on its output returns its apex function, blocks and scalar. These are literal equalities in the defined cell fibres.

**Associativity.** Consider three composable rows, with all shared vertical maps included. Both associations produce the same final source path. Each final graph block is an increasing lift along two nested subsets; equation (1) identifies the two lifts. On a final tuple z, both associations evaluate the innermost ψ maps on the same extracted subtuples, then the middle maps on the resulting compatible tuples, then φ. Their intermediate boundary coordinates agree because both use the same composite vertical functions. Empty subpaths contribute the same boundary coordinate and their own ψ value in either association. The case of an empty outer row reduces to associativity of vertical function composition. Thus the apex maps are equal pointwise on the one fixed set P(final source).

The scalar of either composite is the product of exactly the scalar of each vertex cell in the same finite substitution diagram. One bracketing groups the entire middle row before the lower rows, while the other groups by branches. Associativity and commutativity of M make these equal. This also covers nullary vertices, whose scalar factors are not deleted. Hence all virtual double category laws hold.

The verification is direct. It can also be viewed as the common-profile product of graph partitions, ordinary span multicells, and a global commutative scalar factor. Calling it a product does not replace the typing and nullary checks above.

## 4 Cartesian restrictions and coherent choices

Let H=(G,A←[l]E[r]→B), f:A'→A and g:B'→B. Define its chosen restriction R_(f,g)H:A'⇒B' to have the same graph G and span apex

    E_(f,g) = { (a',e,b') | f(a')=l(e), g(b')=r(e) },        (5)

with projections to a' and b'. The restriction cell

    χ_(f,g): R_(f,g)H ⇒ H

has vertical sides f,g, the single full graph block, the apex map selecting e from the unary tuple's apex (a',e,b'), and scalar 1.

**Theorem 4.1.** This cell is cartesian for every finite source arity, including zero.

**Proof.** Let p be any path from C_0 to C_n and let h:C_0→A', k:C_n→B'. A cell α:p⇒H with vertical sides f h,g k has data (U,φ,m). Define its lift to R_(f,g)H by the same ordered partition U, the same scalar m, and

    φ̄(z) = (h π_0(z), φ(z), k π_n(z)).                    (6)

The equations for α say exactly that (6) lies in (5). Its endpoints are hπ_0,kπ_n. Composition with χ gives α because it selects φ(z), retains the partition, and multiplies m by 1.

Conversely, any lift with boundaries h,k is forced to have first coordinate hπ_0 and third coordinate kπ_n. Factoring to α forces its middle coordinate to be φ. The singleton graph block of χ does not change the inner block list, so the partition must be U; its scalar is 1, so the lifted scalar must be m. The lift is unique in all three coordinates. For n=0, π_0=π_n=id_C, and precisely the same argument proves the nullary case. QED.

This proof also establishes naturality under precomposition by any typed row of multicells: the two candidate lifts have the same composite with χ, or directly the same three coordinates in (6). It does not require injectivity, surjectivity or invertibility of f or g.

The choices are coherent rather than declared split. The identity restriction has apex triples (a,e,b) with a=l(e), b=r(e); deleting a,b is a canonical endpoint-preserving bijection with E. For successive maps h:A''→A', k:B''→B', the canonical comparison

    R_(h,k) R_(f,g) H  ≅  R_(f h,g k) H                   (7)

deletes intermediate coordinates:

    (a'', (a',e,b'), b'') ↦ (a'',e,b'').

Its inverse inserts a'=h(a'') and b'=k(b''). Both graphs are G, and the comparison and inverse are unary cells of scalar 1. They commute with the restriction cells. For any number of successive restrictions, every composite comparison deletes exactly the same intermediate coordinates, and its inverse inserts their uniquely prescribed images. Therefore all associativity and identity coherence diagrams commute as actual function equalities. This is a specified coherent cleavage, not an unsupported assertion of strict pullback associativity.

**Change of choice.** If another horizontal H' and another cell χ':H'⇒H with the same boundary functions are cartesian, cartesianness of χ and χ' gives unique globular comparison cells in each direction commuting with them. Their composites are identities by uniqueness. The same uniqueness proves compatibility with further restrictions. This is a model-level comparison of cartesian choices; it is not the universal reconstruction theorem for all presentations.

## 5 Universal units in arbitrary contexts

For each finite set A define

    U_A = (0, A ←[id] A [id]→ A).

Choose the nullary cell η_A:()_A⇒U_A with identity vertical sides, empty graph partition, apex map id_A:P(())=A→A, and scalar 1.

**Theorem 5.1.** The cell η_A is opcartesian in the full contextual sense. Substitution of η_A gives a bijection between cells with an occurrence of U_A inserted at any specified interface A and cells with that occurrence removed. This holds for every prefix and suffix, every output, and arbitrary fixed outer vertical boundaries.

**Proof.** Fix composable prefix and suffix paths meeting at A. A cell from the path with U_A inserted has an empty graph block at that specific occurrence, because its induced graph has zero vertices. Deleting this block gives exactly a valid partition for the path without U_A. Conversely, insert one empty block at the specified index. These operations are mutually inverse even if other blocks are empty or adjacent types repeat.

For spans there is an endpoint-preserving bijection

    j:P(prefix,suffix) → P(prefix,U_A,suffix).              (8)

It inserts at the specified junction the U_A-apex element equal to the existing boundary coordinate a∈A, with the duplicated interface coordinate also equal to a. Its inverse deletes the added coordinates. The equations for the two identity legs force these coordinates, so there are no additional choices. This includes an empty prefix or suffix. If both are empty, (8) is a↦(a,a,a) from A to P(U_A).

Substitution of η_A on an expanded cell with apex map φ_+ and scalar m produces map φ_+ j and scalar m·1=m, and deletes the empty graph block. Given a cell without U_A with map φ and scalar m, its unique preimage has the inserted empty block, map φ j^(-1), and scalar m. All endpoint equations are preserved by (8). This proves bijectivity on the entire cell fibre, not merely on a selected class of operations. QED.

Removing several inserted units in any order deletes the same specified empty blocks and tuple coordinates and leaves the scalar unchanged. Thus the bijections commute. They also commute with all legal substitutions: at the tuple level they merely insert or erase the forced junction coordinates, and at the graph level they insert or erase empty blocks. This gives the usual coherent unit insertion/removal in all arities.

The chosen η_A is one nullary cell, not the declaration that the whole nullary fibre is a singleton. For example, the identity-boundary nullary fibre with output U_A contains one cell of each value m∈M. Choosing η_A at scalar 1 is what makes its substitution act bijectively without changing the scalar. More generally a scalar unit would yield a different universal nullary cell, with the corresponding scalar-adjusted factorization. A nonunit scalar need not yield a universal nullary cell.

Combining Sections 3–5 proves that V(N,M) is a virtual equipment: all restrictions and all universal units exist. This uses the conventional distinction between contextual opcartesianness and its weaker context-free form. The terminology agrees with Cruttwell–Shulman, Definitions 5.1, 7.1 and 7.6 in [A unified framework for generalized multicategories](https://arxiv.org/pdf/0907.2460v3). Their Example 2.7 supplies the standard span baseline; the graph and global-scalar coordinates have been checked here independently.

## 6 Full recovery of the original graph and arrow core

Let K be an arbitrary finite category. Define a finite-set-valued functor F by

    F(A) = { (A,C,t) | C∈Ob(K), t:C→A },
    F(f)(A,C,t) = (B,C,f t)       for f:A→B.               (9)

These sets are finite. The tag A makes F(A) and F(B) disjoint if A≠B. Each F(A) is nonempty because it contains (A,A,id_A), so distinct objects give distinct sets. The identity and composition laws follow directly from those of K. If f,g:A→B and F(f)=F(g), evaluation at (A,A,id_A) gives f=g. Hence F is faithful, although generally not full.

For a function u:X→Y write Γ(u) for the actual graph span

    X ←[id] X [u]→ Y.

Send a core component W=(G,f:A→B) to

    J(W)=(G, Γ(F(f))):F(A)⇒F(B).                           (10)

This is injective on the original component data. It keeps the actual whole graph G, not just its restricted graphs.

Fix an original output W=(G,f:A_0→A_n) and complete original input path

    p=((G_1,f_1:A_0→A_1),...,(G_n,f_n:A_(n−1)→A_n)).

Here n is an arbitrary arity, unrelated to the graph bound N. There is a canonical bijection

    τ_p:F(A_0) → P(J(p)),                                  (11)

which, starting at x, follows successively the functions F(f_i). Since each graph span has identity left leg, each apex coordinate is forced to be the preceding boundary coordinate, and every subsequent boundary is forced to be its F(f_i)-image. Its inverse is π_0. For n=0, (11) is the identity of F(A_0).

A globular ambient cell J(p)⇒J(W) has a span map φ:P(J(p))→F(A_0). The left endpoint equation forces

    φ = π_0.                                               (12)

The right endpoint equation says

    F(f) π_0 = F(f_n)...F(f_1) π_0.

Since π_0 is a bijection, this is equivalent to F(f)=F(f_n...f_1), and by faithfulness to f=f_n...f_1. If this equality holds, (12) is the unique possible span map; otherwise no span map exists.

Thus the ambient globular cell fibre is canonically and literally parametrized by

    { ordered partitions (U_1,...,U_n) of V(G)
      with G|U_i=G_i and f_n...f_1=f } × M.                (13)

This is precisely the independently defined original operation fibre D(W;p), including the retained output W and full typed input path.

**Nullary check.** A globular cell at an empty original path at A forces G=0. Its span map to Γ(F(f)) is id_(F(A)); the right endpoint equation forces F(f)=id_(F(A))=F(id_A), hence f=id_A. It then has exactly one free scalar m∈M. Thus there are exactly the original nullaries at (0,id_A), with no extra original-profile nullaries.

**Substitution check.** The map on original operations retains their ordered graph partition and scalar, and equips them with the unique span map (12). Graph substitution is the same increasing lift as in the original D. Ambient scalar substitution is the same product. The composite span map is the uniquely forced one for the expanded composite function path, so it agrees with the image of the substituted D operation. Identity and chosen nullary operations map to their stated counterparts. Hence (13) is an isomorphism of the original path-profile calculus onto the full identity-boundary subcalculus on the horizontally embedded original components.

The word full is confined to these operation fibres: the ambient equipment has many additional finite-set functions, horizontal spans, and nonglobular cells. The functor F is not asserted to be full as a functor of vertical categories. No quotient by apex isomorphisms, equal composites, or permutations has been used.

There is also an immediate refinement-category consequence, using Ref of the globular core of V(N,M), so every refinement entry has identity vertical boundaries. On any fixed original whole, every occurrence-indexed refinement tuple whose object and source/target profiles remain original consists of original-profile cells. By (13), these cells correspond bijectively, entry by entry, to the original D entries. The equation a[t_i]=b is preserved and reflected by substitution and injectivity on operation fibres. Composition is entrywise substitution, so J induces an isomorphism from Ref(D) to the full subcategory of Ref(Core(V(N,M))) whose objects have all components in the embedded original core. This conclusion retains each entry's entire child profile and local scalar, including empty runs.

If K is empty, the original comparison has no objects and is vacuous; V(N,M) itself is still defined. Nonvacuous mixed-interface coverage is obtained by any finite K containing the desired interface and arrow patterns. The proof works for every such K and every arity without a uniform finiteness bound on profiles.

### A concrete mixed interface instance

Take N=6, K the ordinal category 0→1→2, and any chosen finite commutative M. Then the tagged finite sets F(0),F(1),F(2) have respectively one, two and three elements. Write a:0→1 and b:1→2. On six vertices take the ordered blocks

    U_1={0}, U_2={1,2}, U_3={3,4}, U_4={5},

with input grades (a,id_1,id_1,b) and output grade ba. Let G^0 be edgeless and G^1 have just the edge joining vertices 0 and 5. These are two distinct retained whole graphs with exactly the same four restricted input components. The second and third input components are equal, including their graph and grade, but are distinct slots. Each whole admits the indicated four-input witness of every scalar m.

At slot 2 substitute the binary cut of its two vertices into ordered singletons with grades (id_1,id_1); at slot 3 substitute its unary identity. This produces a nested five-leaf witness. Swapping which original slot is refined gives a different occurrence-indexed refinement. Alternatively the four-input operation admits both binary regroupings determined by unions of its blocks, preserving all cross edges in the retained wholes. With M the two-element group, scalar pairs (1,1) and (e,e) at the two repeated middle slots give distinct parallel unary refinement tuples with the same total value. Thus the general comparison includes three genuinely distinct interfaces, nonidentity composable grades, repeated equal types receiving different refinements, nonreconstructive wholes, nontrivial arities and nonthin refinement fibres. This paragraph is a concrete mathematical instance, not an executable certificate or independent acceptance of the wider model-suite obligation.

## 7 Exact representability boundary for horizontal paths

In this section take the full ordinary graph family, so that a cross edge between two distinct blocks can be freely included or excluded without changing their induced graphs. Let p=(H_1,...,H_n) be a horizontal path. Let s(p) be the number of its nonempty graphs and let r be the sum of their vertex counts.

**Theorem 7.1.** The path p admits an opcartesian composite in V(N,M) if and only if s(p)≤1. If s(p)≥2, it does not even admit a weakly opcartesian cell.

**Positive proof.** Suppose s(p)≤1. Let G be the unique nonempty input graph, or 0 if all input graphs are empty. Set

    C_p=(G, A_0 ←[π_0] P(p) [π_n]→ A_n).

Choose κ_p:p⇒C_p with the only possible graph partition (the full vertex set in the unique nonempty position and empty blocks elsewhere), tuple map id_(P(p)), and scalar 1. If n=0, this is the unit construction, since P(())=A_0.

Fix arbitrary surrounding prefix and suffix paths and an arbitrary output H, including arbitrary outer vertical boundary maps. A cell from the path with p inserted has graph blocks for the p positions that are all empty except possibly one. Replacing those blocks by their union gives a unique block inducing G; conversely, that block is assigned to the one nonempty p position and empty blocks are inserted at every other position. If all input graphs are empty the union is empty. Thus the graph-factorization correspondence is bijective in every context.

On spans, replacing the p substring by C_p gives a canonical endpoint-preserving bijection of source tuple sets: compress the substring into its one apex element z∈P(p), or expand that element back into its stored coordinates. These are mutually inverse even for an empty substring. A map from the expanded tuple set to the output apex factors uniquely through this bijection. Scalars factor uniquely because κ_p has value 1. The resulting unique contextual factorization is exactly substitution of κ_p. This proves opcartesianness, not just context-free universality.

**Negative proof when r>N.** Any graph partition witnessing a cell with source p must have total cardinality r, so its output graph would have r vertices. No such horizontal output is permitted. Thus there is no candidate cell at all.

**Negative proof when r≤N and s(p)≥2.** On [r], put the vertices of the G_i in consecutive blocks. Define a graph G^0 with exactly the prescribed induced graph on each block and no cross-block edges. Choose a vertex in each of two nonempty blocks, and let G^1 differ from G^0 only by adding the edge between those vertices (or the selected directed edge). These are unequal whole graphs with the same ordered induced pieces.

Let T be the finite span A_0←A_0×A_n→A_n. For each ε∈{0,1}, the horizontal Q^ε=(G^ε,T) receives a globular cell α^ε:p⇒Q^ε. Use the consecutive graph partition, the endpoint map z↦(π_0(z),π_n(z)), and scalar 1. This formula is defined even when endpoint sets or the tuple set are empty.

Suppose κ:p⇒C were weakly opcartesian. Factoring α^0 and α^1 through κ would require globular unary cells C⇒Q^0 and C⇒Q^1. A unary graph partition is the single full vertex set, so such cells force, respectively, graph(C)=G^0 and graph(C)=G^1. This contradicts G^0≠G^1. No choice of span or scalar in C can repair this graph contradiction. QED.

Consequently V(N,M) is horizontally representable exactly when N=0. For N=0 every path has only empty graphs, and the usual tuple-span composites, equipped with scalar 1, supply all contextual composites coherently. Their associators are the tuple-flattening bijections from Section 1; their graphs and scalars are unchanged, so all coherence diagrams commute. If N≥1, two one-vertex graphs give a path with s=2. For N=1 it is excluded by the bound; for N≥2 it exhibits the genuine cross-edge obstruction. The latter already occurs over one-point interfaces and identity spans and works for every M, including M={1}.

**Corollary 7.2.** On a path with s(p)≤1, a cell α:p⇒H is opcartesian if and only if its tuple map P(p)→apex(H) is a bijection and its scalar is a unit of M. Its graph partition is automatically the forced one.

**Proof.** Compare α with κ_p. A unary globular cell C_p⇒H is an isomorphism exactly when its apex map is a bijection and its scalar is invertible: the inverse must invert the function and the scalar, and these inverses suffice. Composing κ_p with such an isomorphism preserves contextual universality. Conversely, if α is opcartesian, factor α through κ_p and κ_p through α. Uniqueness of the two universal factorizations makes the resulting unary comparison cells inverse. Therefore its function and scalar have the stated properties. QED.

In particular, an original graph cut that distributes nonempty vertices over two or more input slots is not an opcartesian assembly in this ambient equipment, even when its scalar is 1. Universal restrictions and universal units do not make all valid decomposition witnesses exact assemblies. Section 7 is a classification inside this named model, not a theorem about free ordinary-equipment completion.

## 8 Original cut fibres and the scalar obstruction

This section concerns the original core embedded in Section 6, not a classification of all ambient factorizations through arbitrary finite spans.

Fix a full original witness

    w=(G;(U_1,...,U_n);(f_1,...,f_n);m)

and a proper contiguous interval [i,j] of length at least two. Write U=U_i∪...∪U_j and h=f_j...f_i. A factorization of w through one intermediate original component at this interval forces that component to be

    K_w=(G|U,h).

Indeed, substitution makes its outer block the union U, hence its graph is G|U; its output grade is the ordered composite h of the full interval input path. Its outer blocks are the original outside blocks with U inserted, and its inner blocks are i_U^(-1)(U_i),...,i_U^(-1)(U_j). Equation (1) verifies these are exactly the required induced input graphs. The whole G, including all cross edges, remains the fixed outer output throughout.

Only the outer and inner scalars a,b remain free. Therefore the full core-restricted factorization fibre is canonically

    Fact_core,[i,j](w) ≅ { (a,b)∈M² | ab=m }.               (14)

Read the two scalars to obtain one direction, and attach them to the forced structural cuts to obtain the inverse. This is the direct coordinate proof of the source dossier's scalar-fibre boundary.

For m≠1, the two pairs (1,m) and (m,1) are distinct. Their factorizations remain distinct after embedding in V(N,M), since each involved original operation fibre embeds injectively. Thus any ambient factorization map admitting these same original factors is noninjective. This does not assert that (14) enumerates its entire ambient fibre: arbitrary intermediate spans can add further factors and isomorphisms.

For every nonempty K, arbitrary empty slots already supply proper-interval witnesses in all N. For N≥3, one may instead take three nonempty graph blocks with identity grades. The principal mixed-interface original family gives further examples without changing the argument. If M={1}, every nonempty core-restricted fibre (14) is a singleton. If M≠{1}, not all such fibres are singletons. This is the exact local scalar boundary, not F1, an all-degree 2-Segal theorem, or a claim about simplicial maps.

At an original unary fibre D(W;(W)), every m∈M is a valid witness, but only m=1 is its identity. At an original designated nullary component (0,id_A), every m is likewise a witness and η_A chooses m=1. Neither legitimate unary nor nullary witnesses have been discarded to force uniqueness. Requiring an arbitrary factorization to have scalar 1 is an additional marking or normalization restriction, not equality of the original full fibres.

An isomorphism-groupoid repair of span-witness ambiguity does not by itself remove every noninvertible scalar obstruction. For M={1,e} with e²=e, the only unit is 1, and the fibre over e in (14) contains (1,e), (e,1), and (e,e). An endpoint-preserving automorphism of an original function graph span is the identity on its apex, because its left leg is the identity. Hence the only invertible unary self-cell of the intermediate original component in this example is the identity: its scalar must be a monoid unit by Corollary 7.2 applied to a unary source. These three factorizations are not connected by an intermediate-isomorphism gauge transformation. Any zigzag through isomorphic intermediate spans would compose to such an automorphism and cannot change this conclusion. Restricting to invertible scalar markings is a legitimate additional hypothesis, but does not replace the full original M-labelled calculus.

## 9 A witness-sensitive base change calculation

The finite-span coordinate also exhibits the difference between having restrictions and preserving exact assemblies under internal interface changes. This calculation is independent of the graph obstruction and scalar factor.

Let S:A←E→B and T:B←F→C, and let f:A'→A, g:B'→B, h:C'→C. Consider the canonical comparison

    R_(f,g)S ×_(B') R_(g,h)T
          → R_(f,h)(S ×_B T).                              (15)

In tuple coordinates, its source consists of (a',e,b',t,c') with

    f(a')=l_S(e),
    r_S(e)=g(b')=l_T(t),
    h(c')=r_T(t).

Its target consists of (a',e,t,c') with the same endpoint conditions and r_S(e)=l_T(t). The map forgets b'. Its fibre over such a target tuple is exactly

    { b'∈B' | g(b')=r_S(e) }.                              (16)

Hence (15) is bijective precisely when every feasible middle interface value has exactly one lift along g; it is surjective precisely when every such value has at least one lift. This is proved by the displayed fibre description, including the vacuous case of an empty target.

Take one-point A,B,C; take E,F one-point; take B'={0,1}, with g the unique map; and take f,h identity maps. Then the source of (15) has two witnesses and the target has one. All relevant pullback restrictions still exist, but the canonical exact-composite comparison is not invertible. The relational existential interpretation forgets this multiplicity and sees a surjection. Scalar 1 throughout does not alter the failure.

To realize this calculation using actual opcartesian composites in V(N,M), take all the involved graphs empty, or put a nonempty graph in exactly one input position. Theorem 7.1 supplies the universal composites in either case, so the failure is not an artefact of asking for a composite that the graph coordinate forbids. This is a sharp local model calculation, not the global E5 transport or I4 interchange theorem.

## 10 Conditional use in a free envelope and remaining limits

Suppose, independently of this file, a presented virtual equipment E and a core map i:D→Core(E) have been constructed, and its genuine universal property supplies a virtual-equipment functor H:E→V(N,M) extending the core embedding J from Section 6. Then i reflects equality of original operations: if i(a)=i(b) for original parallel cells a,b, apply H to obtain J(a)=J(b), and use the fibre injectivity of J to conclude a=b. The same reasoning separates original retained wholes and original refinement tuples whenever the maps concerned retain their stated types.

If a syntax quotient Q is independently known to be isomorphic to D, the composite Q→D→Core(V(N,M)) can be used in exactly the same conditional argument. The ambient model does not itself prove that the free chosen equipment exists, that a chosen presentation admits the needed extension H, or that the core map i is full. An equation-reflecting embedding is weaker than proving that every new original-boundary cell in a free completion has an original representative.

The completed assertions here are the concrete cell construction, laws, cartesian restrictions, genuinely universal units, coherent restriction choices, full original-profile recovery, model-level representability classification, and the explicitly bounded factorization and base-change calculations. The following are not completed here: a universal chosen-equipment presentation, general 2-categorical reconstruction, full ordinary-equipment completion, local-to-global exactness, coherent independent cuts, a simplicial or double-Segal interchange structure, descent through presentation quotients, or a novelty claim.

## Source and proof provenance

The original D fibres and substitution conventions are taken from `sources/Semantics_Transport_Factorization.md`, Sections 1, 2 and 6. The ambient construction and all comparison maps are given explicitly above rather than obtained by redefining that core.

The conventional background is Cruttwell and Shulman, [A unified framework for generalized multicategories](https://arxiv.org/pdf/0907.2460v3), Example 2.7 for span multicells, Definition 5.1 for contextual opcartesianness and units, Definition 7.1 for cartesian restrictions, and Definition 7.6 for virtual equipments. These locations were checked in the primary source. No imported representability theorem is needed for the direct classification in Section 7. The regular representation in (9), the span pullback universal property, and global commutative-scalar enrichment are standard mechanisms; this proof claims their explicit compatibility with the retained-whole original core, not their invention.

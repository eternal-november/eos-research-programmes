# An extended local presentation of graph–span cells and their activated quotient

Author proof, 25 October 2026. Editorial delivery copy: current mathematical scope and review status are in [ScopeAndStatus.txt](../../../../foundations/witnessed-cut-coherence-proofs-and-sources/ScopeAndStatus.txt). Original and delivered hashes are recorded in SourceManifest.txt. Preliminary-target, companion-proof and status references have been normalized; mathematical proof content is unchanged.

## Plain-language abstract

The graph-dependent quotient needs spans and span maps that the original graph-and-arrow generators do not supply. We add those data explicitly. Despite this enlarged collection of types, only reusable local rules are needed: composition of finite functions, binary cuts, reassociation, genuine units, and scalar movement. Every resulting expression has exactly the information of one retained graph partition, one endpoint-compatible witness map, and one global scalar. This gives a local presentation of the concrete graph–span equipment, not an identification with the smaller original free completion. Adding the two span-doubling sections at active graphs then gives exactly the previously studied quotient. No graph partition or scalar is lost, and every original full operation profile is recovered unchanged. Universal preservation in a target is an explicit marking condition, not something falsely inferred from the equations alone.

## 1. Fixed data, notation, and theorem

Fix N>=0 and a finite commutative monoid M with identity 1. Use the ordered graphs, actual finite sets/functions, actual finite spans, boundary-marked tuple sets, and increasing induced-subgraph enumerations of [GraphSpanModel.md](GraphSpanModel.md), Sections 1–3. Work in a fixed small universe of these data. An actual span is

    S = (A <-l- E -r-> B).

The span category SqSpan has these spans as objects and arrows

    f=(a,e,b):S -> T,
    a:A->A', e:E->E', b:B->B',
    l_T e = a l_S,     r_T e = b r_S.

Composition and identities are coordinatewise actual function composition and identities. The notation u_f ALWAYS includes a and b, not just e. In particular, equal empty apex functions with different outside boundaries do not name the same typed generator.

For a path p=(S_1,...,S_n) from A_0 to A_n, write

    [p] = (A_0 <-pi_0- P(p) -pi_n-> A_n)

for its tuple span. For n=0, [()_A]=I_A=(A<-id-A-id->A). For n=1, the explicit span isomorphisms

    rho_S:[S]->S,       rho_S(a,e,b)=e,
    j_S:S->[S],         j_S(e)=(l(e),e,r(e))                 (1.1)

are inverse. No actual apex is identified with a tuple encoding of itself.

A matched row f_i=(a_(i-1),e_i,a_i):S_i->T_i induces

    [f_1,...,f_n]:[S_1,...,S_n]->[T_1,...,T_n],
    (x_0,s_1,x_1,...,s_n,x_n)
      |-> (a_0 x_0,e_1 s_1,a_1 x_1,...,e_n s_n,a_n x_n).   (1.2)

For n=0 this is I_a=(a,a,a):I_A->I_B. Formula (1.2) is a span map, not an asserted bijection. Its composition law follows coordinatewise.

**Theorem.** The extended local presentation below has, on every fixed full horizontal source/output profile and pair of outside vertical maps, exactly one cell for each triple

    (pi,phi,m),                                           (1.3)

where pi is the actual ordered induced-graph partition, phi:P(p)->E is the endpoint-compatible coefficient map, and m is in M. Its evaluation in V(N,M) is an isomorphism of virtual double categories and, with the displayed choices, of virtual equipments. The presentation has an interpretation-category universal property, including cell-natural transformations. Universal markings restrict that property to strong equipment functors.

For every induced-upward graph set I, adding the span-doubling section equations at active graphs presents precisely Q_I. Equality then retains pi and m and forgets phi exactly at active output graphs, with all type and boundary data fixed. The interpretation-category statement and universal markings descend to this quotient.

All arities, empty blocks, repeated equal occurrences, nonglobular boundaries and nullary whiskering are included. This is an infinitary SMALL presentation with finitely many forms of local rules, not a finite list of finite-set or multicell generators.

## 2. Generators and all local equations

The vertical category is the given category of actual finite sets/functions. Name a horizontal

    H(G,S):A=>B

for EVERY allowed ordered graph G and actual span S:A->B. These named horizontals are not quotiented or silently replaced by apex-isomorphism classes.

The generating cells are:

1. For f=(a,e,b):S->T in SqSpan and every G, a unary

       u_f^G:H(G,S)=>H(G,T),   boundaries (a,b).

2. For every H=H(G,S) and m in M, a globular unary d_m^H:H=>H.
3. For every ordered partition (U,V) of the actual vertex set of G and composable spans S:A->B,T:B->C, a globular binary

       c_(G;U,V;S,T):
       (H(G|U,S),H(G|V,T)) => H(G,[S,T]).                  (2.1)

   Its semantic partition is (U,V), coefficient is id_(P(S,T)), and scalar is 1. Either or both graph blocks may be empty.
4. A globular nullary

       c0_A:()_A=>H(0,I_A).                               (2.2)

Form fully typed virtual-double-category cell terms with identities and substitution. A substitution row retains its entire shared interface-map family; at outer arity zero it still retains the single vertical map h and gives nullary whiskering alpha<h>. Take the least parallel constructor congruence containing the VDC laws and the following schemes. All equations have their displayed matching sorts.

### 2.1 Span maps and scalars

For fixed G,

    u_id = id,             u_g u_f = u_(g f);              (S)
    d_1^H = id_H,          d_m^H d_n^H = d_(mn)^H;
    d_m^(H(G,T)) u_f = u_f d_m^(H(G,S));                   (D1)
    c[d_m,id] = d_m c,    c[id,d_m] = d_m c.              (D2)

The d on the right of (D2) is at the output of that c. There is no equation deleting a scalar at a nullary vertex.

### 2.2 Naturality, including nullary whiskering

For f=(a,e,b):S->S' and g=(b,t,c):T->T' with THE SAME middle map b,

    u_[f,g]^G c_(G;U,V;S,T)
      = c_(G;U,V;S',T')[u_f^(G|U),u_g^(G|V)].            (N2)

For every h:A->B,

    u_(I_h)^0 c0_A = c0_B<h>.                             (N0)

This last equation is necessary: nullary precomposition is not erased as an empty list. It will account for normal forms with nonidentity boundaries. Naturality is never used with unmatched interior maps and never assumes that (1.2) is a Beck–Chevalley isomorphism.

### 2.3 Typed ternary rotation

Let (U,V,W) partition the vertices of G, and let S:A->B,T:B->C,R:C->D. Set X=U union V and Y=V union W. The left inner cut has whole G|X and blocks i_X^(-1)(U),i_X^(-1)(V); the right inner cut has whole G|Y and blocks i_Y^(-1)(V),i_Y^(-1)(W). Write these two binary trees as L and R:

    L = c_(G;X,W;[S,T],R)[c_(G|X;...;S,T),id],
    R = c_(G;U,Y;S,[T,R])[id,c_(G|Y;...;T,R)].

Their targets have spans [[S,T],R] and [S,[T,R]], respectively. Define actual endpoint-preserving bijections

    ell:[[S,T],R] -> [S,T,R],
    r:[S,[T,R]] -> [S,T,R]                                (2.3)

by expanding the stored inner tuple and keeping each shared boundary coordinate once. The inverse groups the same coordinates into the indicated inner tuple. Impose

    u_ell^G L = u_r^G R.                                 (A)

The spans in (2.3) generally have unequal actual apex sets. Equation (A) is not literal equality of nested pullbacks.

### 2.4 Genuine left and right unit deletion

For S:A->B and graph G, let

    del_L:[I_A,S]->S,       del_R:[S,I_B]->S               (2.4)

select the S-apex. Their inverses insert the uniquely forced boundary and identity-span coordinates. Impose

    u_del_L^G c_(G;empty,V(G);I_A,S)[c0_A,id] = id_H(G,S),
    u_del_R^G c_(G;V(G),empty;S,I_B)[id,c0_B] = id_H(G,S). (U)

Only the particular diagonal span with its specified c0 is removed. An arbitrary H(0,T) is not deleted. Even a source occurrence H(0,I_A) is not removed by an equality of types: (U) describes substitution of the designated nullary into that particular occurrence.

The equations (S) use the ordinary finite-span-square composition tables. They do not list semantic multicells or their kernel pairs. The remaining schemes have at most ternary cut shape, regardless of final arity or tree depth. Denote this term quotient by P_(N,M).

## 3. Sound evaluation and the canonical flat terms

Every generator has the interpretation in V(N,M) stated above: u_(a,e,b) has coefficient e rho_S, d_m has coefficient rho_S and scalar m, and c0 has coefficient id_A and scalar 1. Category and scalar laws follow by actual function composition and multiplication in M. For (N2), both sides send a source tuple to (1.2); (N0) sends x to h(x) with boundaries h,h. For (A), both sides have the partition (U,V,W), coefficient the identity on the one fixed flat tuple set after expansion, and scalar 1. Equations (U) delete exactly the forced identity-span coordinates. Thus evaluation

    Ev:P_(N,M)->V(N,M)                                   (3.1)

is a well-defined VDC functor, identical on the vertical category and named horizontals.

Fix an actual ordered partition pi=(U_1,...,U_n) of G inducing the input graphs, and a span path p=(S_1,...,S_n). We now specify a term

    c_flat(pi;p): (H(G|U_1,S_1),...,H(G|U_n,S_n))
                      => H(G,[p])                       (3.2)

with identity outer boundaries, coefficient id_(P(p)), scalar 1.

* For n=0, G=0 and c_flat=c0_(A_0).
* For n=1, U_1=V(G) and c_flat=u_(j_S)^G. This is NOT the identity cell unless the actual tuple encoding agrees with the given apex; its coefficient is j_S rho_S=id_(P(S)).
* For n>=2, choose the right-comb binary graph-cut tree on the n input occurrences. Each node graph is the induced graph of G on the union of its descendant blocks; relative child partitions use increasing inverse images. At its root the span is the corresponding nested tuple span S_t. Postcompose the binary-tree term with the actual span isomorphism

       flat_t:S_t->[p]

  that recursively expands every stored tuple and retains each junction coordinate once. For n=2 this is the given binary c itself, with flat_t the identity. For arbitrary n the expansion and its inverse are explicit finite functions.

The graph identities for successive induced restrictions ensure that every node is typed. Coordinate expansion proves the asserted coefficient of (3.2).

### Lemma 3.1 — All cut trees have the same normalized flattening

Take any finite planar binary cut tree whose leaves are the specified n input occurrences, allowing nullary c0 vertices at specified interface positions and allowing the canonical unary tuple isomorphisms needed to compare actual encodings. After postcomposition with its actual flattening map, the term equals c_flat(pi;p), where pi is its lifted leaf partition. This statement retains every genuine source occurrence, including an empty-graph one; it removes only inserted nullary vertices.

**Proof.** First remove intermediate unary tuple isomorphisms by (S) and (N2): at a binary vertex use the entire matched pair of incoming span maps, including the shared middle map. This moves the maps to its output as the actual induced tuple map. The case of a nullary input uses (N0). For the canonical encoding maps at issue the interface maps are identities, but this argument also explains why no unmatched one-sided naturality is assumed.

If a binary vertex has one nullary c0 child, (U), followed if necessary by (S) with the inverse of del_L or del_R, removes that vertex and child while retaining the other subtree. The graph block of the removed child is empty, and the other graph is the whole at that vertex. Its span correction is exactly coordinate deletion. Repeating removes all nullary leaves unless the entire tree has no genuine source leaf; in that case it reduces to one c0. In particular, the binary tree with two c0 children reduces to c0 by composing either equation (U) with the remaining c0. No empty-graph input leaf is eligible for this reduction merely because its graph is empty.

If there are at least two genuine leaves, every remaining full binary tree can be changed to the chosen right comb by finitely many rotations. One elementary proof is recursive: apply the rotation ((x,y),z)->(x,(y,z)) at the root until its left subtree is a leaf, then repeat inside the right subtree. Each step decreases the number of leaves in the current left subtree. Equation (A) identifies the two normalized cut terms at every such rotation. The relative graph blocks agree because i_(i_U(V))=i_U i_V and (G|U)|V=G|i_U(V).

For the coefficient corrections, expansion before a rotation and expansion after it return the SAME ordered list of final coordinates. This is a pointwise equality of two functions with the same final flat target, so (S) identifies the accumulated unary correction maps. Deleting two genuine-unit insertions in different orders likewise deletes the same prescribed coordinates. Thus after finitely many steps the term is the chosen normalized right comb. For one remaining leaf, flattening is j_S, giving the specified arity-one term. For no remaining leaves it is c0. This proves the lemma without a global confluence or terminating raw-term rewrite claim. ∎

A useful special case is grafting flat cuts. For consecutive paths q_1,...,q_k, let Q_i=[q_i] and q=q_1...q_k. There is a canonical bijection

    comp_q:[q] -> [Q_1,...,Q_k]                            (3.3)

that compresses each subpath into its stored tuple, including I_C for an empty subpath at C. Given a parent partition pi and compatible child partitions pi_i, Lemma 3.1 says exactly

    c_flat(pi;Q_1,...,Q_k)[c_flat(pi_i;q_i)]
      = u_(comp_q)^G c_flat(pi[pi_i];q).                  (3.4)

For k=1 this includes the explicit one-factor j maps. For k=0 there are no child cells; the possible nonidentity source-object map is treated by (N0), not suppressed in (3.4).

## 4. Normal form and completeness in every boundary sort

Fix a source horizontal path p from A_0 to A_n, a target H(G,S) with apex E and endpoints B_0,B_1, and outside maps f:A_0->B_0,g:A_n->B_1. For a triple (pi,phi,m) in that fixed sort, the endpoint equations are

    l_S phi=f pi_0,        r_S phi=g pi_n.

Thus (f,phi,g):[p]->S is an actual arrow of SqSpan. Define

    NF(pi,phi,m;f,g)
      = u_(f,phi,g)^G d_m^(H(G,[p])) c_flat(pi;p).         (4.1)

Evaluation gives exactly (pi,phi,m), since c_flat has coefficient id on the fixed P(p). The notation always fixes the full type and both boundaries before referring to the triple.

### Lemma 4.1 — Every term is equal to its normal form

**Proof.** The VDC associativity and identity laws flatten a substituted term to a finite generator-rooted substitution tree, retaining all shared interface maps and every nullary whiskering map. This reduction follows directly by induction on the construction of terms: replace the outer term by its tree and graft the trees of the substituted terms at its ordered leaves. When a leaf run is empty, its specified interface and whiskering map remain part of the tree. We normalize these trees by induction from the root's children. A bare identity leaf on H(G,S) has normal form u_(rho_S) d_1 u_(j_S)=id by (S), (D1), and (1.1); this supplies the zero-vertex base case.

At a unary generator u_a, use the induction hypothesis for its child, commute scalars by (D1) if needed, and compose the full span squares by (S). At d_m, use (D1) to move it past the child's u and use (D1)'s monoid equation to multiply the two scalars. Identity roots disappear by the VDC identity laws.

Consider a binary root c_(G;U,V;S,T). Its children have consecutive source paths q_1,q_2, partitions pi_1,pi_2, coefficient squares

    f_i=(h_(i-1),phi_i,h_i):[q_i]->S_i,

and scalars m_i. The shared middle h_1 is identical for the two children by the original substitution typing. Move the child scalars past their u's by (D1); apply (N2) to the MATCHED pair f_1,f_2; then move both scalars through the new binary cut by (D2). The result has outer unary coefficient [f_1,f_2], scalar m_1 m_2, and underlying cut term

    c_(G;U,V;[q_1],[q_2])
                   [c_flat(pi_1;q_1),c_flat(pi_2;q_2)].

Lemma 3.1 or (3.4) converts this to u_(comp_q)c_flat(pi;q_1 q_2), where pi is the increasing lifted partition. Composition (S) and scalar centrality now give (4.1), whose coefficient is [f_1,f_2] comp_q. This is exactly the pointwise tuple-substitution formula of GraphSpanModel. Empty q_i are covered because [q_i]=I_C and the lemma uses the genuine c0 unit equations, while f_i may still have unequal left and right boundary maps. Crucially, the child's FULL square (h_(i-1),phi_i,h_i) and its scalar have already been moved outward by matched-boundary naturality and scalar centrality BEFORE this unit deletion. The deleted term is only c0_C at its actual source interface; the original nullary coefficient witness, differing boundaries and scalar all remain in the outer normal form.

At a nullary root c0_A vertically precomposed by h:C->A, (N0) gives u_(I_h)c0_C, already (4.1). This also covers later unary postcomposition, which can give a nullary cell with arbitrary differing outside boundaries. Nullary scalar vertices retain their scalar by the unary cases above. These are all generator-root cases. ∎

### Theorem 4.2 — Exact presentation, not merely soundness

Evaluation (3.1) is bijective on each fixed full profile and boundary pair.

**Proof.** Every semantic cell has a triple and hence the preimage (4.1), proving surjectivity. If two terms have equal semantic cells, their partitions, actual coefficient functions and global scalars agree within the SAME fixed sort. Lemma 4.1 identifies each with the SAME specified term (4.1); hence they are equal in P. Conversely all syntactic equations were proved sound. Thus equality is exactly equality of the three coordinates. Because evaluation already preserves identities, vertical boundaries and substitution, these fibre bijections give a VDC isomorphism. ∎

In particular, the presentation neither identifies equal-typed occurrences nor loses a graph block when a tuple set is empty. Empty-domain maps may be unique in a fixed sort, but different vertical boundaries remain different sorts. The scalar coordinate is one global element of M, including at nullary operations. Associativity of simultaneous substitution uses the original commutativity of M; no reduction to M={1} was made.

## 5. Derived restrictions and actual contextual units

For S=(A<-E->B), f:A'->A,g:B'->B, form the named pullback span

    R_(f,g)S:
    A' <- {(a',e,b'):f(a')=l(e),g(b')=r(e)} -> B'.

The actual square (f,pr_E,g):R_(f,g)S->S gives the term

    kappa_(G,S;f,g)=u_(f,pr_E,g)^G:
          H(G,R_(f,g)S) => H(G,S).                        (5.1)

Its direction is FROM the pullback horizontal TO the original horizontal.

Given a cell into H(G,S) with boundaries fh,gk, normalize it as (pi,phi,m). The unique lifted term with boundaries h,k is the normal form with the SAME pi,m and coefficient

    phi_bar(z)=(h pi_0(z),phi(z),k pi_n(z)).               (5.2)

The equations for phi put (5.2) in the pullback apex. Postcomposition with (5.1) returns phi. Conversely, the fixed boundaries force the first/third coordinates of any lift, and factoring to phi forces its middle coordinate. The normal-form bijection therefore proves existence and uniqueness of the lift in P at every arity, including zero. Thus (5.1) is cartesian. Its naturality under all substitutions follows either by these coordinates or by uniqueness.

The chosen unit is H(0,I_A) with c0_A. Fix arbitrary prefix and suffix meeting at A, output and outside boundaries. Let p be the path with that occurrence absent and p+ the path with H(0,I_A) inserted at the specified position. There is an actual bijection

    ins:P(p)->P(p+)                                      (5.3)

inserting the uniquely forced diagonal-span apex and repeated A-coordinate. Given (pi,phi,m) on p, its unique inverse under c0 substitution has the empty block inserted at that position, coefficient phi ins^(-1), and scalar m. Substitution deletes the block and composes with ins. Both operations are inverse in the normal forms, and hence in the term quotient. This proves full CONTEXTUAL opcartesianness, even with empty prefix/suffix and nonidentity outside boundaries. It is not just a relation on a selected binary cut.

The specified restriction comparisons delete intermediate pullback coordinates, and unit comparisons insert/delete forced tuple coordinates. Their composites agree pointwise, so the category tables (S) prove their coherence in P. Consequently Theorem 4.2 is an isomorphism with the concrete chosen virtual equipment of GraphSpanModel, not just a comparison of cell sets.

This does NOT make a binary cut (2.1) opcartesian in general. With two nonempty input graphs, possible cross edges in the retained whole give the obstruction proved in GraphSpanModel, Section 7. The proof of the presentation used no inverse or universal property for such a cut.

## 6. Universal interpretation categories and their precise markings

Let E be any virtual double category. An extended signature interpretation consists of a vertical functor v from our finite-set category to E, a horizontal image of EVERY H(G,S), and images of EVERY u_f,d_m,c,c0 with the specified boundaries, satisfying (S),(D1),(D2),(N2),(N0),(A),(U). It does not assign independent images to arbitrary semantic multicells. Each displayed actual function or tuple comparison indexes a named u generator or composition table, not an additional target-side finite-limit requirement.

Term evaluation extends this data uniquely to a VDC functor P->E. Existence follows by induction on cell terms and soundness of the imposed equations in E; uniqueness follows by the same induction. Restriction of a functor recovers the generator interpretation, and extension/restriction are inverse on functors.

For completeness at the transformation level, a morphism between interpretations F and G consists of a natural transformation tau between their vertical functors, and for EVERY named H:A=>B a unary cell

    tau_H:FH=>GH,    boundaries (tau_A,tau_B),

natural for u_f,d_m,c,c0. For a general cell alpha:p=>H with possibly nonidentity outside boundaries the desired equation is

    tau_H F(alpha)=G(alpha)[tau_(H_1),...,tau_(H_n)].       (6.1)

The sides of (6.1) match by vertical naturality. When n=0 the right side means G(alpha) vertically precomposed by tau at the specified source object; it does NOT mean forgetting that component.

Naturality holds for generators by assumption and for identities by the identity laws. If it holds for an outer term and its substituted row, VDC associativity identifies their two expanded composites, giving (6.1) for the substitution. In the empty-row case vertical naturality of tau identifies the retained common interface-map composites. Thus induction proves naturality for every term. No new horizontal component is to be chosen: ALL H(G,S) are explicitly named generator types. Conversely a cell-natural transformation of VDC functors supplies precisely these components and generator naturality. Identity and composition of transformations have the same vertical and named-horizontal components, so restriction and extension are inverse functors between the interpretation categories. This is an ISOMORPHISM OF CATEGORIES, not only a bijection on their objects.

Now suppose E is a virtual equipment. Define a **universally marked interpretation** by the additional requirements that:

* every image of the derived generator (5.1) is cartesian in E for ALL target source arities and boundary factorizations;
* every image of c0_A is contextually opcartesian in E for ALL surrounding paths.

These are genuine target universal properties, not merely equations on the interpreted subcalculus. By definition and Section 5, the preceding category isomorphism restricts to the category of VDC functors P->E preserving these designated universal cells and its full category of cell-natural transformations. It is equivalently the strong equipment-functor category with this preservation convention. Any other cartesian cell in P differs from the chosen cell with its target/boundaries by the unique invertible comparison; a functor preserves that comparison and hence also preserves the other cell. The analogous uniqueness comparison applies to universal units. Thus preserving the designated family is sufficient for preserving the universal structures, without imposing literal equality to E's choices.

If strict preservation of chosen restrictions and units is wanted, add literal choice compatibility on the named horizontal images and the displayed universal cells to the interpretation data. The same category isomorphism restricts to that subcategory. We make no claim that an arbitrary raw signature interpretation can be strictified while fixing all its already named horizontal images: the named types are additional data, unlike freely generated fresh restriction expressions.

For the activated quotient below, the same argument uses the additional section equations. Generator naturality still extends by the same induction; universally marked interpretations again correspond exactly to strong equipment functors from that quotient.

**Important boundary.** Bare local equations do not force the images of kappa or c0 to remain universal among arbitrary EXTRA cells in E. The relative equipment statement is therefore the universal property of an explicitly universally marked local sketch. This is not silently promoted to the unmarked free chosen-equipment construction of `Conservative_Equipment_Envelope.md`.

## 7. The local section quotient is exactly Q_I

Let I be induced-upward:

    G|U in I  implies  G in I.                            (7.1)

For a span S with apex E, let S[2] have apex E times {0,1} and endpoint legs ignoring the second coordinate. The two actual squares s_i:S->S[2] have identity boundary maps and apex e|->(e,i). Add, for every active G and every span S, the unary equation

    u_(s_0)^G=u_(s_1)^G.                                 (7.2)

Let P_I be the resulting parallel term congruence quotient.

### Theorem 7.1 — Exact quotient normal forms

Within each fixed full profile and outside-boundary sort, two terms in P_I are equal exactly when their P normal-form data satisfy

    pi=pi', m=m', and [G in I or phi=phi'].                (7.3)

Hence P_I is isomorphic to Q_I as a virtual equipment with the same displayed restrictions and units.

**Proof.** The relation (7.3) on V-cells is a substitution congruence: changing an outer coefficient is harmless only at its active output; changing a child's coefficient is harmless because that child's active graph is induced in the retained outer whole, which is active by (7.1). The graph partitions and all scalar products remain the same. Nullaries and empty blocks are included in this induced-subgraph statement. Thus the evaluation into Q_I is sound for the local presentation and (7.2), so no equality outside (7.3) can be generated.

For the converse, only the active-output case is new. Suppose two normal forms have the same pi,m and fixed boundaries f,g, but coefficient maps phi,psi:[p]->S. Define the actual span square

    t:[p][2]->S,
    t(z,0)=phi(z),       t(z,1)=psi(z),
    boundaries (f,g).                                    (7.4)

The endpoint conditions for phi and psi verify (7.4), including empty P(p). Apply (7.2) at H(G,[p]), precompose with d_m c_flat(pi;p), and postcompose with u_t. The tables (S) identify u_t u_s0 with u_(f,phi,g) and u_t u_s1 with u_(f,psi,g). The resulting equation is exactly equality of the two normal forms. Hence (7.3) is also sufficient.

The inherited restriction bijection (5.2) fixes graph, partition and scalar. At inactive G it is the original coefficient bijection; at active G both corresponding nonempty coefficient fibres are collapsed to singletons. It and its inverse therefore descend. The contextual unit bijection has the same property, using the specified insertion/deletion of one empty partition block and the tuple bijection (5.3). Their quotient bijections prove the equipment axioms, not just their equational shadows. ∎

For graph-only all-or-nothing relations (7.3), condition (7.1) is necessary as well. If H=G|U is active and G is inactive, use singleton interfaces, an H-child with a two-element output apex, and its two distinct singleton selectors. They are identified at H. A binary G-cut with complementary graph block and coefficient reading that selected bit yields distinct singleton-to-two-element maps at inactive G. This violates substitution stability of (7.3). This is the exact necessity argument of the quotient source theorem, now expressible using our local generators and their normal forms.

A least congruence generated by (7.2) always exists even for a non-upward I, but we do NOT identify it with simple activation of the upward closure: graph cuts need not be invertible, and further composite-cell equalities do not automatically give all larger-whole unary equalities.

The quotient has a finite equality test on each supplied pair of finite terms after normalization: compare the full sorts, partitions and scalars; if the common output is inactive compare the actual finite coefficient functions. This statement is not a claim of a canonical natural coefficient representative at active graphs, or of a convergent raw-tree rewrite system.

## 8. Original-profile comparison and the limits of the bridge

For any finite category K use the tagged faithful finite-set realization F of GraphSpanModel, Section 6. Send the original graph-and-arrow horizontal (G,h:A->B) to

    H(G,Gamma(Fh)),

and an original cut of scalar m and partition pi to (4.1) with its unique coefficient map. On a path of function graph spans, pi_0:P(p)->F(A_0) is a bijection and the output graph span's identity left leg forces phi=pi_0. The right leg then forces Fh=F(h_n...h_1), equivalently h=h_n...h_1 by faithfulness. For n=0 the same argument forces h=id and G=0. Thus every full original globular cell fibre in P is EXACTLY the original partition-and-global-scalar fibre. Since there is at most one coefficient per fixed original profile, (7.3) adds no original equality and creates no cell in an empty fibre. The same full recovery holds in P_I, uniformly in N,K,M.

The occurrence-wise refinement comparison also follows: an arrow tuple all of whose entries have original full profiles consists exactly of original cells. Entrywise equality and substitution are preserved and reflected by the just-proved fibre bijections. No refinement tuple is replaced by equality of its flattened endpoints.

The original empty-graph identity component maps here to

    H(0,Gamma(F id_A))=H(0,I_(F A)),

and its scalar-one nullary maps to c0_(F A). This is a genuinely universal unit in this PARTICULAR extended presentation. It is extra structure/marking relative to the old unnormalized free-envelope problem, where an original empty-graph component and a fresh universal-unit expression are not literally the same horizontal. Nothing here identifies those two types in that older syntax.

The inclusion of the old local presentation into this extended one is consequently conservative and full on the stated original semantic profiles. It does NOT say the additional H(G,S), the doubled spans S[2], or all u_f are generated by the old C5 components using restrictions and units. They are expressly additional generators. Nor does this theorem say that the C5-only free envelope is isomorphic to V or Q_I, or classify its new cells on original profiles. Its conservative interpretation into the present model can still be obtained by the already proved envelope universal property, with its own separate choice conventions.

## 9. Scope and dependency record

**Established here.** An explicit small extended local multicell presentation; complete normal forms for all finite arities and all boundary maps; derived all-arity cartesian restrictions and contextual units; interpretation-category isomorphisms including transformations, with universal preservation separately marked; the exact local section presentation of Q_I for induced-upward I; and full original-profile/refinement recovery. The proof uses finitely many kinds of equations, not an enumeration of semantic multicells and their kernel equalities.

**Inherited inputs.** The tuple substitution and ordered-graph conventions of `GraphSpanModel.md`; the original C5-to-graph-and-arrow comparison in the supplied source dossier; and the already proved concrete quotient criterion in `GraphDependent_Quotient_and_Cut_Memory.md` (reproved above where needed for presentation completeness). The finite-span composition tables and tuple-coordinate calculations are ordinary category-theoretic infrastructure, not a novelty claim. No new external literature theorem is needed for the explicit term/normal-form proof.

**Not claimed.** Equality with the C5-only free virtual/ordinary envelope; target universality from bare local equations; a finite total generating set for finite spans; strict equality of differently parenthesized tuple sets; opcartesianness of arbitrary graph cuts; erasure of arbitrary empty-graph spans; an all-scalar discrete unique-cut theorem; or a new global simplicial assertion. The certified global cut results may now use THIS explicit extended presentation and its quotient; any statement about the smaller old free envelope still needs its own comparison.

Author proof complete. Independent review status is recorded in ScopeAndStatus.txt.

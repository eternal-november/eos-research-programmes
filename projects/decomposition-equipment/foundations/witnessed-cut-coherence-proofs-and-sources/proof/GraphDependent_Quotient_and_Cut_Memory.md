# Graph-dependent coefficient quotients and the exact memory required by cuts

Author theorem and proof, 25 October 2026.

## Abstract

A quotient can forget span-witness information selectively, according to the graph being assembled, without identifying the original graph cuts. The exact condition is simple: whenever forgetting is allowed on an induced subgraph, it must also be allowed on its retained whole. This quotient still has unique cartesian restriction lifts and preserves the original graph-and-arrow calculus. It does not, however, preserve the information specifying an exact intermediate span. We calculate precisely the symmetries introduced at every cut tree, identify when no repair is needed, and prove that retaining actual intermediate bijections gives a coherent repair. A factorial lower bound measures the required additional choices within an explicitly stated equivariant marking model—not within arbitrary computational representations.

## 1. Scope, inputs, and notation

Fix a nonnegative integer N and a finite commutative monoid M. Let V=V(N,M) be the concrete virtual equipment of [GraphSpanModel.md](../GraphSpanModel.md), Sections 1–6. The principal example below applies for N≥2; hence it applies to the dossier's N≥6 family. All finite interfaces and finite spans are allowed. Arity, empty occurrences, tree depth, and refinement length are unbounded.

A horizontal is (G,S), where G is an actual ordered graph on [r], r≤N, and S is an actual finite span. A cell with fixed full horizontal profile and fixed outer vertical boundaries is

    (pi, phi, m),

where pi is its actual ordered graph partition, phi is its endpoint-compatible map from the boundary-marked source tuple set to the output span apex, and m∈M. All occurrences, including equal or empty ones, remain distinguished. Graph restriction uses the increasing enumerations i_U and the identities

    (G|U)|W = G|i_U(W),     i_(i_U(W)) = i_U i_W.             (1)

We use the explicitly verified tuple-substitution functions, cartesian restriction bijections, and contextual unit bijections of that model. No horizontal representability of V is assumed.

The ordered graph collection of size at most N is finite. Let I be any subset of it; call G active if G∈I. For a span S:A←E→B write

    E(a,b) = {e∈E : l(e)=a, r(e)=b},
    supp(S) = {(a,b) : E(a,b) is nonempty},
    Aut_boundary(S) = product_(a,b) Sym(E(a,b)).              (2)

“Endpoint-thin” means that every E(a,b) has at most one element.

The cut doctrine used here retains PREQUOTIENT actual span-isomorphisms as distinct morphisms. At an active graph, Q_I itself identifies all parallel scalar-1 unary coefficient maps: its intrinsic scalar-1 automorphism groups are trivial, and it has additional isomorphisms between spans of equal endpoint support. Using those intrinsic quotient isomorphisms would be a different cut doctrine, with different retained information. The obstruction and memory theorem below do not assert that Q_I admits no coherent cut construction.

The theorem is about an explicit quotient of the concrete all-finite-span virtual equipment. It is not a construction of a new initial syntax, a proof of a free-envelope comparison for these additional equations, or a global simplicial 2-Segal theorem. Section 10 records these limits precisely.

## 2. The quotient and its finite generator criterion

Define a relation ≡_I on parallel V-cells by retaining the partition and scalar and, precisely at active output graphs, forgetting the coefficient map:

    (pi,phi,m) ≡_I (pi',psi,m')
      iff pi=pi', m=m', and [G∈I or phi=psi].                (3)

Objects, horizontal spans, vertical maps, complete profiles, and outer boundaries are never identified by this relation.

For a finite span S:A←E→B let S[2] have apex E×{0,1}, with both endpoint legs ignoring the second coordinate. At each active G impose the following parallel unary equation, with scalar 1:

    s_0 = s_1 : (G,S) -> (G,S[2]),     s_i(e)=(e,i).         (4)

For fixed N these are finitely many graph-side templates and one span-variable template. They do not enumerate semantic equalities of arbitrary cells.

### Theorem 2.1 — Exact criterion and generation

The relation (3) is a substitution congruence if and only if

    G|U∈I  implies  G∈I                                   (5)

for every G and every actual subset U of its vertex set. When (5) holds, (4) generates exactly (3). The relation also respects the chosen cartesian restriction-factorization bijections and contextual unit-factorization bijections.

#### Proof: sufficiency of (5)

Suppose an equivalent outer cell is substituted into a fixed row of cells. Its graph partition and scalar are unchanged. If the outer coefficient could change, its output G is active; the resulting two composite coefficient maps are therefore equivalent by (3).

Now change one child cell to an equivalent child. If its coefficient changes, its output graph is active. In every legitimate graph substitution that child graph is the induced graph of the retained outer whole on its assigned block. Condition (5) makes the whole active, so the resulting coefficient maps are again equivalent. Changes of multiple children follow one occurrence at a time. The partition and scalar laws preserve their exact retained data. The argument includes nullary substitutions, repeated equal occurrences, and empty blocks. Thus (3) is a parallel substitution congruence.

#### Proof: necessity of (5)

Suppose H=G|U is active but G is inactive. Work over singleton interfaces. Give the H-child a two-point output apex {0,1}, and take two parallel unary child cells from a singleton apex, with maps selecting 0 and 1. These child cells are equivalent by (3). Give the complementary graph G|U^c a singleton apex. There is an outer binary graph cut of G with blocks (U,U^c), output apex {0,1}, and coefficient map reading the H-child's bit. Substituting the two equivalent children yields two parallel G-cells with the same partition and scalar but distinct singleton-to-{0,1} maps. Since G is inactive, these cells are not equivalent by (3). Thus (3) is not a substitution congruence. This construction also works when either graph block is empty.

#### Proof: the generators give exactly (3)

Assume (5). Every equation (4) holds in (3); soundness under substitution follows from the established congruence property.

Conversely, take two cells (pi,phi,m) and (pi,psi,m) with active output graph G. Let P be their common source tuple set, with its source endpoint span. There is a legitimate cell from the given source path to (G,P), with graph partition pi, coefficient id_P, and scalar m. This is merely a valid graph cut; it is not asserted to be a universal graph assembly.

Substitute this cell into (4) for the span with apex P. Then postcompose the unary cell with coefficient

    c:P×{0,1}->E,     c(z,0)=phi(z), c(z,1)=psi(z).

Its outer boundaries are the boundaries of the two original cells, so it is well typed. The resulting equation is exactly (pi,phi,m)=(pi,psi,m). Thus every pair in (3) follows from (4), and no pair outside (3) does.

#### Proof: compatibility with the universal bijections

A chosen cartesian restriction-factorization bijection preserves the output graph, graph partition, and scalar. On coefficient maps it is the usual bijection between maps into the pullback span and maps into the unrestricted span with the prescribed boundary equations. If G is inactive, no equality is added on either side. If G is active, every nonempty coefficient fibre on each side is collapsed to a singleton; the bijection preserves its nonemptiness. Hence the bijection and its inverse preserve (3).

The contextual unit-factorization bijection similarly preserves the retained output graph and scalar and gives the prescribed bijection of graph partitions and tuple maps. The same inactive/active argument applies. This proves the final assertion. ∎

### Consequences and limits of the finite test

Condition (5) is a finite incidence test on ordered induced graphs. The principal nonproduct example is

    I = {G : G contains an edge}.                           (6)

An edge crossing two source blocks can activate the retained whole although both source graphs are inactive. Conversely, two unary coefficient maps on an edgeless graph remain distinct, while the corresponding maps on an edge-containing graph become equal. Therefore this is not a graph-independent quotient of the span factor.

Within the stipulated graph-only, all-or-nothing family (3), the least enlargement of an initial active list making it a congruence is its induced-upward closure. This statement does NOT identify the unrestricted generated congruence from a non-upward list of equations (4): such a congruence can identify larger-whole multicells without identifying all larger-whole unary cells. No inverse to a nonuniversal graph assembly is used here.

Equality in the accepted concrete quotient is decidable by reading the partition and scalar, testing activity, and, when inactive, comparing finite maps. If a representative is desired, order each output apex and choose the least compatible output witness in each required endpoint fibre at active graphs. This normal representative is enumeration-dependent, not natural under span relabeling. No claim of a convergent raw-tree rewrite presentation follows from this observation.

## 3. Universal restrictions, units, and the original calculus

### Theorem 3.1 — Virtual equipment and original-profile conservation

If (5) holds, the quotient Q_I=V/≡_I is a virtual equipment with the same chosen restrictions and contextual units as V. For every finite category K and the faithful finite-set realization F used in GraphSpanModel, the original graph-and-arrow calculus embeds into Q_I bijectively on every original globular full operation profile. The embedding also reflects unary isomorphisms between original components.

#### Proof

The quotient virtual double category exists by Theorem 2.1. Its cartesian restriction and contextual unit universal properties are exactly the induced bijections on quotient cell fibres established there. This proves the virtual-equipment assertion, including every source arity and every surrounding unit context.

For the original-profile assertion, an original component (G,f:A→B) is sent to the graph span Gamma(Ff). On a full original input path, its tuple set is canonically in bijection with F(A_0). The left endpoint equation forces the coefficient map to be the initial-coordinate projection. The right endpoint equation then forces the original grade equality by faithfulness of F. Consequently each original profile and graph partition has at most one possible coefficient map before taking the quotient. Relation (3) therefore adds no equality there; it also creates no cell in an empty fibre. Partitions and all original scalar values are retained. This is precisely the full-profile identification proved in GraphSpanModel, Section 6.

For original-component isomorphisms, a globular unary cell forces the two ordered graphs to agree. A map between graph spans Gamma(Ff) and Gamma(Fg) with the same endpoints is forced by its left leg to be the identity on the apex, and then its right leg forces Ff=Fg and hence f=g. No new unary cell is created by quotienting. A unary scalar is invertible precisely when it is a unit of M, since scalar equality is unchanged. Thus the original component isomorphisms are exactly reflected. ∎

The theorem concerns this concrete semantic embedding. It does not silently assert that the new span-doubling horizontals in (4) are terms of a previously chosen free virtual presentation.

## 4. Quotient isomorphisms and noninvertible interface change

### Proposition 4.1 — The change from witness equality to support equality

Let c:(G,S)->(G,T) be a globular unary cell of scalar 1.

* If G is inactive, c is invertible in Q_I exactly when its actual coefficient map is bijective.
* If G is active, c is invertible in Q_I exactly when supp(S)=supp(T).

For a general scalar, scalar invertibility must additionally hold.

#### Proof

At inactive G, the two inverse equations are literal inverse equations for the coefficient maps. At active G, every available reverse endpoint-preserving map d:T->S is an inverse in Q_I, because both composites have the graph partition and scalar of the corresponding identity. Such a reverse map exists exactly when every supported endpoint pair of T is supported by S: for each finite nonempty target fibre choose a witness in the corresponding nonempty source fibre. The supplied c already gives supp(S)⊆supp(T). This proves the active assertion, including empty fibres. Scalar inverse equations are unchanged by (3). ∎

For the canonical interface-change comparison c:L->R, which forgets chosen internal lifts, the inactive criterion is therefore unique lifting of every actual target assignment. The active criterion is weaker:

    every external endpoint pair supporting an R-assignment
    supports at least one compatible lifted L-assignment.   (7)

Condition (7) does not require every individual R-assignment to lift. Several target assignments at the same endpoint pair may all be sent by a reverse map to one available lifted assignment. This distinction is essential.

These are finite support or fibre tests for a supplied path or tree. An invertible active-root comparison need not be invertible at an inactive intermediate graph. Moreover, the retained-bijection cut certificates below require actual bijections, even where the ambient quotient comparison is invertible by support alone. No root-only or support-only criterion is asserted for transport of those certificates.

## 5. Two precise cut groupoids over a fixed operation

For the cut theorem, all inner exact cells and all intermediate-isomorphism morphisms have scalar 1. The root retains its arbitrary prescribed m∈M. This isolates the coefficient-memory phenomenon without changing the ambient scalar calculus or claiming unique factorization for arbitrary nonunit inner scalars.

Fix a full source path p=(H_1,...,H_n), its interfaces A_0,...,A_n, an actual graph partition (U_1,...,U_n) of the retained whole G, an output span S_R, outer boundaries, and a root quotient cell [alpha] of scalar m. Fix a finite planar rooted cut tree T with that leaf frontier.

Each nonroot node v has its occurrence-indexed consecutive leaf run I_v, with its specified endpoints. Empty runs have their specified boundary position; repeated empty occurrences are not identified. Put U_v equal to the union of the leaf blocks in that run and G_v=G|U_v. Graph partitions at internal nodes are the canonical pullbacks of their child blocks. Identity (1) proves their typing. A run at a nonroot node may be the entire frontier, as happens after unary insertion.

Leaves carry the fixed source spans. For each nonroot internal node v choose an actual span S_v with the run's endpoints, and write E_v for its apex and P_v for the boundary-marked tuple set of its child spans. The root carries the fixed output span S_R.

### Definition 5.1 — The naive groupoid C_T

At each inactive nonroot internal node retain an actual endpoint-preserving bijection

    beta_v:P_v -> E_v.

At each active nonroot internal node retain only its quotient coefficient class, with the EXTRA existential requirement that the class possesses a bijective representative. No such representative is chosen there. At the root retain a quotient coefficient class gamma_T of scalar m. Substituting the tree's quotient cells must give [alpha].

A morphism consists of actual endpoint-preserving span bijections h_v:E_v->E'_v at the nonroot internal nodes. Leaf maps and the root output map are identities. At an inactive nonroot node require the literal equation

    h_v beta_v = beta'_v P(h_children(v)).                  (8)

At an active node this is required only in Q_I, where it imposes no coefficient condition. At an inactive root require

    gamma_T = gamma'_T P(h_children(root));                 (9)

at an active root require the corresponding quotient equality, which is automatic. Composition is componentwise composition of the actual h_v. These equations define a groupoid. The h_v are actual prequotient span bijections, not their identified classes in Q_I; this retention is essential to the stated isotropy calculation.

The existential requirement is deliberate: actual bijectivity is NOT a representative-invariant property of a quotient cell. For instance, at an active G, id_{\{0,1\}} and a constant map on {0,1} over singleton endpoints are equal in Q_I.

### Definition 5.2 — The certified groupoid D_T

An object of D_T is an object of C_T together with an actual bijective representative beta_v at every active nonroot internal node. A morphism satisfies (8) literally at EVERY nonroot internal node. The root equation remains the quotient equation (9). Thus the repair does not restore the root coefficient information intentionally forgotten by Q_I.

## 6. Exact isotropy, contractibility, and coherent contractions

### Theorem 6.1 — The cut-memory calculation

For every finite admissible tree T:

1. C_T is nonempty and connected. At an object x its automorphism group is canonically

       A_x = product_(v active, nonroot internal)
                       Aut_boundary(S_v).                  (10)

2. D_T is nonempty and contractible. The forgetful functor D_T->C_T retains exactly the actual inner bijections erased at active nodes.
3. There are coherent internal-edge contraction functors on both C and D. On C, contracting an active node v projects away exactly its factor Aut_boundary(S_v) in (10); contracting an inactive node removes no factor. Thus that contraction is an equivalence exactly when v is inactive or S_v is endpoint-thin.
4. Every contraction on D is an equivalence. Explicit splitting and unary/unit insertion maps give coherent comparisons for arbitrary finite sequences of contractions and changes of bracketing.

#### Proof of existence and connectedness

For each run I_v, take its canonical flat tuple-composite span with apex P(p|I_v). The canonical tuple-regrouping bijections give every beta_v. At the root, transport [alpha] along the canonical tuple-regrouping bijection. This is independent of the chosen representative of [alpha]: at an inactive root its coefficient is fixed; at an active root the resulting coefficient class is unique. Thus both groupoids are nonempty.

Given any C_T object, choose bijective representatives at its finitely many active nodes solely for this proof. Recursively composing these representatives with the retained inactive bijections identifies each intermediate span with its flat run-composite span. The induced tuple of span bijections satisfies (8) wherever that equation is imposed. Its root equation is precisely the requirement that the composite quotient cell is [alpha]. This gives an isomorphism to the canonical object, so C_T is connected.

#### Proof of the automorphism formula

Condition (5) implies that an inactive node cannot have an active descendant: every descendant graph is an induced subgraph of that node's graph. Consequently every subtree rooted at an inactive node is entirely inactive.

For an automorphism, leaf maps are identities. Equation (8), applied from the leaves upward through an inactive subtree, forces every h_v there to be the identity. At an active nonroot node its own coefficient equation imposes no condition. Its parent is also active, so the parent's coefficient equation imposes no further condition on h_v. The same applies when its parent is the active root. Therefore every endpoint-preserving bijection at an active nonroot node can be chosen independently, and all other h_v are forced. Componentwise composition identifies the automorphism group with the product (10).

Each factor has the explicit cardinality

       |Aut_boundary(S_v)| = product_(a,b) |E_v(a,b)|!.      (11)

This proves (10) as a group identification, not just a cardinality calculation. Since C_T is connected, it is equivalent to the classifying groupoid of this product group.

#### Proof of contractibility of D_T

All its inner bijections are retained. Between any two objects, equation (8) now recursively forces the unique candidate

       h_v = beta'_v P(h_children(v)) beta_v^{-1}.

It is an actual endpoint-preserving bijection. At an inactive root, the equality of the two flattened composites with [alpha], together with the invertibility of the inner tuple maps, implies (9). At an active root (9) is automatic. Hence the unique candidate is always a morphism. Nonemptiness then proves contractibility.

#### Actual contraction maps

Let v be a child of w and contract that internal edge. Replace the occurrence v in w's ordered child list by v's entire ordered child list and remove E_v. The induced graph partition is the one prescribed by (1).

In D_T, if w is nonroot, replace its actual bijection by

       beta_new,w = beta_w T_(...,beta_v,...),               (12)

where T is the explicit tuple-substitution function. It is bijective. If w is the root, use the quotient class of gamma_T T_(...,beta_v,...). This root class is independent of representative, for the same inactive/active reason used in the existence proof. On morphisms discard h_v. Substituting (8) proves all remaining equations, so this is a functor D_T->D_(T/v).

A contraction C_T->C_(T/v) also exists, but it must not pretend that an erased beta_v is still given. If w is inactive, both w and v are inactive, and their actual maps compose. If w is active, the new parent coefficient is its unique active quotient class; any representatives prove existence, and the class is independent of them. When w is nonroot, bijective representatives at the old nodes prove that the new class has a bijective representative. An active v cannot have inactive parent. Thus these cases exhaust the possibilities. Again discard h_v on morphisms.

Under (10), this latter functor deletes exactly the factor belonging to v if v is active and otherwise deletes no factor. Both groupoids are connected and nonempty. Such a functor is an equivalence exactly when its induced automorphism homomorphism is an isomorphism, which here is exactly the stated endpoint-thin condition.

#### Splitting, insertions, and coherence on D

To split a selected consecutive run of children, insert the canonical span with apex their tuple set, give the new node its canonical tuple bijection, and adjust the parent's retained map by the inverse tuple-regrouping bijection. At an active root this adjustment is interpreted as a quotient coefficient class. This defines a splitting functor D_(T/v)->D_T. Contracting the split recovers the original object through the specified tuple identifications. Splitting a contraction is naturally isomorphic to the original object by the unique span bijection read from its retained beta_v. Hence every D-contraction is an equivalence.

Unary insertion subdivides an edge using the same span and the canonical bijection P(S)->E_S. Its action on morphisms duplicates the corresponding h. Nullary unit insertion uses the actual unit span I_A, graph 0, coefficient id_A, and scalar 1 at its named empty boundary occurrence. This is insertion of the chosen unit, not deletion of an arbitrary empty witness.

Two successive contractions evaluate the same ordered tuple-substitution function by the checked substitution associativity of V. Identity (1) makes their induced graph partitions identical. Disjoint contractions, nested contractions, empty runs, and unary insertions satisfy the same identities. Thus the displayed functors and their explicit splitting comparisons are coherent at every finite tree depth. This is an actual tree-level construction, not an inference of coherence merely from contractibility. ∎

### Corollary 6.2 — Exact unmarked domain at a fixed profile

Fix the flat profile and retained partition. Every naive contraction over every admissible cut tree is an equivalence if and only if the flat composite span of every realizable active run at a nonroot node is endpoint-thin. The quantifier includes runs of length one, runs containing empty graph blocks, occurrence-positioned empty runs, and the whole frontier when unary expansions are admitted.

#### Proof

Every exact intermediate span is isomorphic to its flat run-composite span, by the same recursive tuple comparison used above. Thus its endpoint-fibre cardinalities are determined by that run. The criterion follows from Theorem 6.1 for every contraction.

Conversely, a realizable active run with a nontrivial endpoint automorphism can be exposed as a single inner node, with its canonical flat composite span. For the entire frontier use a unary root; for a singleton run insert a unary node at that occurrence. Its contraction then has the nontrivial kernel calculated in (10), so is not an equivalence. Empty-run unit spans have no such nontrivial endpoint automorphisms. ∎

This is a fixed-profile criterion. It is not asserted to remain true after arbitrary new substitutions without checking the newly realizable runs. The certified construction does not need this endpoint-thin restriction.

## 7. The exact finite equivariant marking bound

We specify the preservation requirement before giving the bound. Let x be a naive cut object, and A_x its actual automorphism group (10). A permitted finite-memory repair assigns a nonempty finite set L_x of marks, equivariantly under every actual isomorphism of the naive groupoid. Its decorated morphisms transport these marks; the repair does not separately delete or identify the original actual span-isomorphism morphisms. Equivalently, this is the category of elements of a finite-set-valued functor on the connected naive groupoid. Over the component of x it is equivalent to the action groupoid L_x//A_x.

### Theorem 7.1 — Sharp bound in this marking model

If such a repair has trivial stabilizers, the A_x-action on L_x must be free and

       |L_x| >= |A_x|.

If the repaired component is contractible, that action must be free and transitive, so

       |L_x| = |A_x|
             = product_(v active, nonroot) product_(a,b)
                                      |E_v(a,b)|!.         (13)

The retained-bijection certificates of D_T attain equality.

#### Proof

The automorphism group of a marked object l is its stabilizer in A_x. Thus trivial stabilizers are exactly freeness. Every orbit of a free finite action has |A_x| elements, giving the inequality. The connected components of an action groupoid are its orbits, so contractibility additionally requires transitivity and gives equality.

For the explicit certificates, at fixed naive x the possible actual beta_v at each active node form the set of endpoint-preserving bijections P_v->E_v. This is nonempty and has |Aut_boundary(S_v)| elements. Such choices are independent: if any active node occurs, the root is active, so changing its representative does not alter the required root quotient equality. Thus the certificate set has the product cardinality (13).

An automorphism h of x acts by

       beta_v |-> h_v beta_v P(h_children(v))^{-1}.          (14)

If it fixes every certificate, (8) holds literally at every node. The recursive argument for D_T forces every h_v to be identity. Hence the action is free; its cardinality equals |A_x|, so it is transitive. This proves sharpness. ∎

This is not a universal computational-space bound. A skeleton alone retains isotropy, but canonicalizing representatives while discarding their nontrivial transports, taking pi_0, or quotienting the automorphism groups can avoid carrying these choices by changing the preserved information. Such constructions are not excluded: they are different repairs, not equivariant markings over the same naive witness groupoid.

## 8. Unbounded obstruction family and graph-dependent reassociation

Take the activation predicate (6), singleton interfaces, n≥2, and any fixed active graph G with at most N vertices. Let the source consist of one G-slot with an n-point span apex followed by d≥2 empty-graph unit slots. The retained partition is

       (V(G), empty, ..., empty).

Take a singleton root output apex, its unique coefficient map, and any root scalar m. Every exact composite containing the G-slot has n apex witnesses; every composite of only the unit slots has one.

In the left-associated binary tree, each of the d−1 proper internal nodes contains the G-slot and is active. Its naive automorphism group is therefore

       (S_n)^(d-1).

In the tree which first combines all empty slots and then joins them to G at the root, every proper internal graph is empty and inactive. Its naive automorphism group is trivial. Both groupoids are connected, so they are not equivalent. Arity and depth grow with d while the retained graph is fixed.

The certified repair has exactly (n!)^(d−1) possible marks over a fixed left-comb object. In the marking model of Section 7 this is (d−1)log_2(n!) information bits; a fixed-length binary encoding needs the ceiling of that number.

A cross-edge version uses three singleton graph blocks and a retained edge between the first two vertices. The bracketing ((0,1),2) has an active proper intermediate; the bracketing (0,(1,2)) has an inactive proper intermediate. Giving the first source span n witnesses and the others one yields S_n versus trivial naive isotropy. Thus the obstruction is sensitive to actual induced graph cuts, not just a separately attached scalar or a fixed group factor.

## 9. What the combined theorem establishes

The construction proves, for the stated concrete family:

* a finite graph-incidence criterion for a genuinely graph-dependent coefficient quotient;
* exact generation by the unary span-doubling section equations;
* preservation of cartesian restriction uniqueness and contextual units;
* complete recovery of original graph-span operation profiles and original-component isomorphisms;
* the distinction between witness-bijective transport and endpoint-support invertibility;
* the exact all-tree naive isotropy and contraction-equivalence criterion;
* a coherent retained-bijection tree repair and a sharp finite equivariant-marking bound.

The repair keeps actual graph partitions, actual intermediate spans, and their genuine endpoint-preserving isomorphisms. It neither inverts nonuniversal graph assemblies nor identifies different retained whole graphs.

## 10. Remaining limits and proof provenance

The ambient definitions and their laws are the proved concrete construction in GraphSpanModel.md. The present quotient, generation argument, cut groupoids, morphism equations, contraction maps, and memory calculation are defined and proved above. No arbitrary-equation decidability theorem or generic least-congruence closure theorem is substituted for these claims.

The following are NOT asserted here:

1. That the span-doubling horizontal S[2] is already a named term of a free virtual envelope generated only by the old graph spans, restrictions, and units. A free-presentation theorem for (4) needs an explicit typed bridge or additional span generators.
2. A universal property for a new free ordinary-equipment quotient. Theorem 3.1 is a concrete semantic conservation result.
3. A global simplicial 2-Segal object with all outer faces. Theorem 6.1 supplies the rooted tree-level contraction, splitting, and unit maps over a fixed outer operation. An arbitrary root coefficient map has no automatic restriction to a deleted interval, so global outer faces require a separate construction.
4. Descent of actual coefficient bijectivity as a property of quotient cells. D_T deliberately retains a bijective representative.
5. Unrestricted preservation of the endpoint-thin unmarked subdomain under grafting, or certificate transport along every ambient quotient isomorphism.
6. An absolute algorithmic or representation-size lower bound. Equation (13) applies exactly to the finite equivariant marking doctrine stated in Section 7.

These boundaries are part of the theorem, not deferred qualifications to a broader claim.

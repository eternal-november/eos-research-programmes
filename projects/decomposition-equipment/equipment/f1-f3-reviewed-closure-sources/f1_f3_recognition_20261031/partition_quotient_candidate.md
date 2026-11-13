# Hereditary permutation quotients of original ordered graph cuts

31 October 2026. Author derivation, not independent acceptance. This is a new structural quotient/cut theorem and a concrete presentation/refinement extension; it is **not** by itself a declaration that original F1/F3 are discharged. No new vertex colours, located components, or altered original whole/profile equality are introduced.

## 0. Frozen scope and source imports

For each finite N, finite nonempty category K, and induced-restriction-closed family F of original ordered graphs on at most N vertices, use the original C1/C5 signature restricted to F. Wholes remain (G,f), and input profiles retain every original standardized ordered graph, actual K arrow, interface and occurrence. Empty graph is included. Arity and depth are unbounded. Principal mixed examples permit N>=6 and the three-object chain. The theorem takes M=1. Nontrivial original scalar monoids are NOT silently quotiented out: their already proved scalar factorization obstruction remains outside this positive cut class.

Imports, not new results:

* `../contract_revision_20261028/extracted/witnessed_decompositions/research/workstream_A/rewrite/A3_LOCAL_COMPARISON.md` §§1–6: original actual C,U,D generators, seven equations, flat-cut substitution, right-comb completeness and actual A3 quotient maps.
* The same directory's `THEOREM.md`, termination measure (B,A,H,D): all four entries depend on tree shape/decorator locations, not binary partition labels.
* `../contract_revision_20261028/extracted/witnessed_decompositions/research/workstream_integration/proof/Completion_Comparison.md` §§2–8: independently presented refinement completion, O/MOut/MIn, full occurrence-indexed Hom inverse, and comparison criterion. The extension below verifies its hypotheses for the new rules; it does not merely appeal to object equality.
* Original contract §§F1–F3 and `source_obligation_map.md` supply the unchanged floor and earlier scientific nonacceptance warning.

A graph has canonical vertex set [r]. Write e_U:[|U|]→U for increasing enumeration. For g∈Sym([r]), put

    rho(g,U) = e_(gU)^(-1) g e_U.

For each G choose an explicitly given subgroup H_G≤Sym([r]). No symmetry is added to the occurrence order: H_G acts on VERTEX placements, never on input slots.

## 1. Sharp primitive criterion

The two conditions are:

**R (hereditary restriction).** For every G, g∈H_G and U⊆[r], the standardized ordered graphs G|U and G|gU are literally equal, and rho(g,U) belongs to H_(G|U).

**E (extension by identity).** For every G,U and h∈H_(G|U), the permutation equal to e_U h e_U^(-1) on U and identity outside U belongs to H_G.

Define the orbit of an actual ordered partition pi=(U_1,...,U_n) by g pi=(gU_1,...,gU_n), retaining all original whole/profile data. R's graph-equality clause ensures this is an action within every actual profile fibre.

**Theorem 1.** On the full original partition operation family (empty blocks and arbitrary arity included), R and E are necessary and sufficient for these literal orbit classes to support representative-independent original substitution and representative-independent canonical interval cuts with bijective cut/flatten maps. Necessity means that the orbit action is fibrewise, quotient substitution is the original substitution on representatives, and cuts are the original induced-union cuts. It is not a classification of unrelated possible quotient cut doctrines.

### Sufficiency: substitution is derived

For inner operations pi_i on G|U_i, original flattening uses e_(U_i) on their blocks. Replacing an inner operation by h_i pi_i changes the flattened operation by the identity-outside extension of h_i from U_i, which is in H_G by E. Several occurrences are handled independently; their supports are disjoint, including empty supports.

Now replace the outer partition pi by g pi but leave the chosen inner representative pi_i unchanged in its original canonical coordinates. Acting by g on the old flattening produces the new outer blocks with inner operations rho(g,U_i) pi_i. By R those inner operations are in the same local orbits. By the already established inner-change invariance, their flattening equals that using pi_i in the quotient. Thus arbitrary simultaneous outer and inner changes preserve the quotient result. Unit and associativity descend from original flat-cut laws. This is not assumed compatibility.

### Sufficiency: canonical cut and inverse

For 0≤i≤j≤n, let U=U_(i+1)∪...∪U_j. The intermediate component is exactly

    X=(G|U, f_j ... f_(i+1)): A_i→A_j,

using id_(A_i) if i=j. Inner blocks are e_U^(-1)(U_k), i<k≤j. The outer operation replaces that consecutive list by U, preserving prefix/suffix and replacing its arrows by their composite. Acting by g changes the outer cut by g and the inner cut by rho(g,U). R therefore proves representative independence and unchanged intermediate component.

Conversely choose any pair of orbit classes with matching intermediate component and the prescribed interval profiles. Choose representatives, substitute, and take the quotient. Representative independence was proved above. Cutting this flattening gives the original pair of orbit classes, literally for chosen representatives. Flattening the cut gives the original class. Thus the exact F1 disjoint-union-over-components factorization map is bijective, with specified inverse.

For j=i, only X=(empty,id_(A_i)) can have the required nullary operation; outer inserts an empty/id occurrence. For j=i+1, the inner operation is the unique unary identity. For (i,j)=(0,n), outer is the unique unary identity. For n=0, the same construction is the designated nullary unit and unary identity on (empty,id_A). No empty nonidentity-arrow component is mistaken for a nullary unit. All interfaces are actual A_i,A_j, not merely matching cardinalities.

Nested/disjoint cut iteration is coherent: on representatives it restricts to the same unions and uses e_U e_V=e_(e_U V); on classes it is independent of representatives. Equivalently every tree's flattening bijection is obtained by successive binary cut inverses, and uniqueness identifies every order/rotation of those inverses. Hence all triangulations, not only a quadrilateral, are covered.

### Necessity: singleton partitions detect the group, with no kernel

Assume fibrewise orbit action, lawful descended substitution, and canonical cut descent (bijectivity is more than needed). K nonempty permits arbitrarily long constant identity-arrow paths at one object, so there is no admissibility obstruction to the following probes.

Fibrewise action on (U,U^c) forces G|U=G|gU. For any U, arrange all vertices of U first as singleton input occurrences in increasing order, followed by all complementary vertices as singleton occurrences. Compare this partition with its image under g. Cut the first |U| occurrences. The inner singleton lists differ by exactly rho(g,U). Cut descent identifies their H_(G|U)-orbits. The action on a completely labelled singleton tuple is free: a permutation realizing the equality must be rho(g,U) itself. Thus rho(g,U)∈H_(G|U), proving R.

For E, take outer blocks U followed by each complementary vertex as its OWN singleton occurrence. In U compare the canonical singleton partition with its h-image, h∈H_(G|U). These are equivalent inner operations. Congruence makes their flattened singleton partitions H_G-equivalent. Any g realizing that equivalence is forced, occurrence by occurrence, to act as e_U h e_U^(-1) on U and fix every outside vertex. Thus the extension by identity lies in H_G. Empty U is harmless. This proves E exactly, not only modulo an unspecified kernel.

## 2. Concrete positive family: ordered contiguous clique unions

Let F consist of ordered disjoint unions of complete graphs, each connected component occupying a contiguous interval of vertices. Include the empty graph. Induced restrictions remain in F. For canonical clique intervals C_1,...,C_t of sizes r_1,...,r_t, take

    H_G=Sym(C_1)×...×Sym(C_t).

For any U, G|U is the ordered disjoint union of the nonempty C_a∩U, retaining their original order. A within-clique permutation preserves their sizes and rho permutes vertices only within each surviving clique; hence R. A local within-clique permutation extended by identity remains within the original clique; hence E. This verifies primitive conditions on genuine original ordered graphs, not newly coloured vertices.

An orbit is exactly its **occupancy matrix**

    a_(b,k)=|C_b∩U_k|,

whose row sums are r_b. Whole G, full K path, input occurrence order and all input graph types are retained. The k-th input graph is the ordered disjoint union of the positive entries of column k as clique sizes. Conversely these matrices are realized by partitions; two realizations differ by independent within-clique permutations, proving the orbit classification.

Substitution is explicit: for each column k, its inner matrix has rows indexed, in order, by those original rows b with a_(b,k)>0. Replace a_(b,k) by that corresponding inner row; if a_(b,k)=0, insert zeros across this occurrence's whole replacement profile. Concatenate columns in the original slot order. This includes nullary replacements, possible only for empty/id inputs.

For a selected interval of columns, sum those columns to one outer column. Its positive rows index the inner matrix, obtained by retaining the selected columns and deleting zero rows. The inverse replaces the summed column by those inner rows, reinserting zero rows at the uniquely specified positions. No local isomorphism choice or hidden colour is required.

**Nontriviality.** On G=K_2, the partitions ({1},{2}) and ({2},{1}) become equal. The crossing edge is still present in the retained whole. The same singleton input profile also admits whole K_1⊔K_1; these two wholes remain unequal. Thus the ordinary Segal comparison is not injective and input pieces do not specify a single-valued composition. For a nonhomogeneous positive example use K_2⊔K_1; unlike full placement erasure this quotient retains which original clique supplies each occurrence. For six vertices use K_3⊔K_2⊔K_1 and any composable nonidentity arrows 0→1→2 with enough identity-arrow occurrences to support the desired columns. Every matrix row can split across multiple columns, retaining actual cross-block edges.

## 3. Explicit all-degree simplicial model

For n≥0, X_n consists of G∈F, an n-column occupancy matrix with positive row sums equal to the ordered clique sizes of G, and a composable n-arrow K path. For n=0 there are no rows or vertices and the datum is precisely an object A of K.

* Interior d_i, 0<i<n: merge columns i and i+1 by addition; compose the corresponding K arrows.
* d_0 or d_n: delete the first or last column; delete resulting zero rows; replace the whole graph by the ordered clique graph with the remaining row sums; delete the corresponding end arrow/object.
* s_i: insert a zero column at position i+1 and the identity arrow at A_i. Whole graph unchanged.

Deleting zero rows does not merge adjacent surviving rows: they represent distinct disconnected cliques even when the original intervening clique vanishes. Column deletion/addition and zero insertion satisfy all simplicial identities; the K-coordinate identities are category laws. This can alternatively be checked directly by assigning each surviving vertex row entry to its final column; dropping rows of zero final total is independent of the order of deletions. The formula for every monotone map follows by selecting its endpoint range, grouping the consecutive column intervals between its images (empty intervals give zero columns), and deleting zero rows.

The diagonal comparison for any interval is the matrix cut/inverse above. Iteration gives all triangulation bijections. Zero-column degeneracies are exactly units. Each degree is finite for fixed N,K, but arbitrarily large n has degenerate simplices. Operation fibre over the long edge (G,f) and the consecutive input edges is precisely the quotient calculus of §2, not merely an equicardinal set. Its cut inverse defines exactly the substitution already computed.

This is a constructive positive discrete 2-Segal object. It does not replace F2's separately mandated exhaustive C certificate on ALL original graphs, nor establish a general morphism-level F3 recognition equivalence by itself.

## 4. Actual finite C5 presentation and effective B3 transfer

Retain the original finite generators C,U,D and original seven declared equation templates, with M=1 and graphs restricted to F. Add the following literal finite binary templates:

    L: C(G;U,V;a,b)(x,y) → C(G;U*,V*;a,b)(x,y),

when U is not canonical. Here within each original clique C_b, U* is its first |C_b∩U| vertices and V* its remaining vertices. These two cuts have the SAME original input graphs, output graph, actual arrows and occurrence profile. Thus L is a lawful A3 parallel equation, not a semantic-kernel declaration. Both variables occur exactly once, in the same order.

More generally, for an arbitrary finite R/E family, choose the lexicographically least binary partition in each H_G orbit; the same L construction works because R ensures common profile. The concrete clique rule needs no group search.

**Termination.** Append to the original lexicographic measure (B,A,H,D) the number Lbad of noncanonical binary labels. An old rewrite decreases its original tuple, regardless of any change to Lbad. A new L rewrite preserves the first four entries and decreases Lbad by exactly one: the output/input graphs of the rewritten corolla and every child subtree are unchanged. Thus the full orientation terminates, including contextual instances.

**Normal forms and completeness.** The old shape argument says an irreducible has no decoration (M=1), is u_A in arity zero, the identity leaf in arity one, and a right comb in arity≥2. New irreducibility requires every binary label canonical. A matrix determines exactly one such right comb: first column supplies root left-clique occupancies, the remaining-column row sums supply the right input graph, and recursively the remaining columns determine its right subtree. Actual arrows are the prescribed first arrow and composite suffix. Conversely its evaluation has that matrix. Therefore normal forms are unique for the independent quotient semantics. Termination plus uniqueness gives confluence, and equality in the actual A3 quotient iff equal matrices, whole and full profile. The inverse map is the class of this canonical comb. Both strict inverse laws follow exactly as in A3 §§5–6, using the independently proved quotient substitution, not defining that substitution through syntax.

For a general R/E family, canonical interval-cut uniqueness replaces the matrix argument: choose the canonical representative of the first binary-cut orbit, then recursively the unique tail orbit. This gives the same induction.

**Effective ordinary coherence.** For fixed N,K the labelled template list is finite. Enumerate every ordered pair of rules and every nonvariable node in a left-hand side; retain the syntactically unifiable, well-typed overlaps. This is a finite algorithm on the finite declared signature, not an equality oracle. For each resulting critical peak l←t→r, reduce l and r using a fixed address/rule-order normalizer. They terminate at the same explicit canonical comb; record those two normalization words as its joining equation. Include the old/new disjoint-redex and unique-variable-residual squares. The local critical-peak argument covers every contextual peak: all rules are linear and preserve the same ordered frontier, including actual u rather than a deleted variable. This supplies finite local critical joining data for an O_L relation scheme. It is not the axiom 'all parallel equation paths agree'.

The well-founded proof of `Completion_Comparison.md` §3.2 now applies verbatim to (B,A,H,D,Lbad) and O_L, yielding the canonical equation path kappa(t,u)=nu_t nu_u^(-1). For MOut the L redex survives grafting because its two variable occurrences remain distinct and in their original order. For MIn its two bare corollas are legal forests with the same ordered typed leaves. Thus §4's elementary-to-arbitrary forest derivation applies to L as well as old rules, including nullary grafts.

Consequently the independently generated category with raw graft edges, old and L equation edges, O_L, MOut and MIn is equivalent to Ref(matrix-cut). Objects are still raw trees; arrow images remain the ACTUAL occurrence-indexed tuples of matrix operations, not only their composite. The Hom inverse is the source formula

    b=(b_i) ↦ R(T,(NF(b_i))_i); kappa(T[NF(b_i)],U),

and the existing section/natural comparison/triangle arguments apply with this NF and kappa. A sound alternative path-relation family yields that comparison equivalence iff it entails the full O_L/MOut/MIn basis, by the same faithful-comparison converse. No decision procedure for entailment of arbitrary alternative relations is claimed.

Thus this is a presentation and refinement compatibility result beyond merely decorating the known nerve: it identifies concrete binary partition-collapse equations, proves their convergence, and derives their mixed comparison relations.

## 5. Quotient-map lifting is DIFFERENT from intrinsic unique cuts

Let q send an original labelled clustergraph partition to its occupancy matrix; the formulas in §3 prove it is simplicial, including outer restriction and zero-row deletion. It is generally NOT CULF.

For an active monotone map alpha:[m]→[n], alpha(0)=0 and alpha(m)=n, fix an original coarse m-block partition B_j and a compatible fine target occupancy matrix a_(b,k), 1≤k≤n. Compatibility includes equality of the full K paths after alpha: the fine-arrow composites over every alpha interval equal the prescribed coarse arrows, with identity for an empty interval, and all boundary interfaces agree. Without that typed compatibility the fibre is empty, irrespective of matrix counts. Subject to it, graph compatibility says

    s_(b,j):=|C_b∩B_j| = sum_(alpha(j-1)<k≤alpha(j)) a_(b,k).

The fibre of actual fine partitions lifting those data has cardinality

    product_(b,j) s_(b,j)! / product_(alpha(j-1)<k≤alpha(j)) a_(b,k)!.

Proof: within each known set C_b∩B_j independently choose the labelled finer subsets of those required sizes. Empty alpha-intervals force s=0 and contribute 1 (0!=1). These independent multinomial choices give every lift uniquely.

For K_2 and a coarse one-block partition, the target split (1,1) has two actual lifts. Hence q is not CULF. On the complete all-cuts family, q is CULF iff every clique has size≤1: if all are singletons the occupancy records every original vertex placement, so q is an isomorphism; if some clique has size≥2 split it nontrivially and the displayed fibre exceeds one. This includes N=0 and empty blocks correctly.

There is no contradiction with §1: the TARGET has unique cut pairs modulo H, while q may have several original lifts at a fixed original coarse source. This also prevents conflating the new completion comparison with the older fixed-endpoint refinement-lifting classification, whose hypotheses forbid partition collapse.

## 6. Remaining boundaries and review targets

1. R/E criterion, normal forms, the matrix nerve and multinomial fibre formula above are author proofs requiring adversarial review; no acceptance ledger changed.
2. Necessity uses all original singleton-partition probes, nonempty K and unbounded arity. If a restricted admissibility doctrine removes them, only the sufficient direction is asserted without a new analysis.
3. General F3 forward/reverse constructions with an independently specified target morphism class are not supplied here; the root recognition note must provide them or state the remaining gap. A target class defined merely as 'the image' would not suffice.
4. Old scalar M≠1, arbitrary interface changes, and non-cluster ordered graphs are not claimed positive merely by this family. R/E can be tested on other induced-closed graph families but does not assert every automorphism group satisfies R.
5. The known restriction-species/invertible-operad theory remains baseline. Scientific significance must be separately reviewed for the SHARP R/E quotient criterion, effective actual-syntax extension, and distinction between intrinsic unique cuts and exact multinomial fixed-source lifting—not for the existence of a graph nerve alone.

## 7. Exhaustive uncoloured simple-graph classification (additional author theorem)

The abstract R/E hypotheses are unusually rigid in the ORIGINAL uncoloured graph setting. The following classification is stronger than a cluster-family example. It assumes all singleton-partition tests and the same full fibrewise actions as Theorem 1.

Let the **edge flag** be 1 exactly when the complete two-vertex graph belongs to F and its subgroup is S_2; otherwise 0. Let the **nonedge flag** be defined likewise for the edgeless two-vertex graph. Every subgroup on two vertices is either 1 or S_2.

**Theorem 2.** A group family satisfies R/E iff it is one of the following (with unavailable two-vertex types treated vacuously):

| edge flag | nonedge flag | allowed graphs F | forced H_G |
|---|---|---|---|
| 0 | 0 | any induced-closed ordered simple-graph family | trivial |
| 1 | 0 | induced-closed subfamily of contiguous disjoint complete cliques | product of symmetric groups on connected components |
| 0 | 1 | induced-closed subfamily of complements of those graphs, i.e. complete multipartite graphs with contiguous independent parts | product of symmetric groups on those independent parts |
| 1 | 1 | induced-closed family consisting entirely of complete or edgeless graphs | full symmetric group on every graph |

The flag definitions themselves must match the listed family: for example an active edge flag requires the edge type to occur. Overlap of descriptions in degenerate tiny families does not give different actual group assignments.

### Permutation lemma

For any permutation g, let Inv(g) consist of pairs a<b with g(a)>g(b). Then g lies in the subgroup generated by the transpositions (a b) for pairs in Inv(g). Proof: form the inversion graph on positions. If (a,c) is an inversion and a<b<c, then either g(a)>g(b) or g(b)>g(c), so b joins the same connected component. Thus every component is an interval (unions of edge intervals along a connecting path remain intervals). Distinct interval components have no inversions between them, so every value in an earlier component is smaller than every value in a later one. Since these image sets partition [r] with the original component cardinalities, g preserves each component as a set. Edge transpositions of a connected graph generate its full symmetric group (a path conjugates its edge swaps to an arbitrary endpoint swap); therefore the inversion transpositions generate a group containing g. This includes singleton components, identity and r≤1.

### Necessity proof

For g∈H_G and any inversion pair U={a,b}, rho(g,U) is the nontrivial permutation on two elements. By R the two-vertex type of G|U has active flag. By E, the transposition (a b) belongs to H_G. Conversely every pair whose type has active flag supplies its transposition to H_G by E. The permutation lemma therefore gives the exact equality

    H_G = < (a b) : the edge/nonedge type of {a,b} has active flag >.    (7.1)

There is no unspecified higher-arity group datum left.

Every H_G permutation preserves the underlying adjacency relation (it need not preserve the vertex order, and is not being called an automorphism in the category of ordered graphs): R applied to two-element subsets preserves adjacency. With only edge active, (7.1) is the product of full symmetric groups on connected components. Such a group acts by graph automorphisms only if each connected component is complete: on a component of size≥2 the group is transitive on unordered vertex pairs, and connectedness supplies an edge. Components are contiguous as well. If a<c are in one component, (a c)∈H_G. For a<b<c the pair (a,b) is an inversion of (a c), so by the preceding argument (a b)∈H_G. It follows that b is in the same connected component. Thus every component is an interval. This proves the second row.

With only nonedge active, apply exactly that argument to the complement graph. With both flags active, (7.1) gives all of Sym([r]); graph-automorphism invariance forces all unordered pairs to have the same adjacency, so each graph is complete or edgeless. With neither active, (7.1) gives the trivial group. This proves every necessity assertion.

### Sufficiency proof

Trivial groups satisfy R/E immediately. Contiguous clique products were checked in §2. For complements of contiguous clique graphs, restriction commutes with complementation, so the identical block proof applies. For homogeneous complete/edgeless graphs, every subset is the homogeneous graph of its cardinality, all rank permutations are allowed, and every identity-outside extension is in the full symmetric group. Thus all four cases satisfy R/E.

### Consequences and limits

This classification explains WHY the uncoloured positive example is constrained: one cannot freely decide to collapse a few vertex symmetries at high graph size while retaining coherent cuts and substitution. Two-vertex behaviour forces the entire family. In particular nontrivial edge-type collapse on a family containing a non-cluster ordered graph is obstructed, not merely unproved. This remains a theorem about these literal permutation-orbit quotients; it is not a claim to classify every possible congruence on the original graph calculus.

For sharp finite independent failures, use all complete graphs of sizes≤3. Set H_3=S_3,H_2=1 and H_1=H_0=1: E holds but R fails; two equivalent singleton partitions have inequivalent length-two inner cuts. Set H_3=1,H_2=S_2 and H_1=H_0=1: R holds but E fails; swapping the two local singleton occurrences within a two-vertex block gives equivalent inner operations whose three-vertex flattened singleton partitions are inequivalent. Both examples are fibrewise typed and isolate the claimed primitive hypothesis.

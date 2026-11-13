# Anchored reconstruction across partially visible crossing charts

## Plain-language abstract

Several decompositions can each work correctly on the part of a system they expose, and every pair can be mutually consistent, while the entire family cannot describe one shared component. The obstruction is not an arbitrarily assigned permutation around a loop. It comes from actual whole-system events: if two decompositions expose the same event at the same designated component position, they must identify the same component event. A chain of such obligations can identify two events that one local decomposition requires to remain distinct.

This note gives a finite reconstruction procedure for that situation. It also accounts for interfaces that duplicate or omit boundary values, rather than treating every interface change as invertible. Besides preventing unwanted identifications, a reconstruction must supply exactly the local events required at every lifted boundary value. The remaining choices are a finite partition problem, with explicit certificates for failure and a classification of the resulting witnessed components. The elementary partition machinery is standard; the contribution sought here is its exact derivation from witnessed crossing decompositions and its interaction with interface restriction. Physical implementability remains a separate obligation.

## 1. Scope and primitive network data

Fix a designated typed component occurrence `v` in the network schema. Its global boundary carrier is a finite set E (for spans, E=B×C). This designation is essential: there is no requirement that unrelated components reconstructed by different cuts be identified.

There is a finite family of crossing charts i. Each has the four-component grid of the cylinder reconstruction theorem in `../foundations/Crossing_Grid_Cylinder_Reconstruction.md`, including its actual supplied whole matching θ_i, and an actual local realization `(T_i,α_i,β_i)`. These may be selected from the complete local realization groupoid rather than assumed unique. Let `e_i:T_i→E_i` be its local boundary map and let `p_i:E_i→E` be a specified, arbitrary function. Injectivity or surjectivity is not assumed.

There is a fixed set W of actual whole events, and each chart sees a subset D_i⊆W. These are explicit source-level witness subobjects. They are NOT asserted to be cartesian restrictions along whole endpoint maps; physical realization of these selections is a separate model obligation. Its exposure to the designated occurrence is derived, not separately supplied: the chart identifies each w∈D_i with an actual tuple in its whole composite; apply α_i^{-1} to its P-coordinate (equivalently β_i^{-1} on its other parent) to extract `π_i(w)∈T_i`. The local θ_i equation guarantees agreement of the two extractions. The tuple identification is part of the observed decomposition data, not an arbitrary map between chart components.

Require boundary consistency on actual shared whole events:

    p_i e_i π_i(w) = p_j e_j π_j(w),  w∈D_i∩D_j.       (1)

A failure is already a typed network obstruction.

A generated global reconstruction consists of a finite T→E and, for every i, a bijection over E_i

    h_i:T_i ≅ E_i ×_E T,                              (2)

such that, writing k_i=pr_T h_i,

    k_i π_i(w)=k_j π_j(w) on D_i∩D_j.                 (3)

Generated means every t∈T occurs in some k_i(T_i). It excludes completely unobserved events, not events invisible to W but visible in a local component. All original α_i,β_i and θ_i remain fixed. Thus this is simultaneous reconstruction of one designated component across a family of genuine crossing charts; it is not yet a theorem reconstructing every unknown component of an arbitrary network simultaneously.

## 2. Derived finite criterion

Form the tagged disjoint union X=⊔_i T_i. Give x=(i,t) global type τ(x)=p_i e_i(t). Generate an equivalence relation F by

    (i,π_i(w)) F (j,π_j(w)) for actual shared w.       (4)

Only equality of actual whole events generates (4). No overlap bijection or arbitrary holonomy assignment is input.

Call an equivalence relation K on X admissible when:

* A1: F⊆K.
* A2: τ is constant on each K-class.
* A3 (no local fibre collapse): for every i and z∈E_i, each K-class contains at most one element of `T_i,z=e_i^{-1}(z)`.
* A4 (cartesian coverage): if a K-class has type e, then for every i and every z∈p_i^{-1}(e), it contains exactly one element of T_i,z.

A4 includes the at-most-one condition A3, but separating them exposes the two failure mechanisms. In particular, an empty local fibre over a lift of e forbids any global event of type e, even if another chart sees one. Noninjective p_i requires the same global event to have separate local representatives at EVERY lift z. One must not replace A3 by injectivity of the whole map T_i→T: that is false under duplicated interfaces.

### Theorem 1 (exact generated reconstruction)

For fixed local realizations, a generated global reconstruction exists iff an admissible K exists. Its isomorphism classes are in bijection with admissible equivalence relations K. Every fixed-local-data realization has trivial automorphism group.

**Proof.** Given T and h_i, set x K y iff their k-images agree. Shared-event equality gives A1, boundary typing gives A2. Since h_i is a bijection, each t of type e has exactly one representative at every z above e, giving A3/A4. Generatedness identifies T with X/K.

Conversely let T=X/K and give [x] type τ(x). Define h_i(t)=(e_i(t),[(i,t)]). A3 proves injectivity; A4 proves surjectivity onto E_i×_E T. A1 gives (3). Substitution of h_i into the original local α_i and β_i transports them to isomorphisms with the cartesian restriction of T; their equations with θ_i continue to hold because they are conjugated by the same h_i. Thus BOTH crossing decompositions of each chart, with their actual supplied whole matching, are recovered simultaneously. Every t has a representative, so the realization is generated. Any global automorphism commuting with all h_i fixes every represented event and is the identity. Finally a morphism between the quotient constructions exists iff their kernels agree, and is then unique. ∎

This proof gives the simultaneous factorization maps, not merely a set-theoretic amalgam. It does not produce additional unknown contexts or certify that a span quotient has an implementation by permitted physical gates.

### Effective construction and certificates

First compute F by union-find. A mixed-type F-class or two different elements of one T_i,z in an F-class is an immediate NO certificate: a finite chain of actual shared whole events, ending in a type conflict or a local distinction.

Otherwise enumerate coarsenings of the finite set X/F, disallowing mixed types and local fibre collisions, and test coverage A4. This terminates. More explicitly, introduce equality variables x_ab on F-classes. Impose reflexivity, symmetry, transitivity, forbidden-pair inequalities, and for every class a of type e and every local lift z over e impose

    OR_{b containing an occurrence in T_i,z} x_ab.

Together with forbidden same-fibre mergers this is exactly-one coverage. Therefore the criterion is a finite, explicitly constructed Boolean problem on actual witness data, not an instruction to solve an unspecified descent condition. Exponential search is not claimed novel or efficient. Failure of the least relation F to cover every lift is NOT itself a NO certificate: optional mergers can repair it. Only forced collisions are immediate obstructions; remaining failures require the finite packing/coverage search.

When F already satisfies A4, it is a canonical minimal reconstruction. Additional admissible mergers may still exist unless A3 forbids all of them. Fully anchored fully visible single-chart input with p_i=id forces precisely its original T, so this theorem adds no artificial obstruction to the local cylinder theorem.

## 3. Three individually correct and pairwise compatible charts with no joint component

Let W={a,b,c,x1,x2,y1,y2,z1,z2}. The visible domains and local two-sheet quotients are:

    D1={a,b,x1,x2}:  {a,x1} | {b,x2}
    D2={a,c,y1,y2}:  {a,c}  | {y1,y2}
    D3={b,c,z1,z2}:  {b,c}  | {z1,z2}.

Each pair of domains overlaps in exactly one actual event. Take E=E_i=1 and p_i=id. Every T_i has two events. Any two charts admit a bijection of their two event sets respecting their single shared event, so each pair has a generated reconstruction. But the full family forces

    T1[a] = T2[a]=T2[c] = T3[c]=T3[b] = T1[b],

contradicting the distinction of the two events of T1. This is a certificate consisting entirely of actual shared-event anchors and within-chart factorization fibres.

These quotients arise from honest local four-component grid data, not arbitrary transition maps. At singleton endpoint types take R_i with two witnesses, T_i with two witnesses, Q_i and S_i with one witness each, P_i=D_i, and N_i=T_i. Choose a bijection α_i:R_i×T_i→D_i whose fibres over T_i are the displayed pairs; take β_i the identity under unit identifications. Define θ_i using α_i^{-1}; this is an actual bijective whole matching and satisfies the grid equation exactly. Each local crossing therefore has a fully visible, valid realized middle component. Its observed whole tuples are the actual elements of D_i⊂W.

This smallest fixture uses trivial Q/S endpoints and is not offered as a physically rich example. The failure is not caused by triviality: tensor each chart with the SAME active skeleton from the four-component example in `../foundations/Four_Component_Cylinder_Examples.md`, and take W×V for its whole-event set. At any fixed skeleton event the displayed forced-identification chain still collapses two locally distinct hidden events. Each pair still glues by the prior sheet bijection times the identity on the skeleton. The active tensor factors must be kept as designated component occurrences; no claim is made that tensor padding itself proves a new higher-dimensional phenomenon.

Why this does not contradict anchored-loop triviality: no global component projection W→T is given. Each local projection is independently well-defined. The singleton overlaps determine consistent pairwise identifications, but their cycle cannot be induced by any one global projection. If such a global projection were supplied in advance, it would itself prove that the offending chain cannot occur. We are deciding its existence, not forgetting an already-given coherent whole anchor.

## 4. Nonunique witnesses and solution groupoids

The fixed-local-data quotient problem has discrete solutions up to equivalence, but local data need not have a unique realization. For each chart choose one representative of each isomorphism class in its local realization groupoid, with its actual automorphism group G_i. The local all-fibres classification in `../foundations/Crossing_Grid_All_Fibres_Classification.md` supplies these representatives: visible counts are bounded; doubly unexposed sectors may have arbitrary finite cardinality. Consequently (5) is a groupoid classification, not a finite enumeration over all local choices; the terminating finite algorithm above fixes the local realizations.

For a tuple of local representatives, let Adm be its finite set of admissible K. The product G=∏_i G_i acts on X, on derived exposure maps, and hence on Adm. It preserves actual input data, including α_i,β_i and θ_i. In particular each such local automorphism fixes π_i(w) for every exposed w, because π_i is extracted from those preserved factorization maps. The generated network realization groupoid is equivalent to the disjoint union over tuples of local isomorphism-class representatives of

    Adm // G.                                        (5)

**Proof.** Restriction of a global object gives a tuple of local realizations; transporting to representatives yields a K by Theorem 1. A different transport acts by G. Conversely a K constructs the global object, and local automorphisms carrying K to K′ induce exactly its global isomorphisms. Kernel equality and generatedness show that this correspondence is fully faithful and essentially surjective. ∎

Nontrivial stabilizers in (5) retain genuine witness symmetries. For example, if all whole exposures and all constraining parent contexts are empty but each of two charts has a two-element invisible event carrier at the same singleton boundary, admissible K are its perfect matchings. The S2×S2 action is transitive with diagonal S2 stabilizer: the result is the two-element sector of FinSet_iso, not a discarded multiplicity. Completely globally unobserved events are excluded by generatedness; adding them requires a separate extension analysis, particularly if operations can connect them to observed events.

## 5. Standard baseline and integrated results

The static core is finite equivalence-relation amalgamation with exact fibre coverage. This is not claimed to be a new general gluing mechanism. What is established here is the extraction of its constraints from actual crossing witnesses, the distinction between coherent local whole matchings and a missing GLOBAL component anchor, the arbitrary-interface-map exactness condition, and the classification retaining local symmetries.

The companion results complete the stated finite operational integration and retain its limits:

1. `../implementation/Finite_Acquisition_Circuits_and_Exact_Lifting.md` supplies permitted-circuit semantics. `Integrated_Finite_Network_Lifting.md` proves the simultaneous finite implementation criterion on reconstructed event classes; `../implementation/Maximal_Permitted_Interface_Equipment.md` identifies the certified interface class.
2. Section 6 supplies operational congruence and domain reflection; establishing its primitive operations in the physical model remains a model obligation.
3. `../examples/Cartesian_Partial_Whole_Holonomy.md` supplies the directly active endpoint-Cartesian example and unbounded cycle family. It is the principal structural example; the earlier degenerate fixture is introductory only.
4. Section 8 establishes simultaneous cartesian interface transport. General changes of chart families and refinement remain separate: arbitrary independent reindexing can change coverage and must not be asserted to preserve existence automatically.
5. The mathematical sources have independent AI proof review and bounded executable checks, not human peer review or proof-assistant verification. Standard mechanisms remain acknowledged and no novelty-priority claim is made.

## 6. Exact operational restriction, not just witness-set embedding

Here is a precise extension for deterministic partial operations. It applies when the local component carriers are states or records carrying operations specified by the model; it must not be silently imposed on arbitrary span witnesses.

Fix a finite many-sorted signature of unary operations (controlled successors, source/target maps, and record projections are examples). Give E and each E_i a finite partial algebra in this signature, with p_i a defined-operation-preserving homomorphism. Give each T_i a partial algebra and require e_i:T_i→E_i to preserve every defined operation. Form X and K sortwise. In addition to A1–A4 require:

* O1 (determinism/congruence): if x K y and f(x),f(y) are both defined locally, then f(x) K f(y).
* O2 (no imported local operation): if x∈T_i, f is defined at e_i(x) in E_i, and some y K x has f(y) defined in its chart, then f(x) is defined in T_i.

Here each local occurrence retains its chart tag. A1–A4 apply to every sort, so codomain elements of operations have their own exact coverage obligations.

### Theorem 2 (generated operational reconstruction)

There exists a global partial algebra T→E whose carrier and operation graph are generated by the local charts, whose pullbacks along p_i are exactly the given T_i as partial algebras, and whose actual event anchors agree, iff an admissible K satisfies O1–O2. The quotient is constructed by

    f_T([x])=[f(y)] if some y K x has a defined local f(y),

and f_T([x]) is undefined otherwise.

**Proof.** O1 makes the value independent of y. Since each e_i and p_i preserves defined operations, the quotient map to E does too. The pullback operation at (z,[x]) is defined exactly when f_Ei(z) and f_T([x]) are both defined. The local operation implies these two conditions. Conversely those conditions, plus A4 supplying the unique local x over z, imply local definedness by O2. Its value is the unique element required by the pullback, by O1 and the homomorphism property of e_i. Thus every h_i is an isomorphism of partial algebras, not merely a carrier bijection. Conversely exact pullbacks force O1 and O2, and generatedness forces exactly the displayed operation table. ∎

The theorem extends to finite-arity operations by replacing y K x with coordinatewise equivalence of tuples and requiring the witnessing tuple to lie in one chart. For O2 the entire tested input tuple must lie in one local chart, and the entire boundary tuple must enable the operation in that chart’s base algebra. This qualification prevents inventing operations on mixed-chart tuples. Nullary operations require separate simultaneous constant obligations, or can be encoded using a designated terminal input sort.

To decide the theorem, add the O1 equality implications and O2 forbidden-domain implications to the finite partition formula. One may close F under all forced O1 identifications before optional merging. A resulting local fibre collision is a short operation-and-anchor certificate. During optional coarsening the closure must be repeated; satisfying the original static constraints alone is not sufficient.

If every local domain is invariant under the same total whole operation and every π_i preserves it, forced anchor identifications are automatically congruence-closed. In that special regime O1 does not manufacture a new obstruction. Operational failures require genuinely different partial enabledness, noninvariant observations, or context-dependent operations which are being asked to arise from one context-independent component. Those assumptions must be established in the model rather than smuggled into the example.

The action-groupoid classification extends verbatim with local operation-preserving automorphisms. Completely unseen states or additional unseen operations are not classified: the generatedness restriction is substantive.

## 7. Distinguishing shared-component reconstruction from assembly of the whole

Theorem 1 reconstructs a common component and recovers every supplied LOCAL crossing factorization. It does not by itself construct a single global surrounding context, a factorization of the entire W, or a global θ. Arbitrary witness-selected D_i can fail to have the coverage/product structure required for such an assembly. In particular cardinality of W need not equal that of any proposed R;T. Calling Theorem 1 a full arbitrary-network assembly theorem would be incorrect.

Here is a sufficient concrete coverage condition that does reconstruct a global factorization, rather than assuming one.

### Proposition 3 (outer-boundary coverage glues the surrounding factorization)

Let fixed global spans R:A↝B and P:A↝C be given, and let subsets A_i cover A. Require R_i and P_i to be their actual cartesian restrictions to A_i (so every witness at a selected input is included). Let T_i:B↝C and α_i:R_i;T_i≅P_i be the local recovered maps, with their component boundary maps p_i=id_{B×C}. Suppose an admissible K supplies bijections k_i:T_i≅T. Additionally require that for every actual p∈P whose input lies in A_i∩A_j, the R-witness coordinates of α_i^{-1}(p) and α_j^{-1}(p) are literally equal. For this proposition augment F with the following directly computable parent-overlap anchors: identify the T_i-coordinate of α_i^{-1}(p) with the T_j-coordinate of α_j^{-1}(p) for every such shared p. Require K to contain these extra anchors. This is a derived constraint from the supplied parent factorizations, not an assumed global α. It is redundant if every parent p extends to a shared actual whole event with those same extraction coordinates, but must NOT be omitted when an empty Q or S hides p from W. The proof of Theorem 1 applies unchanged to this larger list of specified anchor equalities.

Then there is a unique span isomorphism α:R;T≅P inducing all α_i under the k_i.

**Proof.** Define α^{-1}(p) using any chart containing the input of p, and apply k_i to its T_i-coordinate. Both coordinates are independent of the chart by the stated R agreement and A1. This map preserves all endpoints. At each a∈A choose a chart containing a. The restriction to input a is a bijection because α_i and k_i are bijections and R_i,P_i include ALL witnesses there. These fibrewise bijections assemble into the desired global span isomorphism. Uniqueness follows from coverage. ∎

The dual statement glues the β-factorization when the right-hand parent and surrounding context are actual endpoint restrictions along a covering family and the unchanged context coordinates agree. If both sides glue and their supplied local whole matchings cover the whole and agree as actual maps on overlaps, the global θ equation follows pointwise from the local equations. Its coverage and agreement are real additional checks, not consequences of the component quotient alone.

This corollary uses ordinary cover gluing, explicitly, but identifies exactly which product/coverage data must supplement the shared-component criterion before claiming a whole-system reconstruction. An endpoint-cover obstruction can therefore be meaningful even though W is fixed: W may admit many factorizations, while no one of them extends the specific anchored local factorizations. Conversely, if a globally coherent factorization and its component anchors were already supplied, their restrictions cannot exhibit the proposed incompatibility.

## 8. Noninvertible simultaneous interface transport

A safe transport theorem must change the actual exposure data together with the interfaces; arbitrary independent replacement of charts has no such guarantee.

Assume every visible whole event w has the consistent global type τ_W(w) from (1). Let u:E′→E be any function. Define

    E_i′=E_i×_E E′,   T_i′=T_i×_E E′,
    W′=W×_E E′,       D_i′=D_i×_E E′.

For nonvisible W events their types may be supplied separately or they may be omitted from this construction. The new extraction is π_i′(w,e′)=(π_i(w),e′), and p_i′ is projection to E′.

### Proposition 4 (cartesian transport and its exact limitation)

Every admissible K induces an admissible K′ by

    (x,e′) K′ (y,f′) iff e′=f′ and x K y.

Its reconstructed component is canonically E′×_E(X/K). The forced relation F′ is exactly the corresponding copy of F at each e′. These identifications compose coherently under successive base changes, by literal tuple reassociation. No injectivity of u is required.

**Proof.** Every anchor step of F has constant global type and lifts at any fixed e′ over it; conversely every lifted step projects to the original step. This proves the assertion about F′. Type constancy and absence of local fibre collisions are immediate. At every new local lift (z,e′), A4 gives precisely the old unique representative over z, paired with e′. Hence K′ is admissible. Mapping [(x,e′)] to (e′,[x]) is a bijection over E′, with the asserted composition coherence. ∎

Not every new solution must descend: different e′ above the same e can choose different admissible partitions. In the static finite-set case a surjective u DOES reflect existence, because one may choose an e′ over each e and use that fibre's partition; constraints do not relate different global types. It need not reflect a specified solution or its uniqueness.

For Theorem 2 the same transport holds when E,E′ and E_i are partial algebras, u is a homomorphism, and all primed objects/operations are their actual pullbacks. The operation table constructed on the quotient is then the pullback of the old table: a defined old operation has a local witnessing occurrence, and it lifts exactly when the E′ operation exists. Therefore generatedness of operation graphs is preserved as well as carriers. Surjectivity of underlying carriers alone is NOT asserted to reflect operational existence, since selecting one lift independently at each type need not preserve operations. A homomorphic section is a sufficient reflection condition, by applying the transport theorem along the section.

This proposition is mathematical interface transport, not authorization to build an arbitrary physical adapter. Its physical interpretation requires the implementing sensor/gate language to realize u and any demanded witness-level selection.

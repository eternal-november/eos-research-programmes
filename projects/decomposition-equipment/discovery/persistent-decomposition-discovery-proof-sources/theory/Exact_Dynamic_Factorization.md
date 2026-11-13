# Exact dynamic factorization and detection of hidden cross-component correlations

## Plain-language abstract

A system can look decomposable in every available partial model while its actual transitions still couple the proposed components. The missing information is not always another state variable. It can be a correlation between two components' transitions, or the identity of the interface event on which they synchronized. This note gives exact tests for both problems.

First, it characterizes independent transition factorization through a specified interface, retaining the number and identity of actual execution records. Second, it characterizes precisely when a family of coarser views can detect every cross-component correlation. If the views fail that test, an explicit linear space describes correlations they can hide, and every nonzero direction supplies a family of false-positive decompositions. Finally, it distinguishes finding some new decomposition after an interface is forgotten from preserving the original decomposition witnesses. The resulting exact factorizations extend to paths of every length and to spatial substitution trees by explicit record bijections.

The matrix, linear-algebra, and finite-limit ingredients are standard. The claims here concern their combined, witness-sensitive application to decomposition discovery. They do not establish novelty priority or provide controller synthesis by themselves.

## 1 Finite witnessed open dynamics

A finite interface graph J has state set B, event set J_1, and source/target maps ∂⁻,∂⁺:J_1→B. Its event labels may include a control action, a sensor/handshake value, and an environment record. The timing of each field is supplied by the interface language. A post-action field must not be treated as a pre-action observation.

A finite witnessed system P over J is a finite directed multigraph (X,E,s,t) with maps b:X→B and λ:E→J_1 commuting with source and target. E consists of actual transition records; equal endpoints do not identify events. Control labels, when used, factor through a specified map J_1→A.

An ordered state cut is a pair of maps p:X→Z, q:X→Y, with boundary maps Z→B,Y→B, for which

    χ=(p,q):X ≅ Z×_B Y.                                      (1)

We permit empty fibres. Candidate cuts need not be supplied. In the GENERATED-STATE scope, both projections p and q are surjective; on finite X such cuts are represented by two equivalence relations, with boundary-constant classes, whose quotient-pair map is bijective onto the fibre product. This excludes extra factor states above a boundary where the opposite factor has no states. To classify those invisible state sectors too, supply finite factor-state bounds and enumerate the extra states and boundary maps directly rather than representing all factors by partitions of X. Fixed-cut Theorem 1 permits those states, but the partition-based discovery claim is generated-state only. Designated component occurrences, local-view anchors, state-size bounds, and allowed boundary maps filter these candidates. The finite partition mechanism is a standard discovery step, not a claim that arbitrary cuts are physically meaningful.

A persistent exact factorization of P at χ comprises finite graphs D on Z and F on Y, graph maps D→J,F→J, and an event bijection

    η:E ≅ D_1×_{J_1}F_1                                  (2)

commuting with source/target through χ. Thus P is isomorphic, as a witnessed graph, to the graph pullback D×_J F. Every matching component-event pair is a whole event, and each whole event has exactly one pair. No additional hidden scheduler may reject a matching pair. This is stronger than matching transition supports or accepting a nondeterministic projection of P.

The existence of an ontic component state p(x) does not imply that a controller can observe it. Conversely failure to observe p(x) does not prove that the component fails to exist.

## 2 Exact transition criterion

For j:b→b′ define row and column types

    R_j=Z_b×Z_b′,   C_j=Y_b×Y_b′.

Define the actual transition-multiplicity matrix

    M_j[(z,z′),(y,y′)]
       = |{e∈E: λ(e)=j, χ(s(e))=(z,y), χ(t(e))=(z′,y′)}|.    (3)

### Theorem 1 Exact factorization classification

For fixed χ and J, a persistent exact factorization exists precisely when, for every j, there are nonnegative integral vectors d_j on R_j and c_j on C_j such that

    M_j=d_j c_j^T.                                          (4)

Given such vectors, D has d_j(z,z′) distinct j-labelled events z→z′, and F has c_j(y,y′) such events y→y′. The remaining factorization data are the actual bijections in each block of (3) with the corresponding products of those records. Additional crossing-view anchors constrain these actual bijections; they are NOT implied by (4).

For a nonzero M_j, condition (4) is equivalent to all 2×2 minors vanishing. There are uniquely determined primitive nonnegative integral vectors p_j,q_j and g_j>0 with

    M_j=g_j p_j q_j^T,

where each vector has gcd of its nonzero coordinates equal to one. Every integral outer-product option is

    d_j=k p_j,  c_j=(g_j/k)q_j,  k | g_j.                   (5)

For M_j=0, the complete classification is d_j=0 or c_j=0, with the other vector arbitrary; if both row and column carriers are nonempty this includes unbounded invisible sectors. Generatedness or a hardware bound must be declared if a finite enumeration is desired. Empty index carriers obey the same product statement, and may leave arbitrary events on the other factor. Invisible records must not silently be discarded.

**Proof.** A factorization (2) partitions each source-target block into a product, proving (4). Conversely construct the component records with the prescribed cardinalities and choose a blockwise bijection; their disjoint union is η. Its incidence equations hold by construction.

For a nonzero rank-one M, select a nonzero column, divide by its coordinate gcd, and call the resulting primitive vector p. Every other column is a rational scalar multiple of p. Since p has integer coordinates with gcd one, Bezout's identity shows that scalar is an integer. Thus M=p v^T for an integral nonnegative vector v. Put g=gcd(v), q=v/g. In any other factorization d c^T=M, the same argument gives d=k p with k positive integral, and c=(g/k)q integral exactly when k divides g. Uniqueness and (5) follow. Finally an outer product is zero iff at least one vector is zero. ∎

The theorem describes semantic factors and actual identifications, not only one count factorization. Relabelling component records induces the usual action groupoid on the chosen bijections. A local chart family can be checked by composing its declared state/event view maps with η and requiring its exact factorization squares and actual shared-event anchors. Finite bounds make this remaining matching problem finite; no abstract compatibility oracle is needed.

## 3 When partial descriptions detect every correlation

This section fixes a candidate cut and one interface event j. Write R=R_j,C=C_j. A partial description independently coarsens the two transition-type sets by total maps

    α_i:R→R_i,   β_i:C→C_i.

Its count matrix is

    L_i(M)=A_i M B_i^T,                                    (6)

where A_i,B_i are the zero-one matrices of these maps. Every actual record is counted once. For a view induced by a state coarsening, α_i(z,z′)=(h_i(z),h_i(z′)); arbitrary α_i are only allowed if the declared interface/view language realizes them. The theorem holds for either class, but does not authorize new observations.

Let

    V={D∈Q^{R×C}: D1_C=0 and 1_R^T D=0}.                  (7)

This is the space of changes to joint transition counts that leave both component marginals fixed. It has dimension (|R|−1)(|C|−1) when both sets are nonempty. The explicit basis, after choosing r0,c0, consists of

    E_rc−E_r,c0−E_r0,c+E_r0,c0.

Call H=V∩⋂_i ker L_i the hidden-correlation space of this view family.

### Theorem 2 Universal reflection of independent factorization

For the fixed row/column view maps, the following are equivalent:

1. For every nonnegative integral transition matrix M, if every observed L_i(M) has rank at most one, then M has rank at most one.
2. H=0.

This gives a finite rational rank test on the declared observation maps, not a search over systems. If H≠0, every nonzero rational D∈H can be scaled to a nonzero integral matrix, and for every sufficiently large positive integer k,

    M_k=k·1_R 1_C^T+D                                    (8)

is a strictly positive integral transition matrix that is not rank one, although every L_i(M_k) equals the corresponding observation of the independent matrix k·1_R1_C^T.

**Proof.** Empty R or C makes all matrices zero and both assertions trivial. Let M≥0 have total N. If N=0, M=0. Otherwise let u=M1, v=1^T M and set Δ=NM−uv. Its row and column sums vanish. A nonnegative rank-at-most-one matrix with total N is exactly the product of its marginals divided by N. Because α_i and β_i are total maps, L_i(M) has the same total N and its marginals are A_i u and v B_i^T. Hence rank≤1 of every L_i(M) gives L_i(Δ)=0. If H=0, Δ=0, so M has rank one.

Conversely choose nonzero integral D∈H. Choose k exceeding every |D_rc|; (8) is positive. Its marginals are the same as the uniform matrix. A rank-one matrix is determined by those marginals and total, so M_k could have rank one only if D=0. Yet L_i(D)=0, so every observation equals that of the uniform independent matrix and has rank one. The entries of M_k are realized literally as distinct events of a finite graph with the prescribed state cut and j label. ∎

The theorem distinguishes identifying a joint transition table from detecting correlations: injectivity on all matrices is stronger than required. Injectivity on the zero-marginal interaction space is exact. The theorem only reflects existence of some count-level independent factorization. Preserving specified component-event identities still requires the anchor checks of Theorem 1 and the provenance comparison below.

### Corollary 2.1 One independently coarsened view

If |R|,|C|≥2, a single view reflects independence for all matrices iff both α and β are injective. If either source index set has size at most one, all matrices already have rank at most one.

**Proof.** Injective maps lose no matrix entries. If α identifies r1≠r2, take D=(e_r1−e_r2)(e_c1−e_c2)^T; it is a nonzero element of H. The β case is symmetric. ∎

### Theorem 3 Exact restriction-view boundary

Instead suppose each view is the literal submatrix M|_{R_i×C_i}, where R_i⊆R,C_i⊆C. Local rank≤1 reflects global rank≤1 for all nonnegative integral matrices iff every choice of two distinct rows and two distinct columns lies together in some view.

**Proof.** Sufficiency follows because every 2×2 minor is tested. If a rectangle {r1,r2}×{c1,c2} is not covered, take M supported only at (r1,c1),(r2,c2), with value one at both. M has rank two. Any view containing both entries would contain the missing rectangle; consequently each view contains at most one nonzero entry and has rank≤1. ∎

These are different view semantics: (6) aggregates every record, while Theorem 3 restricts domains and omits records. They must not be interchanged.

## 4 Preserving original witnesses under interface changes

Let q:J_1→Jbar_1 be a coarsening preserving the declared state-interface endpoints, and retain the original component record sets D_1,F_1. The old whole record set is D_1×_J1 F_1. There is a canonical inclusion

    ι:D_1×_J1 F_1 → D_1×_Jbar1 F_1.                       (9)

### Theorem 4 Exact synchronization descent

The original factorization descends unchanged through q iff every pair (d,f) with qλ_D(d)=qλ_F(f) already has λ_D(d)=λ_F(f). Equivalently, in each coarse interface fibre, either one component has no records, or both components' sets of active fine labels are the same singleton.

The failure certificate is an actual pair of records that match after coarsening but did not match before. It is a new spurious whole transition, not merely a change in an aggregate coefficient.

**Proof.** The map (9) is injective. It is surjective exactly when every coarse matching pair was already a fine matching pair. For one coarse fibre let S,T be the active fine-label sets. The condition is S×T⊆{(j,j)}. If both are nonempty, this is equivalent to S=T={j} for some j. ∎

More generally let r:D_1→Dbar_1 and s:F_1→Fbar_1 be prescribed event maps compatible with q and their state maps. The canonical map

    κ:D_1×_J1 F_1 → Dbar_1×_Jbar1 Fbar_1

is bijective iff every compatible coarse record pair (dbar,fbar) satisfies

    Σ_j |r^{-1}(dbar)∩D_j| · |s^{-1}(fbar)∩F_j| = 1.       (10)

The sum counts the exact preimage of that pair. The state comparison must separately be bijective for a whole dynamic isomorphism. If (10) is merely positive, the comparison is surjective and may lose records; if it is at most one, it is injective and may omit coarse combinations. Quotienting the whole by ker κ can remove a many-to-one multiplicity problem, but cannot supply a missing coarse record pair; it changes the retained information and must be reported as a different reconstruction problem.

### Example Count-level refactorization without witness descent

Let J={0,1}. Each D_j and F_j has exactly one event, all at singleton component state types. The original whole has two records (d0,f0),(d1,f1). Forget J to a singleton. Its aggregate 1×1 count matrix is [2], which has new factorization 2×1 or 1×2. Nevertheless preserving the old D and F projections demands 2×2=4 records; the off-diagonal pairs were not actual whole events. Thus a new factorization exists after forgetting the interface, but the supplied witnessed factorization does not descend. This distinction persists if each event is a self-loop and paths are considered.

## 5 Temporal and spatial coherence

Write Path_n(G) for the actual length-n graph paths, retaining their n ordered event records and n+1 states. Path_0(G) is its state set.

### Theorem 5 All-length interchange

Given (1)–(2), for every n≥0 there is a bijection

    Path_n(P) ≅ Path_n(D) ×_{Path_n(J)} Path_n(F).          (11)

It commutes with deleting an initial/final segment, concatenation of composable paths, and identities. For any finite spatial substitution tree of exact graph-pullback factorizations, the iterated version of (11) is independent of spatial bracketing and of the order in which temporal paths are assembled and component occurrences are expanded.

**Proof.** A P path maps eventwise through η and statewise through χ. Incidence compatibility makes its two component event sequences paths, and their J paths agree. Conversely a pair of component paths with equal J path supplies at each step a unique P event by η^{-1}; its target and the next source coincide because χ is injective and both component coordinates coincide. Thus they concatenate into a unique P path. At n=0 use χ. All stated maps are restrictions or concatenations of the same labelled tuples, so the diagrams commute literally after the specified tuple-reassociation bijections.

For a spatial tree, recursively apply the same construction at the marked occurrence. Every leaf occurrence has a separate event coordinate; repeated types do not identify occurrences. Both orders of construction produce the same tuple of leaf paths and matching interface paths. Unary identities and zero-length temporal paths follow from identity tuples. A nullary spatial component requires an explicitly specified unit object/interface and is not inferred from zero temporal length. ∎

This is a finite-limit/path argument, not a new theorem about arbitrary asynchronous systems. If a view sends a transition to an empty path, it is no longer a same-tick graph map and (11) cannot be invoked without a separate synchronization theorem.

### Corollary 5.1 Exact interface transport

For a graph map h:J′→J, simultaneous pullback of the entire witnessed factorization gives

    h^*P ≅ h^*D ×_{J′} h^*F,

and its path comparisons commute with (11). Composition of interface pullbacks and spatial refinements commutes by the same tuple maps. A physical implementation must separately compile h; categorical pullback does not make an unavailable sensor or inverse-image chooser available.

This preservation result does NOT imply reflection. A restricted interface can remove the events exposing a correlation, and a noninjective duplication can support local choices that do not descend. Theorem 2, Theorem 3, or the record criterion (10) must be used for the relevant declared view semantics.

### Corollary 5.2 Discovery and refinement

The groupoid of hierarchical exact factorizations maps to the groupoid of coarse factorizations by grouping leaf records. Fix the marked occurrence, the coarse factorization, and the identifications of its component and context with those in each refinement. The STRICT fibre with those identifications fixed is the groupoid of exact factorizations of the selected component with the prescribed interfaces and local anchors. If identifications are allowed to vary, use the corresponding homotopy fibre instead; ignoring them would lose the coarse automorphism action. Theorem 1 computes this fibre on finite bounded data. It can be empty: temporal coherence of a coarse decomposition does not create an independent finer decomposition. When the fibre is nonempty, its temporal comparison is (11) at the marked occurrence, and arbitrary finite sequences of refinements commute with path formation.

This states the comparison actually proved, not an equivalence between all coarse and refined discovery spaces.

## 6 Controlled interpretation boundary

An exact factorization alone does not make every component action executable in the whole. The context can have no matching event at a given hidden state. Controller transfer therefore needs enabled-action/nonblocking reflection, in addition to a controller whose chosen action depends only on permitted pre-action observation history. Safety and progress must be quantified over all admitted environment records. If the controller deliberately restricts the plant, distinguish factorization of the full plant from factorization only of the closed-loop reachable subgraph.

A correct control bridge can import a suitable feedback-refinement theorem after proving its hypotheses from (1)–(2) and the enabledness condition. It may not treat λ(e), which can include post-action information, as a pre-action sensor observation.

## 7 Scope and baseline ledger

The new claims in this note are mathematical derivations for the explicitly declared finite synchronous model; they are not Lean verified. The rank-one classification, linear correlation-detection argument, and graph pullback/path construction use standard algebra. Exact source comparisons and independent checks remain required before claiming novelty or acceptance.

The relation to the earlier snapshot reconstruction is precise: earlier carrier/operation gluing can reconstruct consistent local states and transition records, but does not by itself show that every matching pair of reconstructed component/context transitions is an actual whole transition. Equations (3)–(4) test that independence, (7) tests whether the partial views can conceal its failure, and (9)–(10) test whether interface coarsening preserves the actual synchronization witnesses. These are separate obligations.

## 8 Quantitative view adequacy and spatial refinement

### Theorem 6 Interaction-span criterion and lower bound

Put U_R={u∈Q^R:Σ_ru_r=0}, and similarly U_C. Then V=U_R⊗U_C. Total aggregation maps send these spaces to their coarse zero-sum spaces. Let

    Ahat_i:U_R→U_Ri,   Bhat_i:U_C→U_Ci

be the restricted maps. Universal reflection in Theorem 2 is equivalent to

    span_i (im Ahat_i^* ⊗ im Bhat_i^*) = V^*.             (12)

In particular it requires

    Σ_i (|im α_i|−1)(|im β_i|−1)
        ≥ (|R|−1)(|C|−1),                               (13)

with empty-carrier cases treated separately as in Theorem 2. This is only a necessary dimension bound; overlaps between the tensor subspaces can make it insufficient.

**Proof.** The joint map on V is injective iff its dual is surjective. The dual of Ahat_i⊗Bhat_i has image im Ahat_i^*⊗im Bhat_i^*. Its rank is the product of the restricted ranks, which equal |im α_i|−1 and |im β_i|−1 for nonempty source sets. Summing ranks gives (13). ∎

Thus separating every pair of component transition types is not in general enough: the views must distinguish their interaction directions. The basis in (7) constructs the exact test without enumerating possible plants.

### A genuinely proper state-induced positive family

Let component state sets Z,Y each have at least four elements, and let the interface state/event be a singleton, so R=Z×Z,C=Y×Y. For every pair of distinct states of Z take the quotient that merges just that pair; do likewise for Y. Use ALL combinations of one such Z quotient and one such Y quotient as chart views. Every chart genuinely forgets state information on both sides, and every transition-type map is induced by its state quotient.

These views jointly determine every entry of M, and therefore reflect independence. To recover a prescribed transition type (z,z′), choose the merged pair disjoint from {z,z′}. Then both z and z′ are singleton blocks, and that observed transition-type entry has exactly one preimage. For z=z′ there are still two other states to merge. Do the same for (y,y′); the corresponding chart isolates the desired joint entry. This proves actual finite graph realizability of a useful proper-view family; it does not grant those views physically unless the chosen observation language provides them.

### A state-induced negative family despite state separation

On Z={0,1,2}, define a vector l on ordered transition types by

    l_01=l_12=l_20=1,  l_10=l_21=l_02=−1,
    l_00=l_11=l_22=0.

Every proper state quotient p:Z→Zbar kills l under p×p. For a quotient with a singleton and a merged pair, the two cross-block contributions cancel in each direction and the within-block contributions cancel; the constant quotient also kills l. Nevertheless the family of all two-block quotients separates every pair of states. Choose any nonzero zero-sum v on C and put D=l v^T. Then D is a nonzero hidden-correlation direction for every family whose Z views are all proper state quotients. Formula (8) produces actual positive transition systems with locally independent counts but a globally coupled component/context pair.

This example concerns transition-record counts, not state-identifiability. Having enough views to tell states apart does not mean they retain enough joint transition information to validate a decomposition.

### Theorem 7 Nodewise discovery on arbitrary spatial trees

Fix a finite typed spatial tree. Every internal node specifies a shared state/event interface, a Cartesian state cut of that node's proposed system, and its actual local crossing constraints. Then a witnessed factorization along the whole tree exists iff each internal-node matrix satisfies Theorem 1 AND the chosen event bijections satisfy the actual parent/child and crossing-anchor equations. Recursively substituting the accepted node factorizations constructs the whole tree factorization. It retains every occurrence separately.

If each node's count views satisfy (12), exact independent count factorization at that node is reflected by its declared partial views. If (12) fails at any node, the nonzero kernel construction gives a family of false-positive count factorizations there; inserting independent exact contexts at the other nodes carries the failure into the full tree. The all-length comparison of Theorem 5 commutes with every such spatial substitution.

**Proof.** Necessity follows by restriction of a tree factorization to each node. For sufficiency, build the factorization from the leaves upwards by substituting the exact record bijections at marked occurrences. The anchor equations ensure that one record identification, not two unrelated choices, is used wherever a crossing chart refers to that occurrence. Associativity is the tuple proof in Theorem 5. The reflection statement is Theorem 2 at each node. For the negative construction, choose the obstructed node and tensor it with nonempty independent contexts; a purported refined factorization would restrict to its impossible node factorization. ∎

The negative insertion construction is existential in surrounding nonempty independent contexts and anchors chosen compatibly with it. It does not assert a counterexample for every preassigned anchored tree or restricted hardware class; those require the realizability check of Section 9.

The criterion is a finite schema for any supplied tree, not a test limited to a preset tree depth. It still requires local state cuts/interfaces and derived crossing equations at every internal node; it is not a theorem that arbitrary desired refinements exist.

### Concrete coarse-success and fine-failure

Let whole states be triples (a,b,c) of bits. A transition independently chooses e,f∈{0,1} and sets

    a′=e, b′=e, c′=f.

There is one actual record for each source triple and (e,f). The coarse cut Z=(a,b), Y=c is an exact dynamic product: the first component performs a correlated joint reset and the second performs an independent reset. It works for every path length.

Refine the first occurrence into components a and b through a trivial interface. Its matrix, indexed by (a,a′) and (b,b′), has entries 1 when a′=b′ and 0 otherwise, so it has rank two. That finer cut fails, although the coarse factorization is exact. The partial views keeping (a,c) or (b,c) both have independent transition products and lose this correlation. A cut probe retaining (a,b) while forgetting c detects it; this is a proper view of the whole. Making the reset value e an actually permitted synchronization event yields instead an exact refined product conditioned on e. Detecting the missing correlation and providing a lawful interface for it are different repairs.

This example does not assert that the two original views were universally adequate for every coarse candidate. It shows a proved coarse factorization whose proposed finer cut needs a new interaction test and whose defect is missed by those specific proper views. Universal adequacy must be checked by (12) for each proposed node.

## 9 Qualifications for universal reflection

The necessity direction in Theorem 2 quantifies over ALL finite witnessed transition multiplicities on the stated Cartesian row/column carriers. It relies on realizing the positive family (8). If a separate application imposes structural zeros, fixed total multiplicities, deterministic updates, or a fixed hardware resource bound, that family may not belong to its model class. Then H=0 is still sufficient for reflection, but H≠0 alone is not a counterexample in the restricted class. One must exhibit a permitted kernel perturbation or derive the appropriate restricted criterion. The deterministic reversible subclass therefore needs its separate transport theorem; it is not covered by the necessity counterfamily automatically.


## 10 What is and is not discovered from partial descriptions

Theorem 2 can certify count-level existence without reconstructing the full joint count matrix: if the view family is universally adequate and all observed matrices have rank at most one, the unknown actual joint matrix must also have rank at most one. This assertion presupposes that the observations are actual aggregations of one underlying plant through the stated maps. It does not infer a plant from unrelated tables.

Actual factorization maps η require access to the whole event records or equivalent retained record identifications. Counts alone cannot recover which execution in one chart is the same execution in another. The state-cut search in Section 1 also uses X or supplied local state cuts with enough actual shared-state anchors to reconstruct their candidate quotient maps. No theorem here promises cheaper search than full-state enumeration or identifies a real system from measurement readouts.

For a concrete discovery procedure: generate a finite candidate list of (state cut, permitted interface) from the whole finite model and/or compatible local state-cut candidates; use the reflection criterion to screen its count obligations from partial views where appropriate; use Theorem 1 and the actual anchors to reconstruct candidate component records; then run the staged implementation/control checks. The procedure is complete for its declared bounded/generated candidate class, not for arbitrary unavailable physical interfaces or unbounded hidden state.

The witness-sensitive interface theorem shows why records are not optional decoration: two count-level factors may exist while no factorization preserving the original component projections exists. Theorem 4 and (10) decide precisely that different question.

## 11 Explicit bounded discovery problem and theorem

This is a precise integrated formulation. It uses total same-clock abstraction maps. A partial-domain cover or a map that deletes time steps requires its own domain/coverage specification and is not silently included.

### 11.1 Input

1. A finite actual plant P=(X,E) over a declared interface graph J. More generally choose J from a finite list of allowed interface presentations with actual maps P→J. These are semantically available candidates; physical compilation is checked separately.
2. For each view i, a finite graph P_i over J_i, an actual graph map q_i:P→P_i, and an interface graph map ψ_i:J→J_i. The map q_i may identify states/events, but must satisfy the interface square. A view is a supplied model map, not inferred from readout data.
3. For each i, a finite list of local candidate decompositions

       χ_i:X_i≅Z_i×_{B_i}Y_i,
       η_i:E_i≅D_i×_{J_i}F_i,

   including their actual state/event bijections. Such lists can themselves be generated from P_i by Theorem 1 with stated bounds; they are not required to contain a known compatible global candidate. The lists may contain zero, one, or multiple candidates.
4. A marked proposed subsystem occurrence, nominal state/interface types, and finite bounds on global component states and events. In the generated-state branch the state candidates may be enumerated as partitions of X; the general bounded branch includes invisible state sectors directly. The global complement is also bounded. Bounds cover invisible event sectors of zero matrices.
5. Optional typed component comparison maps prescribed by the view language. If not prescribed, they are finite unknowns subject to the equations below and all declared operational restrictions. If a view is supposed to be a cartesian interface restriction rather than an arbitrary abstraction, that is an additional explicit pullback-bijection test, not inferred from commutation.

### 11.2 Output and explicit crossing constraints

An output is a global factorization (χ,η,D,F), one chosen local candidate for every i, and graph maps

    r_i:D→D_i,   s_i:F→F_i

over ψ_i, respecting the designated subsystem occurrence and nominal types. Their state maps are written r_i^0:Z→Z_i, s_i^0:Y→Y_i, and event maps r_i^1,s_i^1. They must satisfy, for EVERY actual state x and event e,

    χ_i(q_i^0(x))=(r_i^0(p(x)),s_i^0(q(x))),              (14)
    η_i(q_i^1(e))=(r_i^1(pr_D η(e)),s_i^1(pr_F η(e))).     (15)

Here q in p,q denotes the state cut projection; q_i is the named view map. These equations should be implemented with distinct variable names to avoid ambiguity.

Graph-map conditions are checked separately, for example

    source_Di(r_i^1(d))=r_i^0(source_D(d)),
    target_Di(r_i^1(d))=r_i^0(target_D(d)),
    label_Di(r_i^1(d))=ψ_i^1(label_D(d)),                 (16)

and the corresponding F equations. If two views have a supplied overlap comparison, impose its literal state/event square on r_i and s_i. When the same actual event occurs in multiple views, (15) uses ONE global d and ONE global f, so their local extracted records cannot be matched independently. These are the concrete anchor constraints, not an assumption that the local candidates descend.

A declared cartesian component view is tested by requiring its comparison

    D → J×_{J_i}D_i

to be bijective on BOTH states and events; the comparison is explicitly d↦(label_D(d),r_i(d)). This uses the orientation ψ_i:J→J_i fixed above. A view with the opposite restriction orientation is a different input diagram, not silently included. No blanket cartesianness follows from (14)–(16).

### Theorem 8 Bounded discovered persistent factorization

There is a terminating, sound-and-complete construction of the outputs above, up to the specified state/event relabellings, on the declared finite bounds. It does not assume a global subsystem, compatible factorization maps, or a common refinement.

**Construction.**

1. Enumerate the permitted interface choices and global state cuts (1), using the generated-state or fully bounded branch as declared. Enumerate one local candidate from each finite list.
2. Enumerate component state comparison maps r_i^0,s_i^0 and reject violations of (14) and the nominal/boundary conditions.
3. Form the matrices (3). On nonzero blocks use the divisor classification (5), rather than arbitrary count search. On zero blocks enumerate the separately bounded invisible sectors. Reject count choices exceeding bounds. Where the view matrices really are the aggregation matrices of Section 3, Theorem 2 may screen or certify this step from those views; otherwise do not apply it.
4. Construct named component event representatives with those counts. Enumerate actual block bijections η of (2) and component event maps r_i^1,s_i^1. Check (15)–(16), every supplied overlap square, and any declared cartesian comparison bijections. These are explicit finite equations on actual records.
5. Quotient only by the declared component isomorphisms preserving χ,η, all view comparisons, and named physical records when present. Retain stabilizers if the intended output is a groupoid. A strict-output convention may instead keep names; do not claim that discarding all symmetries is equivalent.

**Soundness.** Steps 1 and 3–4 give a graph-pullback factorization by Theorem 1. Equations (14)–(16) show it induces every selected local candidate through the actual model maps. Theorem 5 supplies path-level persistence and occurrence-wise spatial substitution, not a bounded trace extrapolation.

**Completeness.** Any output within the declared bounds determines an enumerated state cut and local-candidate tuple. Its component transition counts satisfy (4), hence are included in (5) or the bounded zero case. Choose representative names for its records. Its actual η and r_i,s_i then occur in the finite map enumeration and satisfy every tested equation. Thus it is obtained up to the allowed isomorphism. Conversely two accepted named outputs represent the same object exactly when the specified finite isomorphism equations hold. ∎

This is a completeness theorem for the declared semantic problem, not an efficiency claim. The substantive additional structure beyond finite enumeration is the explicit factor-multiplicity classification, sharp observation-reflection test, exact synchronization descent criterion, and all-path/refinement compatibility. The state search can still be large.

### 11.3 Physical and controlled lifting

An output of Theorem 8 is a semantic persistent subsystem. The companion staged implementation/control construction must then produce one repeated stateful device and the actual state/pre-action/post-action record comparisons. For each admitted action at a local pre-state z and each possible compatible context state y, the sets of enabled interface events must intersect; otherwise a local action is blocked in the actual plant. Controller choices use only the permitted pre-action observation history. The graph factorization equations do not waive these requirements.

The bounded complete search becomes a complete implemented-controlled search only after physical state/event bounds, staged primitive compilation, controller memory bounds, and the exact observation/record comparisons are supplied. No assertion about arbitrary controllers follows from the structural theorem alone.

### 11.4 Relation to the earlier calculus

The spatial structure here is a synchronous graph-pullback model with explicitly marked component occurrences and exact witness maps. Its substitution theorem is a model-level result. It is not, by itself, the original planar presented calculus's free/universal equipment theorem, nor an authorization to add arbitrary parallel wiring to that syntax. An interpretation and preservation comparison with the original calculus remains an integration obligation.

### 11.5 Aggregation is not unweighted event quotient

In (6), every original event is counted once after its row/column TYPE is coarsened. This is realized by keeping the actual event carrier and coarsening its endpoints, or by retaining pushforward multiplicity weights in a quotient view. If q_i identifies several actual events and the observed matrix counts only distinct quotient events with weight one, its matrix need not equal A_i M B_i^T. Theorem 2 does not apply to that matrix without a new proof. Equations (14)–(16), in contrast, explicitly handle the declared event map q_i. Count reflection and actual record-map compatibility must be checked under their respective semantics.


### 11.6 Separate summaries versus aligned execution records

The hidden-correlation space H characterizes what can be concealed from the family of SEPARATE aggregated matrices (6), hence from checking independence in each view individually. It is not a theorem that the full jointly aligned record-level views contain no such information. If the view maps jointly distinguish states and the identity of each actual event is retained across views, one can sometimes reconstruct its full endpoints and hence the original joint table even when H is nonzero. The three-state proper-quotient example is such a warning: state separation plus event alignment may recover information that the separate histograms discard.

Thus there are two different recovery resources: sufficient count observations (H=0), or sufficient cross-view record correspondences (the actual anchors in (15), potentially enough to reconstruct the whole table). Both can matter, and neither may be substituted for the other without proof. The counterfamilies (8) have identical separate count observations; they are not claimed indistinguishable under every possible aligned-event observation.

### Proposition 9 Aligned witnesses can recover what separate summaries lose

Suppose the whole state carrier X is known and its supplied view-state maps q_i^0:X→X_i are jointly injective. Suppose each actual whole event e has a retained common identifier across the views, and those views report q_i^0(s(e)) and q_i^0(t(e)), with its actual interface/control label. Then these aligned observations determine the entire actual graph P, including parallel-event multiplicity, and hence every candidate cut matrix (3).

**Proof.** The tuple of viewed source states has at most one preimage in X, and has one because the views are actual maps of P. This reconstructs s(e); the same argument reconstructs t(e). Event identifiers retain the carrier E and distinguish parallel records. Repeat for each event. ∎

The proposition remains valid when the separate count-observation kernel H is nonzero. It requires actual cross-view record correspondence and a known state interpretation; neither is present in a list of unrelated histograms. Theorem 8 exploits exactly this stronger kind of evidence when available through (15), rather than demanding that all recovery pass through count summaries.

## 12 Temporal-resolution discovery is a different comparison

Theorem 5 starts with an exact factorization of the primitive transition graph and extends it to every path length. Its converse is false: factoring a graph whose events are length-m paths need not supply a factorization respecting the internal time cuts of those paths. The companion `../examples/Temporal_Cycle_Decomposition_Discovery.md` supplies an exact finite classification of this failure over a fixed cyclic context: an unknown autonomous d-state factor exists at primitive time exactly when the loop permutation H is conjugate to an m-th power in Sym(d). The even-cycle binary odd-twist family passes every proper edge restriction and has a coarse m-step factor but no such primitive-time factor, even with all path records retained.

This is not explained by forgetting event multiplicities. It is failure of a discovered factorization to respect temporal subdivision. That note also gives a positive reflection theorem: for a reversible whole, product factorizations of two coprime time samples under ONE anchored state cut imply a product factorization of the primitive update. Separately discovered incompatible cuts do not satisfy the hypothesis. The distinction is central: path formation preserves an already exact spatial factorization, but decomposition discovery need not commute with taking a coarser time scale.

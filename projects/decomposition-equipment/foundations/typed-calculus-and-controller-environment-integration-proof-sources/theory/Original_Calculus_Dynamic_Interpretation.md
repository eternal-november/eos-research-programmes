# Interpreting the original typed calculus in finite dynamic systems

## Plain language abstract

The original calculus can describe how an actual execution of a whole determines executions of its pieces. This does not mean that every imaginable combination of piece executions is possible, or that the whole can be recovered from them. We construct that interpretation without discarding the nonreconstructive cases. An additional, checkable exactness condition identifies precisely the decompositions that do reconstruct every state and every execution record.

The interpretation uses the original typed trees, declared equations and occurrence-indexed refinement arrows, rather than replacing them with a new decomposition language. It explains why expanding a particular component commutes with following the system through time. It also exposes a limitation: changing an interface can create new combinations or introduce unresolved choices of interface witnesses. A valid decomposition map survives some changes for which exact reconstruction does not. We give the comparison map that must be tested, including empty decompositions.

This is a mathematical bridge to the existing finite synchronous model. It is not a construction of the full universal virtual equipment, a claim that every historical example has a dynamic interpretation, or a physical implementation theorem. Physical action and observation timing must be retained separately; an execution label is not automatically a sensor available to the controller.

## 1 Exact source contract

The source archive is `Witnessed decompositions source and contract.zip`, rooted at `witnessed_decompositions/`. The relevant existing definitions are:

* `WitnessedDecompositions/Core.lean`: `Component`, `Path.Slot`, `Path.componentAt`, `Path.expand`, `Signature`. Interfaces are vertices of a fixed quiver; components are edges. Generator input paths have exactly the output's outer endpoints.
* `Calculus.lean`: `CalcData` and `Calc`. Operations have actual ordered profiles, identity operations and occurrence-wise substitution satisfying unit and associativity equalities. `Calc.Hom` preserves the complete profile, identities and substitution.
* `FreeExtension.lean`: `Signature.Assignment`, `Tree.interpretOperation`, `Tree.extend`, `Tree.homEquiv`. These construct the unique strict map from the existing free calculus for any valid target `Calc` and any typed generator assignment.
* `PresentedCalculus.lean`: `Presentation.Model`, `Presentation.extend`, `Presentation.projection_extend`. Descent requires equality of interpreted declared parallel equations; the quotient is the least declared congruence, not the kernel of a chosen model.
* `SemanticRefinement.lean`: `SemanticRefinement.Arrow`, `mapArrow`, `functor`, `mapArrow_injective`. An arrow retains one replacement operation per source-profile occurrence and an equation saying their substitution is the target operation.
* `RawRefinement.lean`: `graftLeafEquiv`, `graftLeaf_assoc`, `profileGraftLeafEquiv`, `profileSubstitutionEquiv_compose`. These identify nested occurrence positions with the flattened positions used below.

The source is generic in `Signature S` and equations `E`. Therefore this result gives an interpretation scheme and an actual target calculus, not an automatic assignment to every generator in every example previously studied. A particular presentation requires its generator tables and equation checks. The fixture application is such an instance. The historical graph-cut presentation is not silently declared dynamically interpreted.

## 2 Finite graphs and typed component assignments

A finite synchronous graph G consists of finite sets G0 of states and G1 of actual event records with source and target maps s,t:G1→G0. A graph map is a pair of functions commuting with s,t. Parallel events remain distinct. Empty sets are allowed.

Fix the SAME syntactic quiver V as the original calculus. Assign a finite graph B_v to each interface vertex v. Assign to each component edge c:a→b a finite graph W_c and two graph maps

    B_a ←ℓ_c— W_c —r_c→ B_b.

These are semantic boundary maps. The syntactic color c remains retained even when two colors have the same assigned graph and boundary maps.

For a typed path p=(c1,...,cn), define P(p) to be its flat compatible-tuple graph: for n>0 its k-sort, k=0,1, consists of tuples (w1,...,wn), with wi∈(W_ci)_k and r_ci(wi)=ℓ_c(i+1)(w(i+1)). Its outer maps are ℓ_c1 and r_cn. Source and target act coordinatewise. For the empty path at v, P(∅_v)=B_v with both boundary maps identity. For a singleton identify P((c)) with W_c by the canonical singleton bijection.

The empty convention is essential: a nullary witness out of W_c exists only when c is a loop at v and ℓ_c=r_c. It is then the unique map to B_v equal to those legs. It is exact only when that map is a graph isomorphism. A spatial nullary witness is NOT a length-zero execution, and a scalar with hidden state or multiple records need not be exact.

## 3 The dynamic target calculus

Define the operations at output c:a→b as pairs (p,w), where p is an original syntactic path a→b and

    w:W_c → P(p)

is a graph map commuting with both outer boundary maps. Distinct maps are distinct operations even if they have equal image, the same transition counts, or the same traces. This is the target calculus Dyn(B,W).

Given a:(p,w) and a family f_i:(q_i,u_i), one for EACH i∈Path.Slot(p), define its substitution by

    W_c --w--> P(p) --expand(u_i)--> P(expand(p,q)).

For a nonempty slot q_i, expand applies u_i to the ith coordinate and retains its ordered new coordinates. For an empty q_i, u_i returns the interface coordinate and enforces equality of the two exposed boundary values; the absent edge coordinates are removed. If every q_i is empty, the common boundary value is retained as the value in P(∅), not discarded into a singleton. Empty outer profiles substitute only the empty family and leave w unchanged.

**Theorem 1.** Dyn(B,W) satisfies the original `Calc` axioms, including arbitrary nullary branches and repeated colors.

**Proof.** For every replacement family, adjoining the internal and external boundary values to the tuples makes expansion simply flattening a sequence of typed tuples; empty subtuples carry their common boundary value. The boundary equalities for u_i make adjacent new coordinates compatible. The same equalities ensure the outer maps remain those of W_c. Source and target commute with expansion because each u_i is a graph map.

Identity at c is the identity map W_c→P((c)). Substitution of identities leaves each coordinate unchanged. Substitution into identity applies the supplied map. At three levels, both bracketings send any state or event x to precisely the list of coordinates indexed by (i,j,k), in that order, obtained by applying the same three maps. Empty lists enforce the same boundary equalities; if all lists vanish both results retain the same outer boundary value. The original `Path.expand_assoc` is exactly the indexing transport between these lists, and `graftLeaf_assoc` retains all three occurrence coordinates. Equality follows at both graph sorts by function extensionality. Equivalently, for a nonempty profile represent w as its profile-indexed family of coordinate graph maps W_c→W_ci satisfying adjacency and outer-boundary equations. Substitution is literal coordinate-function composition indexed by original Path.Slot expansion; the source transports are exactly those in Calc.subst_assoc. The nullary map is unique when it exists. This supplies strict operation equality without treating nested categorical pullback carriers as literally equal. These are operation equalities, not merely equalities of profiles. ∎

**Theorem 2.** Every original typed generator assignment g↦w_g into Dyn(B,W) has a unique original strict calculus interpretation

    Tree.freeCalc S → Dyn(B,W).

It descends through the original presentation by E iff every declared equation has equal interpreted graph maps in its common profile. The descended map induces the existing occurrence-indexed semantic refinement functor.

**Proof.** Theorem 1 supplies the target of `Tree.extend`; the specified maps supply `Signature.Assignment`. Apply `Tree.homEquiv`. Equation satisfaction is precisely `Presentation.Model`; `Presentation.extend` supplies descent and its uniqueness. Necessity follows because any descended map sends equal quotient elements to equal target maps. `SemanticRefinement.functor` then applies to this actual `Calc.Hom`. On an arrow its function is explicitly (u_i)_i↦(interpreted u_i)_i, with the source's profile transport. The target equation follows from strict preservation of substitution. ∎

No equation can be justified merely by equal input/output observations or equal counts. In a finite instance the check evaluates both interpreted maps on every state and every actual event record. An infinite equation family requires a proof for that family, not a finite sample.

### Image and reflection

The image is exactly the identity-and-substitution closure of the assigned generator maps (with syntactic profiles retained); this follows by tree induction in both directions. A semantic map outside that closure need not be denotable. Choosing every semantic operation as a generator would make the statement uninformative, and is not required here.

The interpretation preserves all declared equations but need not reflect equations or arrow equality. For example two distinct unary generators on a singleton state/loop graph can both denote its identity map. Without a declared equation they remain distinct syntax but have equal semantic maps. Likewise two forests replacing the same repeated color at different occurrences are NOT identified merely because the colors agree; only actual entrywise equality can identify their images. If the interpretation is injective on each operation fibre, the original `mapArrow_injective` proves faithfulness on refinement arrows. No such injectivity is assumed for the dynamic model.

## 4 Exact witnesses and the previous dynamic theorem

Mark an operation (p,w) exact when w is bijective on states and on events. A graph map bijective on both sorts has a graph-map inverse: apply the commuting source/target equations and the inverse functions. Thus this is precisely graph isomorphism, not merely surjective behavior.

**Theorem 3.** Identities are exact. Substitution of an exact outer witness by exact witnesses at all occurrences is exact. This includes empty branches. Exactness of the resulting composite alone does not imply exactness of its nodes.

**Proof.** Invert each u_i independently and use the boundary equalities to assemble compatible parent coordinates. This is an inverse to expansion. For empty replacement profiles the inverse of u_i recovers the erased component coordinate from its interface value; exactness is exactly what licenses that recovery. Compose with w inverse. For nonreflection use unary component graphs consisting respectively of one and two states, each state with one self-loop. The injection 1→2 selecting one state followed by the constant map 2→1 has exact composite but neither constituent is exact. All boundary graphs can be terminal. ∎

For the common-interface instance, take one vertex with graph J and loop colors D,F,P whose left and right legs are the same map to J. Then the binary witness is exactly

    P → D ×_J F.

Its state component is χ and event component is η of `Exact_Dynamic_Factorization.md`. Consequently the prior rank-one multiplicity criterion applies to the binary marked fibre, with actual record bijections supplied, not merely counts. The original calculus also contains all nonexact maps P→D×_J F. Restricting the whole target calculus to exact maps is optional and is not done in Theorem 2.

The refinement functor retains the complete forest, not merely the composite graph map W_c→P(p). Two different replacement families may have the same composite because the outer witness sees only part of its component domain. This is precisely why the occurrence-wise arrow data must not be erased.

## 5 Time and spatial refinement

Write Path_n(G) for actual length-n executions with every event retained; Path_0(G)=G0. Applying Path_n to graph spans yields a target calculus of finite-set spans and backwards decomposition maps, with the same original syntactic types and profiles.

**Theorem 4.** For every n≥0 and every finite original profile p, there is a canonical bijection

    Path_n(P(p)) ≅ P_n(p),

where P_n uses the component execution sets and interface execution sets. Under these bijections the interpretation of every original tree commutes with Path_n, as does every original semantic refinement arrow. The comparisons commute with execution truncation and concatenation. An operation is exact iff its n=0 and n=1 maps are bijective; exactness therefore supplies bijections for all n.

**Proof.** A path of compatible tuples is exactly a tuple of component paths whose interface paths agree at every state and every event. The forward map transposes the time and occurrence indices. The inverse transposes them back. In a nullary profile both sides are Path_n(B_v). At substitution both constructions yield the same array indexed by time and the flattened occurrence address; hence the comparison commutes with substitution and thus with tree interpretation. Restriction to a time interval and concatenation simply restrict or concatenate the time index. Identity and associative transports are the same tuple maps. Exactness at n=0 and n=1 is exactly bijectivity on graph sorts; the inverse graph map gives all remaining inverses. ∎

This extends the earlier binary exact path comparison to the actual original calculus, including nonexact witness maps, their occurrence-wise refinement functor and specified spatial units. It does not establish the original contract's full graph-cut bisimplicial/2-Segal theory, nor asynchronous edge-to-empty-path views.

## 6 Interface changes and their obstructions

### 6.1 Forgetting boundary distinctions

Let q_v:B_v→Bbar_v be graph maps. Keep each component graph W_c unchanged and postcompose its legs with q. For every profile there is a comparison κ_p:P_B(p)→P_Bbar(p). For nonempty p it keeps the same component tuple; for an empty profile it is q_v. These maps commute with expansion, including empty substitutions. Hence w↦κ_p w gives a strict map between the two target calculi on the same syntactic quiver and gives the corresponding refinement functor.

For an exact w the changed witness is exact iff κ_p is bijective on both graph sorts. For a nonempty profile κ_p is injective: exactness therefore means no newly compatible tuple. For an empty profile injectivity need not hold, and the criterion is that q_v itself be an isomorphism. Treating every κ as an inclusion would be wrong.

For two components the condition is exactly: whenever q(r_D(d))=q(ℓ_F(f)), already r_D(d)=ℓ_F(f), on both states and events. For example two loop events labelled 0 and 1 on each component have two fine-compatible pairs and four coarse-compatible pairs after the labels are forgotten. The old exact witness remains a valid nonexact operation. This is the previous record-level interface obstruction in the original calculus.

Nonempty-profile graph-map equality is reflected by this coarsening map because κ is injective; exactness is not preserved. Although κ on an empty profile need not be injective, the fixed-output nullary operation fibre has at most one element, forced by its boundary legs. Thus the coarsening map is injective on all operation fibres (profiles remain retained), and consequently faithful on original semantic refinement arrows. This does not imply fullness or preservation of exact marking: new nullary operations may appear when previously unequal outer legs become equal after q.

### 6.2 Independently changing all endpoint types

This is NOT the same as the previous theorem's simultaneous common-interface base change. Given h_v:B'_v→B_v, independently restrict each component span to

    W'_c = B'_a ×_{B_a} W_c ×_{B_b} B'_b.

For a profile p:a→b write

    R_h(p)=B'_a ×_{B_a} P_B(p) ×_{B_b} B'_b.

There is a graph map π_p:P_{B'}(p;W')→R_h(p) forgetting internal lifted boundary coordinates. An old operation w gives a base-restricted map w^r:W'_c→R_h(p).

**Theorem 5.** A transported operation retaining that old witness is exactly a graph-map lift w':W'_c→P_{B'}(p;W') satisfying π_p w'=w^r. Equivalently it is a section of the pullback of π_p along w^r. If w is exact, an exact transported operation exists iff π_p is a graph isomorphism; if so it is unique. If each h_v is an isomorphism, these unique transports preserve all original substitution/refinement and form inverse equivalences under inverse interface changes.

**Proof.** The lift equation says exactly that every old component record and the two chosen outer lifts are retained. The pullback-section equivalence is the explicit map x↦(x,w'(x)), inverse projection. When w is exact, w^r is an isomorphism by its inverse acting on the middle coordinate. If w' is exact, π_p=w^r(w')^{-1} is an isomorphism; if π_p is an isomorphism its inverse composed with w^r is the unique lift. For isomorphic h all internal lifts exist uniquely, so π_p is an isomorphism. Both sides of any substitution or iterated transport equation retain the same old coordinates with their unique lifts, and hence agree. ∎

For a nonempty profile each state or event fibre of π_p is the product, over internal cut positions, of fibres h_v^{-1}(the required boundary value). Thus empty internal fibres obstruct existence and multiple lifts obstruct exact transport. A graph-map section also has incidence coherence; selecting states and events independently is insufficient. For a nullary profile at v, π is the diagonal

    B'_v → B'_v ×_{B_v} B'_v.

It is an isomorphism iff h_v is injective on both sorts. Thus even the identity boundary unit can fail under independent noninjective endpoint restriction. This is why a naive claim that the backwards-map target already has all virtual-equipment restrictions would be invalid.

The criterion can be applied only on the pullback along w^r for a nonexact w; unused parts of P_B(p) need not admit lifts. Moreover arbitrary individually selected lifts need not commute with substitution. Coherence must be proved for a selection, or forced by unique lifting as in the exact case. This is an explicit obstruction rather than an automatic interface action.

### 6.3 Simultaneous common-interface base change

For components all over one J with equal left/right legs, instead put W'_c=W_c×_J J' and B'=J'. This chooses ONE common lift, not two independent endpoint lifts. There are canonical bijections

    P_{J'}(p;W') ≅ P_J(p;W) ×_J J'

for every profile, including the empty profile. Consequently this construction commutes with the target calculus, its original tree interpretations, and refinement. It preserves exactness. It reflects exactness and equality of a specified witness when the projections from its domain and target back to the original graphs are surjective on both sorts; in particular a levelwise surjective h:J'→J suffices. Without this coverage a restricted interface may simply remove the counterexample records. The statements concern a specified base-changed witness, not descent of arbitrary new factors found only after base change.

## 7 Staging and the controller boundary

A one-phase graph map does not automatically respect which information is available before an action. For the staged systems in `Causal_Implementation_and_Control_Transfer.md`, repeat the construction sortwise in the category of finite diagrams with sorts X,M,E,O,A,V and structure maps s0:M→X, o:M→O, s1:E→M, a:E→A, t:E→X, p:E→V. Fix shared external O,A,V as appropriate; use explicit typed maps for any internal interfaces. Limits and compatible tuples are formed on every sort, so Theorems 1–3 and the interface comparison proof remain valid. Exact means isomorphism on the required state and actual pre/post record sorts, with specified external labels preserved. Initial sets require their own correspondence.

An alternative encoding is a phase-expanded graph with boundary vertices X, acquired vertices M, acquisition edges indexed by M and action edges indexed by E, and nominal phase/observation/action labels retained. The graph-map construction must preserve these labels and phase sorts. Merely proving isomorphism of collapsed X←E→X graphs does not suffice.

The fixture instance can therefore supply local component tables, actual shared contact records, a common open action socket and actual record comparison maps. The original tree interpretation composes those witnesses. If local maps are exact and stage-correct, Theorem 3 gives exact whole open-plant matching before selecting the controller. The existing causal-control theorem can then be applied after its additional hypotheses are proved: compiled observation timing, a fixed initialized controller memory, enabledness against every compatible context, safety and progress. These hypotheses are not consequences of an arbitrary original refinement.

A deterministic request/response runner has operations of shape Params_op×State→Response_op×State. It can implement an upper interface while issuing lower requests. Such a runner fits this staged finite model when its operations and actual invocation records are specified. Calling it a comodel of a particular algebraic theory additionally requires verifying that theory's equations; this note does not claim every graph span is such a comodel. Nondeterministic response relations retain their actual response records rather than being forced into deterministic co-operations.

## 8 What this closes

This proves a concrete original-core interpretation and occurrence-refinement bridge, identifies the prior exact dynamic factors as a marked semantic substructure, and proves time/refinement compatibility and explicit interface-change boundaries. The arbitrary-operation target is constructed independently of exact reconstruction, so it does not assume the desired factorization as its definition.

It does not prove that an arbitrary given presentation has a physically meaningful assignment, full faithfulness, arbitrary noninvertible coherent transport, the full original equipment universal property, original graph-model comparison, 2-Segal/recoverability, or physical controller correctness. Those require the corresponding data and arguments. No new Lean proof is claimed: existing Lean universal-property and refinement APIs are identified exactly; their concrete dynamic instance and the additional theorems here are mathematical proofs with reproducible finite checks.


## 9 A concrete presented equation and a rejected equation

Let G,F,O be three finite component graphs over J, with both legs equal to the label map. Define H_GF=G×_J F, H_FO=F×_J O and W=G×_J F×_J O. Retain the following four generator witnesses as distinct declared primitives:

    a: W→[H_GF,O],     b: H_GF→[G,F],
    c: W→[G,H_FO],     d: H_FO→[F,O].

Their maps are the coordinate groupings and ungroupings. The two literal trees

    a(b,id_O)     and     c(id_G,d)

are distinct source trees with the SAME output W and SAME original profile [G,F,O]. Declare exactly the parallel equation between these two trees, not the whole kernel of the dynamic model. On every state and every actual event (g,f,o), the left tree evaluates to ((g,f),o) and then (g,f,o); the right evaluates to (g,(f,o)) and then (g,f,o). Thus the required `Presentation.Model` condition is proved, and the existing `Presentation.extend` factors the interpretation through this genuine presented calculus. All four generators are exact, so either refinement tree preserves exactness. This is the original syntax with a specified independent grouping equation, not a quotient generated after inspecting all semantic coincidences.

In the fixture instance G is the gripper, F the fixture and O the object. Its independently specified local tables and compatible actual contact records supply these graphs; W and the two intermediate groupings are computed from them. The two branches encode expansion at DIFFERENT occurrences and their equation has been checked by actual coordinate maps, not by equality of successful outcomes. This particular equation expresses standard regrouping; its role here is to exercise the original presented API on the worked interaction, not to claim a novel associativity law.

For a rejected parallel equation, let a component have two distinct self-loop event records e0,e1 with the same visible contact response and the same boundary label. The identity witness and the witness exchanging e0,e1 have the same output/profile, state map and visible behavior, but different event maps. Assign them to two distinct unary generators. An equation identifying them does NOT satisfy the presentation model condition: evaluation at e0 differs. Even though both witnesses are exact, exactness does not license the equation. The same test rejects any proposed equalization of two grouping maps that differ by such a record permutation. This negative control is independent of whether the fixture's specific hardware has duplicate visible records; it shows what the source interpretation precondition actually checks.

A structural interface J may retain a complete coordination transcript (command, contact event, wrench, returned observation). A component's graph map to J does not grant its hardware permission to read all of that transcript. The fixture's staged implementation must separately show which incoming wires it uses and when. In particular the returned observation may constrain the mathematical matching tuple but may not choose the earlier action. The bridge preserves this distinction by using staged-sort maps for the implementation claim, rather than interpreting every field of J as a pre-action sensor.

## 10 Reproducible checks and provenance

`check_original_dynamic_bridge.py` exercises 578 grouping/occurrence instances, 225 nonempty-interface coarsening cases, 31 nullary diagonal cases, 2,184 nontrivial temporal path comparisons, 5,835 common-interface base-change cases (including reflection under surjective coverage), two retained boundary values after all-nullary substitution, a rejected parallel-record equation, nonexact cancellation, and retained-forest nonfaithfulness controls. It also checks the graph-section obstruction: the directed two-cycle maps surjectively on states and events to one loop, but neither of its vertices has a self-loop, so no graph section exists. This cover can occur as the internal boundary lift in Theorem 5 while the outer types are terminal. Sortwise nonempty fibres therefore do not prove transport exists.

These checks are regressions for the stated mathematical proofs, not exhaustive verification of all finite graphs or a Lean instantiation. Selected original Lean sources are copied unchanged into `theory/original/` solely for exact declaration provenance. The archive and previous delivered proof notes are unchanged.

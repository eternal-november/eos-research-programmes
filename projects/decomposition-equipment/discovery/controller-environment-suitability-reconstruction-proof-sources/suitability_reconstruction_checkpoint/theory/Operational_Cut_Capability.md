# Causal capability reconstruction from witnessed cuts

## Purpose and exact scope

A partial description can show that a small memory would suffice at each individual cut while concealing that the required memory encodings cannot be updated by one physical driver. This note derives a finite simultaneous criterion from actual history/readout records. It reconstructs the driver tables when the criterion holds and produces a concrete mixed-cut obstruction when it fails. The example is not the theorem: all finite cut systems, arbitrary finite alphabets, nonunique allowed task responses, shared driver occurrences and restricted finite hardware libraries are covered.

The finite episodic theorem is followed by a recurrent dynamic certificate theorem. In the latter, memory is related to environment state rather than assumed to be a function of it. This matters because two histories can reach the same environment state with different controller memories. The dynamic certificate theorem is standard finite-controller verification/synthesis infrastructure; it is not advertised as a new game-solving mechanism.

Spatial substitution in the original dynamic Calc is compatible-tuple expansion. It is NOT temporal concatenation of observations. The data below are temporal cuts and actual readout extensions extracted from an operational model. Any use with original spatial refinements must supply the comparison from that model and verify the cut/readout maps. The companion presentation note owns that bridge.

## 1 Actual records and physical sharing

Let C be a finite directed acyclic protocol of publicly specified phases/cuts. An occurrence a:c→d is one observation step. The observation/query protocol and its allowed branching are supplied independently; in this episodic theorem the driver computes the required terminal response, rather than selecting which observation branch the environment will offer. Publicly prescribed query commands belong to the protocol. Controller-selected commands in recurrent interaction are handled separately in Section 5. The same physical table may label several occurrences; write type(a)=τ. An independently specified finite set W contains the admissible complete episode records. W is nonempty. It may encode a correlated promise, persistent unknown world alignment, and adverse choices. It is not assumed to be a Cartesian product of independent sensor values.

For each cut c let W_c⊆W be the episodes actually visiting c. For an edge occurrence a:c→d let W_a⊆W_c∩W_d be the episodes taking that edge. At cut c let p_c:W_c→H_c be the FULL causal observable prefix, including the public path/phase tags, prior delivered replies and the driver’s prior issued commands, with H_c its image. It is not merely a summary of current world state. At occurrence a let o_a:W_a→O_τ be the newly delivered readout. The new prefix p_d is the old prefix with the publicly known edge tag and readout appended; in particular it factors through (p_c,o_a) on W_a, and does not discard the old prefix. Every episode has its specified actual path. Alternative branches are tested only on the episodes that visit them; a nonexistent history is never manufactured at an unvisited cut. Actual matching between overlapping charts must preserve these full prefixes. All subsequent formulas using p_c are restricted to W_c, and all edge formulas are restricted to W_a.

Each cut has a finite memory type M_c with a chosen budget b_c=|M_c|. Occurrences sharing physical table type τ have the same input memory type, reply type and output memory type. Public phase information is explicitly part of the interface. A b-state data register with an externally supplied phase schedule is not claimed to be an autonomous b-state machine. If a controller must maintain the phase itself, the phase states and scheduler implementation must be counted separately; a disjoint phase implementation has sum_c b_c states, not max_c b_c.

Shared component/cut occurrences impose specified anchors on history records. An anchor (c,h)~(c',h') requires the same physical memory value after the stated type identification. These anchors identify the same physical prefix occurrence under actual witnessed chart matching, or impose an explicit physical-memory constraint. Equality of current environment states alone does not generate an anchor. They do not identify different histories merely because those histories have equal marginal observations. Identity transport is used below for simplicity; specified bijections of memory types can be inserted in the equations.

For each physical table type τ fix a finite library L_τ of permitted total maps M_in×O_τ→M_out. The unrestricted finite-register case takes every such map. A restricted library can describe permitted gates or a finite set of compiled drivers. Mere set-theoretic factorization is not a hardware implementation unless its resulting table belongs to this library. If a circuit grammar rather than a finite table library is given, computing its exact table image is a separate compiler obligation.

At a terminal phase c, each w∈W_c has a nonempty or empty set A_c(w) of task-acceptable commands. An empty set means this episode cannot meet that terminal requirement. A physical decoder type δ has a finite allowed library D_δ of total maps M_c→A. Sharing a decoder means the SAME selected map is used at every occurrence of that decoder type.

## 2 The simultaneous cut criterion

Unknowns are only finite code maps e_c:H_c→M_c. They must satisfy:

C0 Initial implementation. At each initial phase, e_c factors through the actually available initial input and the permitted reset table. All occurrences of the same physical reset identifier use one common selected reset table. In particular, with no initial observation it is constant. One must not allow a different initialization for hidden world parameters.

C1 Actual shared cuts. Every supplied anchor has equal code values, after the declared type transport.

C2 Causal update compatibility. For each physical type τ, form its combined required table graph

    T_τ(e) = { ((e_c(p_c(w)), o_a(w)), e_d(p_d(w))) : type(a)=τ, w∈W_a }.

There must be a table u_τ∈L_τ containing this entire graph. Thus one table must work simultaneously across all its occurrences and all worlds. In the unrestricted-library case, this is exactly the explicit pair condition

    e_c(p_c(w)) = e_c'(p_c'(w')) and o_a(w)=o_a'(w')
        implies e_d(p_d(w)) = e_d'(p_d'(w')),

for every pair of occurrences a,a' of the SAME physical type τ and records w∈W_a, w'∈W_a'. This eliminates the unknown update function: the required graph is functional, and any total extension implements it. A relation that is functional separately at each occurrence is insufficient when the physical table is shared.

C3 Robust terminal response. For each decoder type δ there is one d_δ∈D_δ such that

    d_δ(e_c(p_c(w))) ∈ A_c(w)

for every terminal occurrence c of type δ and every w∈W_c. For an unrestricted decoder library, this says that for each memory value m the intersection of ALL A_c(w) whose encoded history is m is nonempty. Pairwise intersections do not suffice for set-valued task responses.

All conditions are finite tests on the actual record tables and allowed hardware tables. No global strategy, causal lift, or winning controller is assumed as an input.

### Theorem 1 Exact reconstruction

There is a deterministic driver with the specified phase/memory architecture, reset convention, table sharing, anchors and permitted hardware libraries that meets every visited terminal requirement on every record w∈W along its actual path if and only if codes satisfying C0–C3 exist.

Proof. A driver induces e_c by running it on the full actual observation/command/public-phase prefix p_c(w), for w∈W_c. Determinism and the full-prefix convention make the result independent of the chosen representative w. This argument would be false for an arbitrary lossy summary of the prefix. Its actual shared memory gives C1; its fixed update table contains every required pair in T_τ(e), giving C2; universal task success gives C3. Initialization gives C0.

Conversely choose witnesses to C0, one table u_τ to every C2 condition, and one decoder d_δ to every C3 condition. Assemble precisely those physical tables, retaining their sharing. Induction along the actual path of each episode shows that the register at c equals e_c(p_c(w)): the initial step is C0, and the successor step is the defining membership in T_τ(e). C1 makes paths ending at the same anchored cut agree. C3 then proves the required command for every actual adverse episode. No selected table depends on w or on a future reply. QED.

The proof handles arbitrary finite protocol length and branching. It does not authorize spontaneous switching between tables at different occurrences of a shared physical component. It also does not claim that W is an empirically correct description of the world.

### Consequences

1. A certificate consists of the code tables and selected permitted hardware tables. It can be checked directly without executing every syntactic refinement history.
2. Nonexistence is a finite constraint problem with explicit equality implications and hardware-table exclusions. Exhaustive search is a reference procedure, not an efficiency theorem.
3. For a fixed finite collection of allowed budget vectors, the criterion computes the feasible capability spectrum and its Pareto-minimal vectors. There need not be one componentwise least feasible vector.
4. Actual memory labels matter when hardware tables or sharing distinguish them. Quotienting codes merely by their kernels is valid only together with coherent relabeling of the corresponding tables and anchors. It must not independently rename each cut and then claim one fixed table.
5. All temporal composites inherit their encoded update equations by induction. A spatial-refinement theorem still has to show that its transported records, histories, table sharing and newly available readouts satisfy these SAME equations. The theorem does not equate spatial substitution with sequential composition.

## 3 What a single cut can and cannot certify

Suppose a cut c has a future-view map z_c:W_c→Z_c and a deterministic required task answer f:W_c→A. If one permits an unrestricted decoder M_c×Z_c→A, define a conflict graph on H_c: distinct h,h' conflict exactly when there exist w,w' with p_c(w)=h, p_c(w')=h', z_c(w)=z_c(w'), and f(w)≠f(w').

A code e_c admits such a decoder exactly when it is a proper coloring of this graph. The proof is the well-definedness of the required output on pairs (e_c(h),z). This is the familiar zero-error communication/confusability mechanism, not a new graph-coloring theorem.

For a general acceptable-action relation A(w), replace binary edges by forbidden memory fibres: a fibre is forbidden if, for some fixed future view z, the intersection of the acceptable action sets of all matching records is empty. The sets {a,b}, {b,c}, {a,c} show why a graph of pairwise conflicts loses information: every pair intersects, but the common intersection is empty.

Individual cut feasibility says nothing about C2. It allows each cut to invent an unrelated encoding with no implementable update between them. The next section exhibits this distinction with complete finite tables.

## 4 Strict mixed-cut obstruction

Take binary observations in fixed order x1,x2,x3,x4. This fixture permits unrestricted finite-register update tables separately at each public phase (distinct physical table types τ_t, or one table with the supplied phase tag among its inputs). It does NOT impose one phase-blind update table at every step. The promise domain and required response are

    0000→0   0001→1   0010→0
    0110→1   0111→0
    1000→0   1001→1   1011→0
    1100→1.

The domain has nine actual records; inputs outside it are not admitted environment episodes. At cut t, p_t is the length-t prefix and z_t is the remaining suffix. Every individual cut conflict graph is bipartite, so every cut separately admits a two-message code and arbitrary future decoder. The exact individual minimum profile is (1,1,2,2,2).

Nevertheless NO driver with at most two data-memory values at every cut computes this task.

Proof. At cut 2, the conflict graph has exactly the edges

    01—00, 00—11, 11—10.

Its connected path has a unique bipartition up to swapping colors. Hence every two-code has e_2(00)=e_2(10). Reading the same next bit 1 and using a deterministic update forces e_3(001)=e_3(101).

At cut 3 there is the odd-length conflict path

    001—011—000—101.

Any proper two-coloring gives opposite codes to 001 and 101. This contradicts the required update. QED.

Three values at cut 2 suffice, while two suffice elsewhere. One valid code assignment is

    cut 1: 0↦0, 1↦1;
    cut 2: 00↦0, 01↦1, 10↦2, 11↦1;
    cut 3: 000↦0, 001↦0, 011↦1, 100↦0, 101↦1, 110↦1;
    cut 4: code equals required response.

The assignments satisfy C2 at each stage. At cut 3, code 0 uses final reply unchanged, while code 1 complements it, on all promised records. Thus the feasible width profile is (1,2,3,2,2), and minimum maximum data width is exactly 3 although maximum individual cut chromatic demand is 2.

There is a second valid repair, with profile (1,1,2,3,2): forget the first bit; at cut 2 remember the second bit; at cut 3 use codes 000,100↦0, 001,101↦1, and 011,110↦2; the final update returns the required task response. These two repairs are incomparable.

In fact the ENTIRE Pareto frontier of feasible data-memory profiles is exactly

    A=(1,2,3,2,2),    B=(1,1,2,3,2).

Proof. Local conflicts require at least two codes at cuts 2, 3 and 4. If cut 3 has at least three, B fits within the budget. If cut 3 has exactly two, the preceding contradiction forces at least three actually reached codes at cut 2, since cut 1 has only two possible observed prefixes irrespective of its nominal budget. If cut 1 had only one code, a binary second reply could reach at most two cut-2 codes. Therefore cut 1 must have at least two codes, and A fits. The displayed implementations prove both sufficiency claims. Initial memory is constant, so one initial state suffices. QED.

Consequently there is no componentwise least sufficient capability profile: the componentwise meet of A and B is (1,1,2,2,2), which is infeasible. A repair can retain earlier information or provide more memory later. This is a precise simultaneous-repair obstruction, not an unsupported claim that two abstract closure operators fail to commute.

This is a regression certificate for the general reconstruction theorem, not a claim that nine records alone establish practical significance. Its mechanism is exactly the interaction of promise correlations, different cut encodings and a physical update constraint. A total Cartesian-input deterministic-function task has canonical residual functions whose updates are well-defined; there the corresponding obstruction is absent. The proper larger comparisons are incomplete-machine minimization and constrained branching programs, not only ordinary total-automaton minimization.

### Unbounded family of competing physical repairs

Take k independent copies of this episode relation, run at the same public phases, with k separately owned register components. Each component reads only its own reply and register and must produce its own answer; cross-register communication and pooling are physically forbidden. The typed profile measures the number of required active codes at each phase. Different phase cardinalities do not mean a fixed physical register can change its installed capacity for free. Installed capacity is discussed separately below. The full environment domain is the Cartesian product of the k promise domains.

The exact per-register Pareto frontier is the product {A,B}^k, containing 2^k incomparable resource profiles. Necessity follows by fixing all other episode records: the isolated driver's table still has to implement the entire nine-record relation on its own inputs, so its profile dominates A or B. Conversely, independent implementations of either repair in each register realize the product. This is a product-architecture theorem, not a claim that arbitrary centralized algorithms must decompose this way.

If j registers use the early repair A and the remaining k−j use B, their required joint active-code cardinalities at the five cuts are

    (1, 2^j, 3^j 2^(k−j), 2^j 3^(k−j), 2^k).

Every feasible product architecture can be improved componentwise to one of these choices before minimizing peak active-code cardinality. Hence the exact minimum peak joint active-code cardinality is

    3^ceil(k/2) 2^floor(k/2).

Indeed the two middle capacities are respectively increasing and decreasing functions of j, and their maximum is minimized by the two integers nearest k/2. In contrast, optimizing each cut separately still gives at most 2^k messages, with maximum individual-cut minimum exactly 2^k. The ratio is (3/2)^ceil(k/2). This is an unbounded gap between separate cut adequacy and causal implementability under the specified no-cross-register architecture, and an explicit tradeoff between early information retention and later buffering. It is not, without an additional permitted allocation architecture, the installed physical memory requirement.

If every register instead has one fixed capacity for all phases, each requires at least three values and the joint capacity is at least 3^k. Neither statement is a 3^k lower bound for an unrestricted centralized memory. The product argument is standard; its role is to amplify the actual mixed-cut obstruction and expose the architecture assumption, not to manufacture a general circuit lower bound.

## 5 Dynamic environments and memory relations

The episodic representation must not be misread as asserting that memory is a function of current environment state. For finite recurrent dynamics use a finite phase-indexed actual environment state set S_v, including any persistent unknown completion parameter θ. Every actual transition record has form (s,a,y,s'), with command a, delivered reply y, source phase v and target phase v'. All original records and adverse outcomes are retained, and θ does not change unless the model explicitly permits such change.

Fix a finite controller architecture with memory types M_v, allowed initializers, permitted command tables λ_v:M_v×Obs_v→Act_v and permitted update tables u_v:M_v×Obs_v×Act_v×Reply_v→M_v'. Shared table declarations again mean one selected table for all occurrences. Observation o_v(s) is the actual physically available value, not the full state. The implementation choices are made once, before the unknown world and all adverse outcomes.

Unknown reachable relations R_v⊆S_v×M_v, not functions S_v→M_v, satisfy:

D0 Every allowed initial environment state occurs with the memory assigned by the same permitted initializer using only its allowed input.

D1 At every (s,m)∈R_v, a=λ_v(m,o_v(s)) is an enabled permitted command. Absence of an adverse successor is treated according to the declared termination protocol; unplanned blocking is failure, not vacuous safety.

D2 For EVERY actual record (s,a,y,s'), the pair (s',u_v(m,o_v(s),a,y)) lies in R_v'.

D3 Every pair in R is task-safe, and every terminal command satisfies its actual task requirement. For sure finite-time completion without fairness assumptions, use the stopped-at-first-goal semantics: goal pairs terminate, and D1–D2 apply to nongoal pairs only. Give a natural-number rank on these nongoal pairs, strictly decreasing along every transition between nongoal pairs. This is safety-until-goal plus termination, not a claim about behavior after a goal has been reached.

### Theorem 2 Dynamic finite-architecture certificate

A selected finite physical controller is nonblocking and universally safe for every permitted initial state and every actual adverse run exactly when there are R_v satisfying D0–D3 without the termination rank. Under the stopped-at-first-goal semantics, it guarantees safe goal arrival on all runs, with no fairness assumption, exactly when such a certificate also has the stated rank, provided non-goal deadlock is excluded.

Proof. The sufficiency of safety is induction on actual transitions. For necessity take the actual reachable pairs. For termination, a decreasing natural rank precludes an infinite nongoal path. Conversely, in the finite stopped-at-first-goal closed loop the pairs reachable BEFORE the first goal have no nongoal cycle, since Nature could repeat a cycle forever; longest remaining path length supplies the rank. All finite hardware tables are fixed throughout the argument. QED.

Bounded synthesis enumerates permitted tables, not arbitrary unbounded distributed strategies. This theorem and its reachability/ranking method are standard infrastructure. The reason to retain it here is to make the dynamic semantics and quantifier boundaries exact: controller reconstruction may use relations between current world and memory, and a persistent unknown completion is not reselected at each step.

The static theorem is recovered by unrolling a finite episode into its actual prefix histories and reading the code as the reached memory. Conversely any reconstructed static driver induces a dynamic product relation. Recurrent environments cannot generally be replaced by finitely many episode records or by a memory encoder on current world state alone.

## 6 Relation to the source program and significance boundary

The source dynamic Calc retains actual state/event maps and occurrence-specific refinement witnesses. It supplies neither command ownership nor causal observation timing by itself. These are genuine additional operational data. The original Calc interpretation must be enriched by actual staged interfaces, or accompanied by a proved extraction of such interfaces from operational generators. The spatial/temporal comparison must preserve actual record matching, readout availability, physical-table sharing and budgets; mere graph isomorphism or equality of final response functions does not certify this.

The useful new obligation is simultaneous capability reconstruction across the program's witnessed cuts and refinements. The finite criteria above expose exactly what must be proved: terminal response adequacy, shared-table factorization, and dynamic closure cannot be checked independently at unrelated cuts. They are not, by themselves, a novelty claim for state minimization, closed covers, bounded controller synthesis or relational constraint solving. The companion presentation theorem must derive and preserve these constraints from the independently specified typed decomposition operations and provide the generated-language scope. Without that bridge the result remains a useful operational criterion, not the promised integrated structural milestone.

Primary comparison for incomplete-machine state minimization: the 1962 IBM report describes compatibility and generated-state-set techniques; later exact closed-cover methods explicitly require coverage AND successor closure. https://research.ibm.com/publications/some-theorems-for-incompletely-specified-sequential-machines-with-applications-to-state-minimization ; https://www2.eecs.berkeley.edu/Pubs/TechRpts/1993/2448.html . These baselines preclude presenting nontransitive compatibility or successor closure alone as new.

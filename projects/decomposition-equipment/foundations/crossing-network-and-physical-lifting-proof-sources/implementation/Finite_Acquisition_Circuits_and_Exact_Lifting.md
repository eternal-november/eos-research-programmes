# Finite acquisition circuits and exact lifting of crossing reconstructions

## Plain-language abstract

An abstract reconstruction can identify a subsystem without supplying the sensor hardware that would make it work. This note adds that hardware explicitly. A component has finitely many installed sensor ports, a specified collection of allowed local gates, and actual measurement records. It may reuse a reading, but obtaining a fresh reading is a different operation. We give a terminating procedure which decides whether a proposed witnessed component can be built on that hardware. The procedure generates exactly the allowed computations, rather than assuming that every mathematical function is physically available. Applied to a crossing network, it requires one implementation and one record identification that work in all the local views. Independently implementable views are not enough. The construction covers the previous raw-wire positive examples, the loss-of-decoding example, and the arbitrarily high-order port-budget obstruction. Its categorical semantics preserves composition of actual executions; unrestricted changes of interfaces are deliberately not declared physical operations.

## 1. Fixed physical data

All sets below are finite. Types are nominal and distinguish protected source wires from values readable at a particular receiver, even when their underlying finite sets are equal. Ordinary computational gates accept only readable value types. A protected exterior wire can become readable only through a permitted acquisition primitive; an internal local-state read is separately authorized at its owning receiver. Equality of underlying Boolean sets does not supply a type conversion. Wiring between receivers likewise requires a declared physical port. Fix a finite list of these sorts, a finite library G of typed deterministic gates, and explicitly listed constants. Gate evaluation is permitted computation; no other local function is implicitly permitted. It is legitimate, for a particular device model, to choose a functionally complete Boolean library. That permits arbitrary Boolean processing of values the device actually receives, not arbitrary sensing of exterior state.

A whole state is X=product_i X_i. A receiver occupying coordinates U has its own state X_U. A sensor primitive j has declared exterior support S_j and a finite span

    X_(S_j) <-l_j- M_j -r_j-> O_j.

An m in M_j is an actual measurement event, with source state l_j(m) and returned value r_j(m). Deterministic total sensors are graph spans of the earlier functions s_j. There is no gratuitous independent label factor. Multiplicity in M_j must describe distinct permitted executions of the stated primitive.

A physical allocation a installs a finite list of sensor instances. Each instance has an identity, a sensor type, and a receiver placement. A primitive may be installed at U only if its declared exterior support is disjoint from U. A device with k slots admits the finite allocations assigning a permitted sensor type or vacancy to each slot. This is a finite hardware grammar, not an arbitrary predicate on semantic maps. Different ports carrying the same deterministic raw value can be physically redundant, but are not silently identified as hardware layouts.

For a fixed allocation, its synchronized measurement-record set is

    W_a = {(x,(m_v)_v): l_type(v)(m_v)=x restricted to S_type(v), for all installed v}.

Its available local values are

    obs_a:W_a -> Z_a = X_U × product_v O_type(v),
    obs_a(x,m)=(x_U,(r_type(v)(m_v))_v).

The allocation does not expose x outside U. The source map src_a:W_a->X is used by semantics, not supplied as a gate input.

An implementation is the allocation and a finite typed circuit over G, whose inputs are the coordinates of Z_a. It computes an output of sort Y, or optionally Y+{abort} if an abort primitive is included. Its span denotation is

    X <-src_a- {w in W_a: h(obs_a(w)) != abort} -h obs_a-> Y.

Without abort, every physical sensor execution must be represented. Allowing a circuit to suppress an event is not automatic: the partial-execution/abort convention must be part of the chosen device specification. The total deterministic examples require no abort.

## 2. Composition and accounting are operations, not closure assumptions

There is ONE ambient syntax: acyclic nominally typed circuits, with finite-span sensor primitives and deterministic gates, denoting ordinary finite spans. Serial execution is a pullback over the COMPLETE wired interface, and independent parallel execution is Cartesian product. Protected/readable types prevent computational gates from accessing protected wires. A nominal protected source type may have underlying carrier X without granting any computational projection from X. Its only readable eliminators are its explicitly permitted local-state reads and sensor acquisitions.

The fixed-world apparatus of §1 is an **environment-relative instance of this same syntax**. All its simultaneous acquisitions must refer to the SAME whole state x. Carry an opaque environment wire X through the circuit. Its interfaces are X×A, where A is the readable payload; operations preserve the X coordinate and gates cannot inspect it. Serial composition is pullback over X×B, not merely B. Parallel composition sharing that environment is fibre product of records over X, not their ordinary Cartesian product. In categorical language these are spans in finite sets over X. Forgetting to carry X would allow a false execution pairing measurements from different whole states.

During an environment-relative computation, the complete span is X<-W->X×Y with right leg (src,out). The reduced notation X<-W->Y in §1 describes the same execution carrier after discarding the opaque snapshot at the final observation boundary. That discard is permitted only when no subsequent stage requires that snapshot. It cannot be used as an intermediate boundary and then silently reintroduce X. More generally a readable input A gives X×A<-W->X×Y. The executable language consists of acyclic circuits respecting this opaque wire, the nominal readable types, receiver placement, and explicit sensor vertices. Composition is allowed only when all these interfaces match.

**Execution lemma.** Restricting an execution of a glued circuit to its two subcircuits gives a bijection with pairs of records agreeing on the complete intermediate interface (including X in the relative model). Conversely such a pair joins to exactly one execution. This proves preservation of serial span composition; the corresponding argument proves the stated independent or shared-environment parallel law. Empty wire circuits denote identities and reassociation gives the ordinary canonical bijections. This is a proved semantics of syntax, not an assumed equipment.

The structural finite-span reconstruction theorem can be applied to the full boundaries with X explicitly carried, or fibrewise to spans over X. A shared-environment product must NOT be substituted for an ordinary Cartesian product without this translation. The fixed-world hardware lifting test below uses the reduced notation only to compare source/output event fibres; its composition claims always use the complete interface. Formally, the physical lift in Theorem A may equivalently compare X<-E->X×Y against X<-W->X×Y. The two tests have identical source/output equations. The previous raw and encoded examples use the protected source type X, whose readable eliminators are exactly their local-state projection and catalogued sensors. They do not grant arbitrary read access to X.

Two uses of an already computed wire share its upstream record. Two invocations of a sensor have two record coordinates. Consequently there is no equation

    copy after sensor = two independent invocations after copy.

For example, a sensor with two genuine internal execution modes, both returning the same visible value, has two records. Copying its result has two records, while invoking it twice has four. Erasing records to relations hides this difference. The example must be understood as a sensor specification with actual distinct modes, not permission to attach arbitrary labels to any gate.

Physical resource accounting follows circuit topology. Sequentially or independently composed devices retain the disjoint union of their acquisition vertices. Sharing a sensor is an explicit common vertex with fan-out, not an equation erasing one invocation. For deterministic raw input pins, a receiver may read one installed pin any number of times; its pin demand is the set of installed sources, not the number of wire uses. Combining two fragments at that same receiver can share their already installed pins, so the demand is their union. Independently installed devices do not acquire this sharing automatically.

The unbounded syntax is composition-closed. The k-slot fragment generally is not: composing circuits can require more slots, and changing inputs can require more source pins. A theorem about a fixed k-slot apparatus is a lifting theorem into that hardware fibre, not a claim that this fibre is a virtual equipment.

### 2.1 Nonadaptive snapshot normalization

The hardware grammar classified by §§3–4 is explicitly **nonadaptive and eager**: every acquisition vertex reads only its declared projection of the same immutable opaque snapshot X; its invocation is fixed by the allocation, never selected by a decoder-produced value. The local gates process the returned values and readable initial inputs. All allocated acquisitions execute once, even if a later decoder returns abort. There is no short-circuit rule skipping hidden executions. These are important physical assumptions, not semantic equations derived from spans.

**Normalization lemma.** Every finite acyclic implementation in this grammar is equivalent in exact execution-span semantics to (1) its distinct acquisition vertices performed first against the common snapshot, followed by (2) one permitted deterministic decoder circuit. The acquired records and their sharing are unchanged.

Proof. No acquisition depends on another acquisition's returned value or on a decoder gate, so move all acquisitions before all computational gates. Each acquisition retains its actual vertex identity and one record coordinate. The enabled records are exactly the synchronized set W_a: there are no further guard-dependent invocations. All remaining vertices are deterministic gates, whose original acyclic dependency order supplies a decoder circuit on the same measured values and readable initial inputs. Moving a read does not change X, which is immutable. Restricting a normalized execution to each original vertex and conversely assigning those vertex records gives mutually inverse endpoint-preserving maps. Fan-out retains one coordinate; separate invocations retain separate coordinates. ∎

Accordingly finite allocations plus gate-table saturation are complete for this declared grammar, not just a search through convenient implementations. Composition of two snapshot circuits preserves the grammar when the same X is explicitly carried and acquisition IDs of independent calls are kept disjoint; decoder outputs may feed later deterministic gates but cannot select or supply sensor invocations. Cached values shared across fragments come from one explicit acquisition vertex. Adaptive sensing, conditional acquisition, sensors reading computed payloads, mutable worlds within a tick, and feedback require a larger grammar and are not covered by the finite completeness claim.

## 3. Exact synthesis for a fixed finite allocation

Fix a. For every permitted value sort V maintain a set H_V of tables Z_a->V. Initially include precisely the input-coordinate tables and explicitly available constants. Repeatedly add

    g(h_1,...,h_n)

whenever g:V_1×...×V_n->V is in G and h_i in H_(V_i). Store a derivation circuit for each new table.

**Finite synthesis lemma.** This saturation terminates and H_V is exactly the set of functions Z_a->V computed by the allowed gate circuits on this allocation.

Proof. There are at most sum_V |V|^|Z_a| distinct typed tables. Each strict step adds one, proving termination. Every added table has a circuit by its stored construction. Conversely induction on the finite circuit's gate order shows every computed wire belongs to the appropriate H_V. Fan-out introduces no new operation on tables. ∎

This is a fixed-signature, fixed-allocation theorem. It does not give a finite search over arbitrarily many fresh sensor events. In particular the unrestricted composition language may have unbounded record cardinality. Hardware bounds make the allocation search finite. Unlimited gate count is harmless here because only finitely many tables on the fixed input sorts exist. The method is exact but can be very expensive; no polynomial synthesis claim is made.

If only reachable Z_a values matter, one may restrict all tables to image(obs_a). Saturating on the full product is simpler and ensures that an extension is genuinely a permitted circuit. Replacing it by all arbitrary functions on the reachable image would be unsound for a restricted gate library.

## 4. Exact witnessed lifting theorem

Let a proposed reconstructed component be the finite span

    T = (X <-s- E -t-> Y).

The E here is its actual event carrier, not a chosen event alphabet that can be enlarged freely. Fix a finite set of hardware allocations and the gate library above.

**Theorem A (physical lift).** T has an implementation, with its event distinctions preserved up to span isomorphism, exactly when some allocation a and generated table h in H_(Y+abort) admit a bijection

    phi:E -> W_(a,h) = {w: h(obs_a(w)) != abort}

such that src_a phi=s and h obs_a phi=t. In the total convention omit abort.

This is an effective criterion: saturation constructs the complete finite list of possible h; for each h the remaining test is finite typed bijection matching. Without additional anchoring constraints, this test reduces to the explicit equalities

    |{e:s(e)=x,t(e)=y}| = |{w:src_a(w)=x,h(obs_a(w))=y}|

for every x,y. With prescribed chart event correspondences, require phi to satisfy them as well; raw counts alone then no longer suffice.

Proof. An implementation supplies its allocation, generated table, and the claimed semantic identification. Conversely a successful test supplies a concrete circuit from the saturation derivation, and phi verifies its exact witnessed denotation. The unanchored count test is sufficient by choosing bijections separately on each endpoint fibre, and necessary by restriction of phi. ∎

This is not merely the instruction 'check whether an implementation exists': the allowed gate functions and physical execution carriers are explicitly generated from finite hardware data. It does not claim that synthesis by finite function-table closure is new.

### 4.1 Simultaneous local views

Suppose a structural crossing reconstruction has produced E and charts E_i with specified boundary maps and fixed maps k_i:E_i->E. Suppose proposed local physical implementations have record carriers R_i. Adapter data must be finite circuits built from the named primitives, with their acquisition slots bounded as for the component; validate their typing and compute their execution records directly. Any maps rho_i:R_i->W_(a,h) used below must be derived from these explicit circuits (or literal restriction of the same shared execution) and verified on their finite record tables. An arbitrary asserted map rho_i is not an implementation certificate. If adapters are to be synthesized rather than supplied, enumerate their bounded allocations and saturated gate tables too. A simultaneous lift requires bijections phi_i:E_i->R_i and one phi satisfying

    rho_i phi_i = phi k_i

for every i, together with the stated boundary and chart-pullback equations. There is ONE allocation, ONE gate table, and ONE base-record identification. Separate choices (a_i,h_i,phi_i) with no common lift do not pass.

**Theorem B (lifting a reconstructed network).** For a fixed finite structural solution and finite permitted adapter/allocation data, existence of a simultaneous physical lift is decidable by Theorem A plus these finite equations. Suppose, in addition, that every other component and context span involved in the network already has a specified physical implementation, with specified semantic identifications, and every adapter is an actual permitted circuit. When the test succeeds and its identifications are compatible with those data, every network composition equation proved by the structural solution holds up to the corresponding isomorphism of execution spans. This is not equality of circuit syntax. Each shared component occurrence must use the corresponding shared record; distinct occurrences use distinct invocation records.

Proof. Necessity is restriction of a physical network execution to each chart. Sufficiency uses the accepted circuits and identifications: each chart equation commutes by the displayed condition. For a sequential wiring, two records glue exactly when their complete interface values agree, including the opaque environment in the relative model; the execution/pullback bijection of §2 transports the structural composition equality to a circuit-execution equality. Induction on the acyclic network's wiring proves the complete statement. Shared records are glued only along the explicitly common physical vertex. The proof never identifies two independent acquisitions merely because their returned values agree. ∎

This theorem composes with a structural classification of E, k_i: apply it to each structural candidate. It is not a replacement for deriving those candidates, their coverage conditions, or their event identifications. For unbounded structurally invisible events, fixed hardware provides the necessary finite cut-off |E|<=max_a |W_a|. Hardware outside that finite signature needs a different decision problem.

## 5. Simultaneous lift obstruction even with compatible extensional views

Take Boolean state (a,b) and desired output a XOR b. Consider contexts b=0 and a=0. On the first context a-only hardware implements the output; on the second b-only hardware does. They agree at their common state (0,0), so their extensional tables glue on the union

    K={(0,0),(1,0),(0,1)}.

Nevertheless no single fixed one-raw-pin apparatus implements the glued output on K: the a-pin cannot distinguish (0,0) and (0,1), and the b-pin cannot distinguish (0,0) and (1,0). A two-pin apparatus works. Selecting which pin to acquire based on an unexposed context tag is not allowed by this hardware grammar. This is a small diagnostic for Theorem B, not by itself the larger crossing-network theorem. The true four-coordinate crossing below has the same failure through loss of local decoding state.

## 6. Recovery of the established finite-state examples

Choose deterministic raw or encoded sensors, Boolean gates NOT and AND plus constants (hence enough local computation for all finite Boolean truth tables), no abort, and one tick of synchronous state update. For any allocation a, W_a is in bijection with whole states X, but the circuit sees only local state and its installed sensor values. Theorem A therefore specializes exactly to constancy of the desired update on obs_a fibres. This specialization retains the whole-state source map while denying the circuit access to hidden exterior coordinates.

For raw sensors, a receiver U can realize f_U iff all essential exterior dependencies B(U) occur among its installed pins. Necessity is the single-coordinate indistinguishability pair. Sufficiency changes omitted coordinates one at a time and uses Boolean completeness to synthesize the resulting finite local table. For crossing U_t and C=intersection U_t,

    B(C) subset union_t B(U_t).

Thus an explicit merged raw-pin allocation reconstructs C whenever it fits its hardware slots. This proves a constructive physical upper bound; it does not declare the original budget closed under crossing.

For the encoded example c'=u XOR v XOR z, only sensors a=v XOR z and b=u XOR z are installed. Parents {c,u} and {c,v} use their internal u or v to decode. Their crossing singleton {c} sees only c,a,b. States (c,u,v,z)=0000 and 0111 have identical circuit inputs but different required output. No generated gate table can lift the singleton update, even with unlimited local gates and both sensors. Adding raw u, raw v, or raw z gives three genuinely different sensor allocations that pass Theorem A.

For r cuts of n=2^r state coordinates with f_i=AND_(j!=i) x_j and k=n-2 raw slots per component, every proper subfamily has intersection blocks of size at least two and therefore lifts; all r cuts force singletons with n-1 required exterior pins, so none can lift. A mathematically defined single-bit conjunction observation is not a primitive sensor in this apparatus. Synthesizing that observation requires all n-1 raw acquisitions at a singleton. The synthesis theorem accounts for this directly through hardware inputs, not through an after-the-fact cost label on the one-bit function.

## 7. Interface changes: exact positive class and a genuine limitation

Input precomposition along an actually available deterministic adapter circuit respecting these nominal visibility types is implemented by circuit composition, with its real acquisition demand included. Denotation is the corresponding input pullback of the execution span: events are (new input, old event) satisfying the adapter equation. A supplied adapter with additional hidden executions instead creates extra records; its semantics is span composition, not input restriction along its support function.

A FinSpan restriction at the output along v:Y'->Y has records

    {(x,e,y'): old event e starts at x, old output(e)=v(y')}.

It need not be physically implementable. It asks for one execution for EVERY possible inverse-image choice y', including multiplicity, and none when the inverse image is empty. A sufficient explicit relative class consists of output maps v for which the hardware library includes a finite fibre-enumerator primitive with span Y <-v- Y' ->id Y'; composing that primitive produces exactly the restriction. With a deterministic permitted inverse, bijective retyping is a special case. Without such a primitive or an equivalent circuit certified by Theorem A, no physical restriction is asserted.

For example, a deterministic output 0 pulled back along the two-to-one map {0,1}-> {*} has two witnesses at the new output. A deterministic circuit library with only one execution per input cannot realize that restriction. Adding a genuine choice primitive can, but changes the apparatus. This rules out claiming that the implementation language is automatically a virtual equipment with all finite functions vertical.

Noninvertible contexts can also hide physical obstructions by removing input states. Successful local implementations then do not imply a base implementation: §5 gives an explicit jointly covering family on K whose locally chosen hardware allocations fail to descend. Theorem B tests the common allocation and record matching instead of assuming descent.

## 8. Scope and further integration

Established here: a concrete composition-respecting operational semantics; exact finite synthesis for fixed hardware; exact witnessed lifting and simultaneous chart compatibility; resource bounds derived from circuit topology; the deterministic model's required examples; and an explicit restriction limitation.

Not established here: unrestricted equipment structure for the physical language; a polynomial synthesis algorithm; universal realization of all finite spans; arbitrary recursive/feedback circuits; a novelty claim for wiring syntax, finite term-function closure, or ordinary descent. The substantive network result requires the separate structural theorem deriving the candidate event carriers and compatible chart maps from actual crossing witnesses. The present note supplies an effective implementation layer for those candidates rather than treating physical admissibility as an oracle.

## 9. Compact gate obstruction and the semantic/syntactic distinction

Consider hardware with the two raw Boolean pins x,y and only XOR gates and constants. Every generated output is affine over F_2. The four context views x=0, x=1, y=0, y=1 of the actual whole output f(x,y)=x AND y are individually executable: their output tables are respectively 0,y,0,x. Their restrictions agree at every overlap, and all are restrictions of the one actual whole table, so there is no invented inconsistency in chart identifications. Nonetheless no single permitted base circuit realizes the whole. Every affine table satisfies

    h(0,0) XOR h(0,1) XOR h(1,0) XOR h(1,1)=0,

while AND makes this value 1. The displayed equation is preserved by every primitive and therefore certifies failure without quantifying over circuit sizes. Installing an AND gate repairs it. This is a family of crossed context views, not yet an embedding into the full four-component decomposition grid; it tests the implementation layer, not the independent structural theorem. Affine invariants and finite clone closure are standard mechanisms, not claimed novel here.

The synthesis output classifies finite semantic capabilities (allocation, computed table, and specified record identification). It does NOT classify every circuit layout: infinitely many circuits can compute one table by adding redundant gates, and their syntactic automorphisms are not the span realization group's automorphisms. Stored derivations supply concrete circuit witnesses for successful semantic capabilities. Any claim about a full syntax-level realization groupoid would require a separately specified quotient and proof.

## 10. Integration with the anchored network classification

Use the notation of `../theory/Anchored_Network_Reconstruction.md`: fixed local crossing realizations T_i over E_i, boundary maps p_i:E_i->E, actual whole-event anchors, and admissible quotient K of the tagged local carriers. For a reduced fixed-world hardware test assume E=X×Y, so its candidate has source whole state X and readable output Y; its compositional form carries X through both boundaries as specified in §2. For general publicly readable circuit interfaces, use their actual source and target instead. This is a substantive typing choice: a structural component with boundary B cannot be tested against whole-state-source hardware by silently setting B equal to an observation quotient. Either B explicitly includes the opaque environment, or a proved boundary/observation descent must first translate the component. The latter is not supplied for arbitrary component boundaries here. The structural theorem constructs, rather than assumes, the chart maps k_i and proves exact local pullback coverage A1–A4. If extra partial operations are part of the model, include O1–O2.

A physical semantic realization is a quadruple

    (K, a, h, phi:T_K ≅ W_(a,h)),

with a from the finite allocation grammar, h generated by its gate library, and phi satisfying the endpoint and actual chart-record compatibility equations of §4.1. Every implementation yields such a quadruple, by taking its structural kernel and execution identification. Every accepted quadruple supplies both the structural local factorization maps and a concrete circuit realizing their shared component. If the surrounding coverage conditions of theory Proposition 3 and the physical-context conditions of Theorem B hold, it also supplies the corresponding whole-network factorization in execution semantics. Without those additional hypotheses this classifies a shared component across the supplied charts, NOT arbitrary whole-network assembly.

This gives the exact finite physical filter on the structural action groupoid. With named physical ports and record identities fixed, a morphism is a permitted structural isomorphism g whose induced map satisfies phi' g = phi, with the same allocation and computed reachable table. It may not permute physical execution records independently. If the device specification itself allows hardware automorphisms, they must be supplied explicitly and included on the right side of that equation. Circuit-layout identities are outside this semantic classification.

### Hardware bounds the structurally invisible sectors

Let N=max_a |W_a|. Every physical candidate has |T_K|<=N. Exact cartesian chart coverage gives

    |T_i| = sum_(t in T_K) |p_i^(-1)(boundary(t))| <= |E_i| N.

Thus even local event sectors that were unbounded in the abstract all-fibres classification become bounded under fixed finite hardware. Enumerate the local realizations only up to these bounds, compute admissible K, and run the finite physical filter. This is a terminating complete procedure for generated physical semantic reconstructions with the stated fixed apparatus, rather than only a procedure conditional on already selecting all local hidden-event cardinalities. Completely ungenerated global events remain excluded by the structural theorem; allowing additional hardware events requires the semantics to expose them in its generated component or a separately justified hiding operation.

For semantic capabilities, gate tables differing only outside image(obs_a) can be identified after saturation. They must not be filled in arbitrarily before synthesis: retain at least one genuinely generated full-table extension and its circuit certificate. This quotient avoids treating unreachable assignments as extra physical behavior while preserving exact gate admissibility.

## 11. An active four-component grid with structural reconstruction but no physical lift

This example uses the same nominal circuit syntax with two explicitly supplied raw input pins for T. No later stage requires T’s old snapshot, so it may discard that snapshot at its output. All source coordinates used by R,Q,S are likewise explicitly supplied input pins; no hidden projection is inferred from an underlying carrier. All four component occurrences affect the output. Let

    A=B={0,1}², C=K=L=D={0,1};
    R(a1,a2)=(NOT a1,NOT a2);
    Q(k)=NOT k;
    T(x,y)=x AND y;
    S(c,l)=c XOR l.

Regard each deterministic function as its graph span, with one actual execution per input. Put P=T after R and N=S after (T×id_L). The actual whole function is

    F(a1,a2,k)=((NOT a1) AND (NOT a2)) XOR (NOT k).

Both parent decompositions (P×Q);S and (R×Q);N have the same F and unique input-indexed execution records. Their whole matching is the actual identity on those records. The grid has the exact global structural reconstruction T, not merely an unanchored relation with the same support. Since R is bijective and the P factorization is fixed, this T is forced.

Now restrict B along each of its four coordinate faces x=0, x=1, y=0, y=1, and restrict A along the inverse image under R. These are honest input endpoint restrictions, not hidden-event selections. Leave C,K,L,D unchanged. Each restricted grid is the corresponding restriction of the actual global grid, and the component maps on overlaps are actual restrictions of T. The local T maps are respectively constant 0, identity on y, constant 0, identity on x. Consequently all structural overlap, event, and coverage conditions hold; the family covers every B input.

Fix the same physical permission at every chart and globally: two public Boolean input pins (their fixed coordinate is supplied by the context on a face), constants, XOR, and NOT, but no AND gate. Every local T is implementable; R,Q,S are also implementable affine circuits and are behaviorally active. The global T is not implementable by the parity invariant in §9. No selectable context tag is supplied at the global interface: choosing a different local circuit according to which face contains the input would itself require a permitted global selection circuit, which affine gates cannot implement here.

Thus a genuine four-component crossing has a unique coherent witnessed reconstruction, all restricted shared components compile under one uniform permission policy, and the reconstructed global shared component fails physical lifting. The P,N and whole F in the negative case are semantic specifications; this example does not assume that they already have global implementations in the restricted affine library. The local restricted P_i,N_i do compile. It therefore demonstrates the exact remaining implementation obstruction, not a claim that a globally affine assembled system can mysteriously require nonaffine behavior.

Two matched positive controls are immediate. Adding the AND primitive implements the original T and both parent composites. Alternatively replace desired T by x XOR y, leaving the affine library and active R,Q,S fixed; all local and global factors then compile. These controls hold the wiring and actual chart construction fixed while changing either the permitted operation or the requested semantics.

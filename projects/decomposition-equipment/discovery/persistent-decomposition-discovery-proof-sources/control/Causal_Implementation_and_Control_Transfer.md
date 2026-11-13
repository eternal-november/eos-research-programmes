# Causal implementation and control transfer for persistent witnessed decompositions

## Plain-language abstract

A valid decomposition does not automatically provide a usable controller. A subsystem can have hidden internal state without ceasing to exist, but a controller cannot choose its next action using a measurement that will arrive only after that action. It also cannot assume that the surrounding system will permit every action its local model allows. This note separates these issues. It gives a finite, explicitly staged implementation language; an exact test that one repeated device realizes the reconstructed state and transition records in every view; and a control-transfer theorem with an explicit test for actions blocked by the context. For a declared finite controller-memory and hardware budget, successful safety and task completion can be checked for all execution lengths, not merely simulated for a time limit.

The finite circuit enumeration and finite-graph control tests are standard mechanisms. The bridge established here is their compatibility with the actual decomposition witnesses, including occurrence identities, signal timing, context matching and exact execution multiplicities. No claim is made for arbitrary adaptive hardware, unbounded controller memory, asynchronous communication or empirical robot validation.

## 1 Staged systems and the information boundary

All carriers are finite. A staged plant P has:

* tick-boundary states X and a nonempty initial set I;
* pre-action acquisition records M with source s0:M→X and readable observation o:M→O;
* post-action transition records E with source s1:E→M, control label a:E→A, target t:E→X and post-action readable value p:E→V.

Multiple records are allowed to share all visible values and endpoints. They represent actual different executions, not arbitrary extra labels. An execution is

    x0, m0, a0, e0, x1, m1, a1, e1, ...

with s0(mi)=xi, s1(ei)=mi, a(ei)=ai and t(ei)=x(i+1). Nature chooses the available m before the controller acts and the available e after the action. Empty acquisition or transition fibres are genuine deadlocks. A pre-action signal and a post-action signal are different nominal types even when they have equal underlying sets.

A finite deterministic controller has memory Q, specified initial memory q0, action function α:Q×O→A and memory update μ:Q×O×A×V→Q. The next action may use only q and the CURRENT pre-action observation. The memory update may use the post-action observation of the completed tick. No source state x, hidden component state, or current post-action signal is a controller input unless explicitly added as a permitted observation. Constant q0 can be generalized to a specified initial-observation protocol by including that protocol in M; it is not selected separately for each hidden initial x.

There is no observation-uniformity requirement on a mathematical state factorization χ:X≅Z×_B Y. A hidden component state z is legitimate. Uniformity applies to the implemented controller and to gates at receivers, not to the theorist's knowledge of χ.

A target originally given only as X←E→X does not automatically include sensor executions. Deterministic sensors with one record per state can be added by a canonical record-preserving staging. Nondeterministic sensors create additional executions. Either the intended whole already includes these records, or one must explicitly replace it by a sensor-augmented plant. The latter is an extension of the target, not an isomorphism silently preserving its original E.

## 2 A finite synchronous physical grammar

A hardware specification fixes finite nominal state sorts and a finite list of candidate allocations/templates. Each template is a finite typed DAG for one tick with the following phases:

0. **Read and acquire.** Authorized reads of the owning component's pre-tick registers, plus named sensor primitives on declared source supports. Every allocated acquisition executes once. Its invocation cannot depend on its own or a later phase's return value.
1. **Action socket.** The OPEN capability has a marked external action input of type A after phase 0. Its execution tables include every action value, whether enabled or not. Only after the open capability has been matched to the structural plant is a controller plugged into this socket. Its deterministic gates compute α from controller memory and the explicitly routed phase-0 observation. No controller gate here accepts a phase-2 or phase-3 type.
2. **Execute and communicate.** Named finite transition/handshake primitives execute using their declared local pre-state, action and earlier inputs. Their records may return post-action signals and proposed local updates. The dependency graph within this phase is acyclic, with explicit signal direction. There is no unmodeled joint scheduler that correlates independent primitives.
3. **Commit.** Deterministic gates commit each owner's next registers. A component cannot directly write another owner's protected state. Values needed at the next tick become explicitly declared registers. When a controller is plugged in, its separate μ circuit updates its own memory from the declared pre/post observation wires.

Each primitive is given by an actual finite execution table, with its input/output types, ownership, record set and source/target functions. Primitive records can depend on their listed inputs, including an action at phase 2; they are not required to be snapshot sensors. Fresh invocations have fresh record coordinates. Copying one output shares its upstream record rather than invoking it again. Communication wires and shared primitive occurrences are explicit vertices. Any shared boundary record used for synchronizing two components must arise from the same vertex or from a certified handshake, not from equating two independent random outcomes.

The grammar does not grant arbitrary functions of the whole transition record. In particular a proposed label λ:E→J is physically available only if it equals the value on the corresponding typed wire of a compiled template under the chosen event identification. A post-action λ remains post-action when that equality holds.

Plant state-register carriers, allocations, primitive invocations and wiring templates are fixed finite input. The controller memory carrier and its α,μ gate grammar are separate finite input, used only at the controller-synthesis stage. Open capability states X_C do NOT include that controller memory, and open record matching does not discard actions a particular controller never chooses. At each deterministic region the gate library is finite; arbitrary gate count is allowed. The available functions in a region are obtained by table saturation from exactly its input wires and constants. This terminates because its input and output carriers are finite, and induction on circuits proves completeness. With several regions, enumerate their finite generated-table choices in dependency order. Candidate state encodings may be enumerated among finitely many declared register carriers; no unbounded implementation state is invented.

The resulting pre-action record set M_C and post-action record set E_C are computed by enumerating compatible actual primitive records in the template. For a shared whole-state environment, all reads in phase 0 refer to the same pre-tick state; phase 3 commits only after phase 2. Reusing the resulting template at every tick gives a finite-state device, not a new independently selected circuit at each time.

**Proposition 1 (finite causal capability construction).** For the fixed OPEN grammar above, finite region-table saturation and exact primitive-record execution generate exactly the semantic capabilities of all gate circuits filling those templates, with the action socket left external. The enumeration retains actual M_C,E_C and all state, observation, control and post-observation maps. It supplies a finite circuit certificate for every generated capability.

**Proof.** Every generated region table has a gate derivation, and evaluating a filled DAG yields precisely its compatible primitive-record tuples. Conversely any permitted filled template has the same finite allocation and DAG. Induction through its deterministic gates puts each region function in the saturation. Induction through the template's phase/dependency order identifies its executions with the generated record tuples, preserving one coordinate per actual invocation. The template is repeated with the same state carriers and gate tables, so this argument is uniform in tick number. No phase reversal or hidden-state read is used. ∎

This is complete only for the declared finite templates/resources. The result does not cover arbitrary unbounded acyclic architectures, conditional invocations outside the templates, algebraic feedback within a tick, or arbitrary finite-state implementations with more registers.

## 3 Exact lifting of a reconstructed decomposition

Let a structural solution supply a fixed whole P, component/context states and actual component/context pre- and post-action records, together with state and staged-event factorization maps. In the simplest product case χ:X≅Z×Y and η:E≅D×_J F; in a state-interface case use Z×_B Y and require source/target boundary compatibility. A one-phase η must be supplemented by a phase-0 factorization whenever observations have their own execution records. Stagewise factorization is additional data to derive/check, not a consequence of counting complete transitions.

A physical lift consists of one compiled OPEN capability C (before inserting a controller), bijections

    χ_C:X≅X_C,  φ0:M≅M_C,  φ1:E≅E_C,

and the corresponding component/context record identifications. They commute with s0,s1,t,o,a,p and with the given χ,η and every actual crossing-chart anchor. The initial state is carried to the specified physical initial state set. If the component is compiled separately, all contexts and wiring used for a whole-device conclusion must also have their certified implementations.

For each view i, physical maps ρ_i on states and records must be actual restriction/projection of the same template execution, or come from a compiled permitted wrapper preserving phase. Require ρ_iφ_i=φk_i on both pre/post records and the analogous state equation. A time-varying or chart-varying choice of φ does not pass. Equal visible input/output behavior alone does not pass.

**Theorem 2 (bounded causal lift and all-time execution comparison).** Exact finite bijection matching against the capabilities of Proposition 1 decides existence of such a lift within the declared grammar. Every accepted lift gives, for every n, a bijection of length-n staged execution records commuting with initial state, every state at a cut, observations, actions, post observations, path concatenation and restriction to each chart. It also gives the corresponding bijection of infinite executions.

**Proof.** The finite matching test is necessary by restricting any implementation to its state and primitive-record carriers. It is sufficient because the accepted capability has a circuit certificate and the equations make it an isomorphism of staged transition structures. Apply the fixed φ0,φ1 coordinatewise to each tick. Source/target equations guarantee that adjacent ticks remain composable; inverse bijections give the converse. Concatenation and chart restriction retain the same coordinates, so all comparison diagrams commute literally up to the declared tuple reassociation. Infinite paths use the same pointwise maps; no compactness or limit selection of incompatible finite isomorphisms is involved. ∎

A physically meaningless signal can therefore fail before any controller is considered: it has no phase-correct wire realization. A meaningful post signal can support a component update but still fail to support the preceding action choice.

## 4 What exact factorization says about enabled actions

At a fixed concrete pre-action state, write it as a compatible component/context pair (z,y). For action a let

    J_D(z,a)={j : some component post record d starts at z with a,j},
    J_F(y,a)={j : some context post record f starts at y with a,j}.

Here z,y may include their pre-acquisition records, and j includes every synchronized boundary coordinate required by η, not merely its visible support. In the state-interface formulation restrict to compatible source boundary states.

**Lemma 3 (derived nonblocking criterion).** Under the exact post-record factorization η, a whole post-action record is available at (z,y),a if and only if J_D(z,a)∩J_F(y,a) is nonempty.

**Proof.** Any whole record determines a matching pair with common j. Conversely a j in the intersection supplies records d,f whose exact paired lift is a whole record. ∎

Thus component enabledness J_D(z,a)≠∅ alone is insufficient. Define a conservative context-robust admissible set

    Adm(z)={a : for every compatible y, J_D(z,a)∩J_F(y,a)≠∅}.

It is finite and computed from the actual factorization. Using only reachable compatible y can sharpen it when that reachability is independently established; quietly assuming favorable hidden context states is not valid. Context robustness is a DESIGN-TIME calculation. It does not reveal y to the runtime controller.

The decomposition does not itself imply that Adm(z) is nonempty or observationally distinguishable. A controller must choose an action belonging to Adm(z) at every z still possible under its observation history. If no such common action exists, that is a control/observation obstruction, not nonexistence of the component.

## 5 Local control transfer and its scope

Let A be a staged local abstraction derived by projecting the reconstructed component records, with a map h on concrete states/pre-records/post-records preserving actions, both observation stages and incidence. Require:

1. Every actual concrete pre/post record projects to a local record; initial states project into the local initial set.
2. Acquisition does not deadlock outside the terminal goal in the actual system.
3. The controller uses the same observation and memory update in both systems.
4. At every reachable concrete pre-record, its chosen action is concretely enabled. Lemma 3 provides an independently checkable sufficient condition through Adm.
5. Local safe states pull back to concrete safe states, and entering a local goal implies entering the concrete task goal. These are actual predicate implications, not guessed interpretations.

**Theorem 4 (sound transfer).** If that controller keeps every local execution safe and makes every maximal local execution reach its terminal goal, then it does the same in the concrete whole.

**Proof.** Map any concrete closed-loop execution through h. The observation equations and deterministic controller tables imply, inductively, identical memory and action sequences, so its image is a local closed-loop execution. Safety transfers by condition 5. A concrete execution cannot stop outside the goal: acquisition totality and chosen-action enabledness rule this out. Hence an infinite concrete execution projects to an infinite local execution; a finite maximal one ends in the goal. Local universal reachability and condition 5 give concrete reachability. ∎

This is standard simulation/feedback-refinement reasoning applied to a map DERIVED from the actual factorization and causal implementation. See Reissig–Weber–Rungger, *Feedback Refinement Relations for the Synthesis of Symbolic Controllers*, https://arxiv.org/abs/1503.03715v3, especially the feedback-composition and controller-transfer results. The staged model and exact witness map here are stated explicitly, so the proof does not rely on pretending its definitions are literally identical to that source's simple systems.

The theorem is sufficient, not a claim that a winning local controller is necessary whenever the whole is controllable. The local abstraction may allow interface histories that no actual context can generate. Completeness of control discovery is instead the bounded whole-device result below. Nor does safety of z alone prove safety of hidden y; condition 5 must establish the relevant whole-property implication.

## 6 Exact bounded controller test and constructive progress certificate

Fix controller memory size/carrier Q, initial q0 and the allowed gate grammar for α,μ. For each compiled structurally compatible physical capability and generated pair of controller tables, form the finite closed-loop graph H. Vertices are (x,q). Goal vertices are terminal: omit their outgoing edges when computing reachability, ranks and safety. For every NON-GOAL x and m with source x, set a=α(q,o(m)); for every e with s1(e)=m and a(e)=a add the ACTUAL edge (m,e) to

    (t(e), μ(q,o(m),a,p(e))).

All primitive acquisition records, transition multiplicities and independent invocations are retained. Mark as a blocked vertex any (x,q) for which there is no pre record, or for which SOME possible pre record m has no compatible e for the chosen action. Existentially having another productive m does not repair that adversarial deadlock. Reachability includes every edge and initial (x,q0), x∈I.

Take an absorbing terminal goal G and a safe set S containing G. The terminal convention is explicit: once G is reached the task ends; no obligation to execute a nonexistent next tick is imposed there. An equivalent implementation can provide a certified safe halt self-loop. If a nonterminal reachability target is desired, add a reached-goal bit before using the following cycle test; do not reject harmless cycles occurring only after the task was already achieved.

**Theorem 5 (exact bounded safety and progress).** A fixed candidate controller is sure safe and surely reaches G against every available acquisition/transition choice iff:

(a) every reachable vertex is safe;
(b) no reachable non-goal vertex is blocked;
(c) the reachable subgraph induced by non-goal vertices is acyclic.

Equivalently, (a),(b) hold and there is a natural-number rank r on reachable non-goal vertices strictly decreasing along every edge whose target is non-goal. Such a rank can be chosen below the number of reachable non-goal vertices. Every run reaches G within at most that number of ticks.

**Proof.** Unsafe reachability contradicts safety. A blocked acquisition/action choice produces a maximal non-goal execution. A reachable non-goal directed cycle can be followed forever by the adversary. Conversely, if (a)–(c) hold, every non-goal execution step that remains outside G follows a DAG edge and decreases a topological rank. There are finitely many such vertices, and (b) forbids stopping early, so every run enters G within the bound. Every visited state is safe by (a). ∎

Enumerating the finite generated α,μ tables and physical capabilities is therefore sound and complete for the specified finite-state hardware/controller grammar. This is not completeness over unbounded controller memory or arbitrary apparatus. If controller functions are unrestricted finite tables, this reduces to ordinary finite-memory controller synthesis; the nontrivial integration is that only one causally compiled device with the exact common decomposition records is admitted.

## 7 Substitution and permitted interface changes

Suppose one component occurrence in an accepted factorization is replaced by a physically compiled exact staged subfactorization. Require identical external pre/post observation types, actions, initial-state correspondence, and a phase-preserving state/record isomorphism at the replaced occurrence. Rename the primitive invocation IDs of independent occurrences apart. The execution tuple lemma gives an exact staged isomorphism between coarse and refined whole systems. Consequently a fixed external controller has isomorphic closed-loop graphs, and safety/progress ranks pull back along that isomorphism. This proves controller-certificate transport under EXACT occurrence-wise refinement, not every refinement that merely preserves outputs.

An interface adapter can be used in this argument only if it is a compiled phase-preserving template. A post-action wire cannot be retyped as a pre-action observation by an equality of underlying sets. A wrapper with extra hidden sensor/handshake records changes the record carrier and must satisfy the explicit exact matching equations; its extra records cannot be erased just because the returned values coincide.

For a noninvertible abstraction, Theorem 4 applies instead of an isomorphism argument, with nonblocking and predicate conditions checked anew. A chart/interface change may remove an obstructing context and create controllers that do not descend. Therefore independent local controller feasibility does not imply one common controller, and no equivalence of controller solution spaces is claimed for arbitrary interface changes.

## 8 Checks and claim boundary

The companion finite checker validates the critical distinctions: post-only information cannot choose an earlier action; persistent hidden information can become usable after a permitted probe and one memory update; resampling it after the probe invalidates that controller; an abstractly enabled action can be blocked by a context; and parallel records are preserved in exact matching. It also cross-checks the cycle/rank decision against an independent backward winning-set calculation on all 332,940 instances with one to three vertices, arbitrary directed edge sets, per-vertex unsafe/safe/goal status, blocking flags and a singleton initial vertex. A phase-typed gate check generates exactly 16 pre-action Boolean tables from memory/phase and 256 post-action tables after the returned bit is admitted; it rejects a backward-in-time wire and compiles the two-state probe controller. These are bounded regression checks, not an exhaustive check of every physical template or every finite plant.

The result is an integrated bounded bridge, not a new general control-synthesis mechanism. It requires explicit finite causal primitives and does not infer physical implementability from an arbitrary transition label. No stochastic probabilities, continuous robot dynamics, fairness assumptions, asynchronous message delivery, infinite-memory controllers or universal minimality claim are included.

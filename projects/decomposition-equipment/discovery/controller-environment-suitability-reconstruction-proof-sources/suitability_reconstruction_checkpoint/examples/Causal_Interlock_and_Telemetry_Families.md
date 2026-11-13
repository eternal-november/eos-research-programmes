# Causal interlock and telemetry families

## Plain-language purpose

A robot may be able to read every fact it needs and still be unable to use those facts with its installed controller. The order in which readings become available, the memory available between readings, and whether the readings describe the same stable environment can determine suitability. A one-bit answer at the controller boundary does not imply that a one-bit driver can produce it.

The principal family below asks for a complete pre-execution admission decision for a task involving many interlocks. It has arbitrarily many independent interlocks and arbitrary observation orders. We derive the required memory directly from which interlocks straddle each observation cut. A second family adds distributed side information and one shared telemetry driver. Its local pieces can all be controllable without one shared controller being possible.

These are deliberately recognizable computational stress families, not claims of a new equality algorithm or a new index-coding theorem. Their job is to force a reconstruction theorem to preserve causal information, shared-controller identity, physical observations, and the distinction between safe refusal and complete task suitability. A generic statewise factorization theorem does not suffice.

## 1. Task and environment semantics

For n >= 1, a task comes with a required interlock configuration u in {0,1}^n. A facility presents a current configuration v in {0,1}^n. The i-th bit can stand for the required versus actual discrete mode of a gate, ventilation partition, powered zone, or mutually exclusive access interlock. This is a model assumption, not a claim that real interlock safety is fully described by independent bits.

The admission predicate is

    Admit(u,v) = 1 iff every u_i = v_i.

The controller must emit its decision by the end of the inspection episode. The specification has two parts:

- Safety/soundness: do not admit when configurations disagree.
- Completeness/progress: admit when they agree.

Completeness is important. Safety alone has the constant-refuse solution, and the lower bounds below would then be false. Rejecting admission in an underobserved state does not prove the physical task unsafe. This family tests whether the controller can decide the specified admission question exactly, not whether every possible environmental configuration allows the task to proceed.

The environment chooses (u,v) adversarially at the start of an episode. The selected values persist until the decision. It then may choose a fresh arbitrary pair for the next episode. Consequently the result covers universal correctness over all modes, not an average success rate or a stochastic independence assumption. A stationary full-support stochastic version has the same zero-error requirement, but no probability claim is needed here.

Allowed observation operations are tagged reads U_i and V_i. Each returns only its designated bit, with a common episode identifier. The schedule pi is a permutation of the 2n read tags, so every bit is read exactly once. There are no unlisted sensor wires, rereads, hidden shared memory, or access to the full vector by an encoder. A known protocol phase may be provided by the schedule. Later we separately consider a uniform finite-state implementation without a free phase-dependent state relabeling.

The hidden mode and read labels form an ordinary finite staged transition system: stage t and (u,v) are the plant state; the scheduled read is the only admissible request; its reply is the corresponding bit; plant mode persists and the stage increments. The terminal controller action is permit/refuse. The task monitor checks the two clauses above. All possible mode choices and both possible replies where the hidden mode permits them remain in the system.

## 2. Actual crossing descriptions

Two different descriptions of the same episode are:

- Region/role descriptions: all U readings versus all V readings.
- Interlock descriptions: the n pair descriptions (U_i,V_i).

Their intersections are the individual tagged readings. They are crossing descriptions, not different parenthesizations of one ordered list. Statewise, the pair descriptions jointly recover (u,v), and the region descriptions do also. At the level of complete episodes they encode the same admission predicate.

The causal interface is extra data: which tagged observations have occurred before a decision or memory cut. Erasing that data makes block order and interleaved order look equivalent, even though their implementability differs exponentially. Merely reassociating a fixed ordered trace must preserve the result; permuting reads need not. A planar decomposition theorem must not silently introduce those permutations as harmless coherence maps.

A claimed physical repair must actually change an available operation: more controller memory, permission to interleave reads, rereads, or a stable-snapshot service. It cannot be justified solely by existence of an abstract function of the whole hidden state.

### 2a. Actual witnesses in the original dynamic target

This example can be assigned to the existing dynamic `Calc`, rather than adding a decomposition label to an unrelated machine. Fix pi and let J_pi be its clock graph: vertices 0,...,2n, with one actual edge (t,pi(t)) from t to t+1 at each nonterminal stage. The tag is retained as physical protocol data, although a bare unlabelled graph comparison could forget it.

For each coordinate z among U_i,V_i, define a component graph D_z with vertices (t,b) and events (t,b), where b is its persistent bit. Its source/target maps are (t,b) and (t+1,b). Both span legs project to J_pi. Define W_pi with vertices (t,u,v) and events (t,u,v), with the analogous source/target maps and clock legs. Assign all these as loop colors at the original interface vertex with boundary graph J_pi. Then the coordinate map

    W_pi -> D_U1 x_J ... x_J D_Un x_J D_V1 x_J ... x_J D_Vn

is bijective on states and on actual events, and preserves both legs. Its inverse assembles the bits, whose clock coordinates must agree. It is therefore an actual exact operation of the established dynamic target. The phase cut at t is the fibre over the actual clock vertex t; the consumed read tags are exactly the prefix of actual clock edges, not an independently guessed scanning order.

Let W_U be the compatible product of all D_Ui, W_V the analogous product, and P_i=D_Ui x_J D_Vi. The maps W_pi -> W_U x_J W_V and W_pi -> product_J P_i are exact operations as well. Refining either grouping into its actual bit occurrences is coordinate projection. For every original tree built from these grouping generators, substitution gives the same coordinate maps at its ordered leaf occurrences. This follows directly at both state and event sorts and supplies a generator assignment to the existing free calculus.

The two fully expanded profiles have different orders: the region grouping gives U_1,...,U_n,V_1,...,V_n, while the pair grouping gives U_1,V_1,...,U_n,V_n. They are not declared equal in the planar source. Their comparison is the explicitly specified permutation of named coordinate occurrences in the common-interface fibre product. Any extension admitting that comparison must retain it as extra data rather than invent symmetry. Importantly, this permutation of *spatial coordinates* does not change the physical order of clock events pi. One may regroup the same staged whole into pair components without acquiring the right to read those pairs earlier.

The physical observation function on an event (t,u,v) is exactly (pi(t), the designated bit). It does not expose the persistent hidden bits stored in a component's semantic state. A driver additionally carries its actual memory graph and causal update for this observation. Coupling requires the same scheduled tag/reply record and actual memory update, as in the separate causal-descent construction. A root graph's complete-state coordinate access is not a sensor wire.

For two schedules pi and pi', their completed length-2n episode sets are both canonically X={0,1}^{2n}. The resulting unstaged set bijection preserves the final admission predicate, but not the order of physical observation events. The residual-width theorem below proves that it cannot in general transfer a bounded-memory implementation. Within one fixed schedule, order-preserving typed refinement preserves the actual cut data and hence all residual widths. Across schedule-changing comparisons, residual-width excess supplies a concrete obstruction. This is a limitation of aggregate-record semantics for causal suitability, not a contradiction of the graph-level exactness theorem.

## 3. Exact residual-width theorem for every observation order

At a cut after t reads, let:

- A_t be the interlock indices with exactly one of U_i,V_i already read; write a_t = |A_t|.
- C_t be the indices with both readings completed; write c_t = |C_t|.
- The remaining indices have neither reading completed.

Two observed prefixes are residually equivalent if every common assignment to the unread tagged bits gives the same final admission answer. Since all modes (u,v) are possible, every prefix and every suffix assignment in this definition is permitted by the plant.

**Theorem 1.** The number of residual equivalence classes at cut t is exactly

    R_t = 2^(a_t) + indicator(c_t > 0).

**Proof.** If a completed pair disagrees, the residual answer is constantly refuse. This class is reachable exactly when c_t > 0. Otherwise, the residual behavior is determined by the observed bit at each active index. Each unread mate must equal that stored bit, and each fully unread pair must agree internally. The values of completed agreeing pairs have no further effect. Hence there are at most 2^(a_t) such nonrejecting residuals. For two distinct active assignments, complete the unread mates and wholly unread pairs so that one assignment admits. The other then refuses at an active index on which it differs. Thus all 2^(a_t) are different. Each is also different from the constant-refuse residual, because it has at least one admitting completion. This also covers t=0 and the terminal cut. QED.

**Corollary 1a, necessity.** Any deterministic causal driver that is correct for every episode has at least R_t distinguishable internal memory states at cut t. If two inequivalent prefixes produce the same state, their distinguishing common suffix generates the same future observations and therefore the same output, contradicting correctness for one prefix.

**Corollary 1b, sufficiency.** With a known protocol phase, a driver with maximum layer width W(pi) = max_t R_t exists. Its state at each stage is the residual class. Appending the next observed bit induces a well-defined next residual class: equality of current residual functions implies equality after restriction to a common next bit. Output is the final residual value. Thus the bound is exact for the stated phase-aware machine model, rather than just a necessary information count.

A state set can be reused across protocol phases, so W is the maximum simultaneous memory cardinality, not the sum of all layered states. If a single autonomous machine must internally retain phase, phase storage must be counted separately. No free schedule clock should be introduced when that interface is absent.

**Block order.** For U_1,...,U_n,V_1,...,V_n, the midpoint has a_n=n and c_n=0. The maximum is 2^n: earlier cuts have at most that many classes, and later cuts have 2^(n-k)+1 <= 2^n for k>=1. Thus at least n bits of persistent memory are necessary, although the final exposed answer is one bit.

**Pair-interleaved order.** For U_1,V_1,...,U_n,V_n, the maximum layer width is 2 for n=1 and 3 for n>=2. A uniform four-state machine works for every n: G (all completed pairs agree, expecting U), P0, P1 (pending observed U bit), and B (a disagreement has occurred). A U reply b moves G to Pb; the matching V reply returns Pb to G, and the other moves it to B; B remains B. The tagged fixed protocol guarantees the expected alternation. At the final cut, permit exactly in G. These four states include the pending-read distinction but do not need to count n.

The exponential separation is in actual controller memory demand caused by observation order. It is not a claim that computing equality is a newly hard robotics problem. This is the familiar residual-function/ordered-branching-program mechanism, now used as a compulsory compatibility test on the semantics of typed observation cuts.

## 4. Persistent episodes and unavailable observations

The block-order lower bound persists when the facility conducts arbitrarily many episodes with fresh adversarial modes. Fix any preceding episode history and the resulting controller state at the next reset. Vary the new u values. The same distinguishing-suffix proof still requires 2^n midpoint states; earlier episodes cannot store information about a fresh unconstrained mode. A reset operation can make the positive implementation reusable. Without a reset interface, the controller must implement its own return to G after committing the result.

More memory cannot repair missing current observations. Suppose a particular V_i can change adversarially after its last read and before admission, without an observable version change or interlock. There are then two executions with identical complete controller observations but different current admission truth values: use an agreeing state, and flip that final unseen bit in the other execution. No deterministic observation-uniform controller can satisfy both soundness and completeness, regardless of memory size. Randomization does not give a zero-error answer for both either.

This failure is environmental, not merely a deficient controller implementation. A permitted snapshot/locking protocol can repair it by making the readouts refer to one frozen version; a version number alone is insufficient if it does not establish a coherent snapshot and current validity at commit. The main family assumes the stable episode explicitly, rather than inferring it from readout data.

### 4a. A genuinely decomposed controller and its plant coupling

The positive interleaved driver also has a two-register implementation, so the controller side need not be treated as an opaque lookup table. It owns one pending-bit register p and one agreement register a, initially p=0,a=1. At a U_i reply b it updates p:=b and leaves a fixed. At the following V_i reply b it leaves p fixed and updates a:=a AND (p=b). Its final answer is a. Thus it has four possible register valuations independent of n. Induction on completed pairs gives a=1 exactly when all completed pairs agree; the pending register holds the preceding U_i before each V_i. Every input bit is the actual scheduled reply, not a hidden mode coordinate.

This has an exact two-component dynamic witness. Let the public reply graph O have stage vertices t and edges (t,b). Let internal interface I have vertices (t,p) and edges (t,b,p,p') with source (t,p) and target (t+1,p'). The latch L has vertices (t,p) and those I edges satisfying p'=b at a U stage and p'=p at a V stage. The accumulator A has vertices (t,p,a) and edges (t,b,p,p',a,a') satisfying a'=a at a U stage and a'=a AND (p=b) at a V stage; p' is an external wire value, not an independently owned memory cell. Both have two equal span legs to I. Their compatible product K has vertices (t,p,a) and exactly the edges satisfying both register equations. The coordinate witness K -> L x_I A is bijective on states and actual events. In the original dynamic target it is an exact binary operation with the actual latch and accumulator as occurrences. The p wire has one owner, L; its appearance at A is declared interface data.

The environment W_pi maps to O by the scheduled observed bit; K maps to O by its actual input reply b. Their graph pullback has states (t,u,v,p,a) and exactly the coupled steps whose b equals the environment's scheduled bit and whose memory updates obey both local equations. It retains every adverse mode and all actual read records. No information about the other 2n-1 bits is thereby exposed to K. Terminal output a is compared with the declared admission predicate. This supplies both an explicit environment decomposition and an explicit controller decomposition, plus their actual coupled executions.

These are three different interfaces: the fine clock port J_pi, the internal latch wire I, and the physical reply port O. The environment observation map W_pi -> O does not factor through J_pi, because the clock omits the observed bit. The observation map is therefore explicit additional structure, not inferred from the existing Calc boundary. The two Dyn decomposition witnesses and the physical coupling equations are all given directly; this alone is not a proof of a general equipment-level retyping or mixed-interchange theorem. Any general suitability compiler must consume those physical observation maps and preserve their timing.

Correctness follows by the preceding register invariant, rather than by an assumed controller/plant compatibility label. Controller-component expansion and environment-coordinate expansion give the same complete coupled tuples because they impose exactly the same equalities on t,b,p,p',a,a' and the selected mode coordinate. That elementary instance is a test of the general interchange theorem, not a proof of unrestricted interchange.

For block order, this particular two-register controller is not a candidate equality implementation: there is no preceding paired U_i held immediately before each V_i. The lower bound is stronger than its failure: every causal driver with fewer than 2^n midpoint states fails, even if its updates are redesigned completely. A larger controller may be suitable, and a controller with the pair-interleaved interface is suitable. Suitability is therefore a relation between environment protocol, task and actual controller capability, not a single intrinsic 'complexity level' attached to the environment.

## 5. Shared telemetry and distributed route selectors

A complementary family varies the spatial information architecture. Let a facility mode be x in a finite set X subseteq {0,1}^n. Local selector i must choose action a_i=x_i before its deadline. A bit may designate which of two local passages is admissible in that mode. The global task requires all designated selectors to choose correctly; an allowed always-stop action would require a separate progress specification to rule out vacuous success.

A telemetry driver sees only o_0(x) in O_0 and sends a message e(o_0(x)) in a fixed alphabet M. Selector i sees only the message and o_i(x), and computes d_i(M,o_i(x)). Its desired decision is more generally h_i(x). The family includes side information o_i(x)=x restricted to S_i, and h_i(x)=x_i. The physical observation map o_0 is an explicit input, not an omniscience assumption.

For a fixed installed controller, e and all d_i are given and suitability is the universal equation

    d_i(e(o_0(x)), o_i(x)) = h_i(x), for every x and i.

For bounded synthesis, the question is whether such e and d_i exist within the prescribed observation architecture and message capacity. Those are different questions and must not be conflated.

Define a demand-confusion edge between x,y when some i has o_i(x)=o_i(y) but h_i(x)!=h_i(y). Then:

**Theorem 2.** With unrestricted deterministic encoder and decoder tables on the stated finite interfaces, a suitable shared controller exists iff there is an M-valued coloring of the demand-confusion graph that is constant on every o_0-fibre.

**Proof.** A successful encoder cannot send the same message on a confusion edge, since the witnessing selector would receive identical data while requiring distinct actions. It also factors through o_0. Conversely, for such a coloring, define d_i(m,z) to be the common h_i value on the fibre of states with message m and local observation z. The coloring property makes this well-defined; define unused decoder inputs arbitrarily. QED.

Equivalently contract each o_0-fibre. A confusion edge inside a fibre is an absolute observation obstruction; otherwise the contracted graph must be |M|-colorable. Hardware-restricted encoders or decoders add constraints and are not covered merely by the coloring criterion. Multi-stage implementation is exactly where the preceding temporal family matters: an admissible static map can fail to have a runner with the permitted memory and observation schedule.

This theorem is standard zero-error coding with side information, and the full-observation side-information specialization is index coding. It is an audit baseline, not a new claimed contribution.

### Unbounded local-to-global control failure

Take X={0,1}^n, no selector side information, a fully observing telemetry station, and |M|=2^(n-1). Every proper subset J of receivers has a suitable controller: transmit x restricted to J, padding unused codes if necessary. But all n receivers jointly require an injective encoder on X, hence at least 2^n messages. Every pair of distinct modes differs in a demanded coordinate and is a confusion edge.

Thus every fixed-order collection of receiver tests can pass while the global system fails, by taking n larger than that order. The spatial plant factors into n independent hazard components and a star telemetry architecture, but the common encoder is one shared unknown, not a separate encoder that may be redesigned for each receiver chart. Using separate local encoders is precisely the unsound step. The example does not imply that all pairwise consistency algorithms fail when supplied a sufficiently rich complete shared-controller separator; the separator must retain the common encoder or equivalent causal relation.

### Nontrivial positive sharing

If each selector i observes all other hazard bits, the common parity message XOR_j x_j suffices: selector i XORs it with its side information to recover x_i. This sends one bit instead of n, but it uses actual observation wires and a permitted parity-computing encoder. If the telemetry station cannot distinguish a confusion pair, or if its physical operation library cannot implement parity, the abstract code does not certify the hardware. General side-information architectures connect the family to the established index-coding problem, including nontrivial coding advantages and limitations.

## 6. What this family demands from the main theorem

A successful general reconstruction result must instantiate the above models from their actual staged observations and task monitors, not add an assumed 'strategic exactness' hypothesis whose content is the desired answer. In particular it must:

1. Keep a single shared controller table/state update across all environment modes and overlapping charts.
2. Quantify universally over all environmental outcomes while requiring one causal, observation-uniform implementation.
3. Distinguish an abstract statewise answer from a runner that can obtain and retain the required information in time.
4. Derive the residual/memory obstruction and recognize the interleaved repair from actual interface data.
5. Preserve the admission guarantee under legal order-preserving refinement, while refusing to equate an unavailable reordered protocol with an implementable one.
6. State whether it checks an installed controller, synthesizes within a bounded architecture, or does both.
7. Return 'not certified by this information/capability' rather than calling every unrealizable admission algorithm a physically unsafe environment.

Monolithic model checking or bounded synthesis can solve the fully expanded finite instances. These families do not show that such methods are powerless. The decomposition contribution must therefore be a rigorous reconstruction/transfer and structural tractability result for independently supplied partial descriptions, with explicit causal separators and loss-of-information obstructions. Neither the known coloring criterion nor the residual-width calculation alone meets that ambition.

## 7. Primary baseline sources

- Ziv Bar-Yossef, Yitzhak Birk, T. S. Jayram and Tomer Kol, *Index Coding with Side Information*, author-hosted full version: https://webee.technion.ac.il/people/zivby/papers/indexing/indexing.full.pdf . Confusion graphs and the coding/coloring mechanism are established baseline theory.
- Noga Alon, Eyal Lubetzky and Uri Stav, *The rate of Index Coding*, author-hosted paper: https://www.cs.tau.ac.il/~nogaa/PDFS/witsen.pdf . It discusses confusion graphs and nonlinear/multiround coding effects.
- Randal E. Bryant, *Binary Decision Diagrams: An Algorithmic Basis for Symbolic Model Checking*, Handbook of Model Checking chapter, author-hosted manuscript: https://www.cs.cmu.edu/~bryant/pubdir/hmc-bdd18.pdf . Variable-order sensitivity and residual-function representations are established mechanisms.

The elementary proofs above are supplied directly so their use does not rely on importing an unverified theorem from a citation. The citations prevent presenting the underlying coding or decision-diagram mechanisms as new.

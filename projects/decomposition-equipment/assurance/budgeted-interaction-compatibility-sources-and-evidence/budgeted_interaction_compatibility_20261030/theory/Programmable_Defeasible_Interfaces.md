# Programmable interfaces with explicit validity conditions

Status: restricted theorem and interpretation added after the user's 30 October 2026 clarification. The numerical workload protocol is unchanged. The value of a discovered interface is that clients can be written and composed against it; a distinct efficiency advantage over another sound reconstruction method is not a necessary success criterion. Efficiency remains relevant to whether a particular interaction can meet its budget.

This note connects the existing action-record sufficiency theorem to a small programming semantics. It does not establish a general equivalence between models, comodels, runners and categorical cybernetics. The substitution proof is standard forward-simulation reasoning, instantiated to the evidence-indexed mission contracts in this project.

## 1. Interface data and what a program may use

An interface version I consists of:

- Public value types V, with ordinary deterministic functions, products, projections, copying and branching.
- An abstract interaction state z in Z. It includes the physical memory, time, resources and mission progress needed by the contract, or an explicitly proved sufficient summary of them.
- Typed operation symbols op with a public input type A_op and public result type B_op.
- A precondition Pre_op(z,a) and a nonempty allowed joint-record relation C_op(z,a) on (b,z',cost,hazard,mission-label). A record describes an entire operation interval, including its relevant pending effects. It is not merely a result marginal.
- A versioned assumption/evidence context Gamma and a validity guard G. The operation contract is valid only while these premises hold.
- A terminal predicate Acc(z), including completed mission obligations and safe termination of delayed effects.

In this restricted theorem the abstract state is publicly maintainable: each operation has a deterministic updater U_op(z,a,b), and every allowed record has z'=U_op(z,a,b). The result b contains exactly the public data needed for that update. Any hidden cost is represented by a conservative public debit or by retained uncertainty, rather than selecting a favorable hidden amount. This condition prevents a simulation witness from choosing the next abstract state using inaccessible information or future observations. The initial abstract state and each operation input are likewise computed causally from public data.

A client is a finite, causal program built from return, deterministic value computation, branching, and operation call followed by a continuation. Equivalently it is a finite operation tree/DAG. At a call, the current abstract interaction state is consumed and its successor is passed to the continuation. The result value may be copied and passed to several pure calculations. Copying that value does not duplicate the physical interaction state, remaining energy, a pending effect, or the authority to execute a resource-consuming operation.

This state-threading restriction is a programming discipline, not a theorem that physical states are mathematically uncopyable in a Markov category. A concrete API may use a single owned handle, a state monad, a graded effect, a capability system, or another mechanism. No particular language implementation is claimed here.

Program verification uses C_op: each called precondition must hold; every permitted result/successor branch must continue safely; costs and time must be debited; every terminal branch must satisfy Acc. A branch cannot inspect a hidden mechanism or a report that has not yet arrived. The existing finite WIN certificate is one concrete representation of such a verified client.

## 2. Realizations and handlers

A realization M has a concrete state space X_M, permitted operation implementations, and the same public value interfaces. Its hidden mechanism may be deterministic but unknown, as in the ladder benchmark, or genuinely stochastic in a separately specified extension. For the deterministic/nondeterministic statement here, each concrete call produces a nonempty set of full joint records.

Let R_M(x,z) relate concrete states to their abstract interface state. We require the following operation obligations whenever R_M(x,z), Gamma is true and G holds:

1. If Pre_op(z,a) holds, the implementation accepts the call and terminates within its declared interval/resource bound. It cannot deadlock or introduce an unbounded delay.
2. Every concrete result has the same public result value b as some allowed abstract record in C_op(z,a), with a related successor R_M(x',U_op(z,a,b)). Matching a record is not permission to choose a hidden-dependent public state: the updater has already fixed it from available data.
3. The abstract cost/hazard/mission interpretation conservatively covers the concrete one. In the exact specialization these fields agree. More generally, the contract debit upper-bounds actual cost, contract safety implies concrete safety, and abstract terminal acceptance implies concrete mission completion with safe termination.
4. The preserved state relation and assumption context are available at the next call, and the validity guard required by that call is preserved or re-established before it executes. A different guard or version requires a separately validated replacement contract. Exiting G without such a contract ends the theorem's applicability. The concrete history is not forgotten by reselecting an unrelated hidden mechanism after each step.

The operation implementation is a handler for the interface signature in this limited sense: it interprets the primitive calls and threads concrete state. This terminology does not assert a general algebraic-effects/comodel correspondence.

## 3. Positive program substitution theorem

**Theorem.** Suppose a finite client P is verified against I, M satisfies obligations 1–4, and its initial concrete state is related to a verified initial abstract state. Then executing P with M preserves the certified safety, resource and terminal mission guarantees for every permitted concrete execution. Consequently any replacement M' satisfying the same interface obligations can run the same client without re-proving the client against M's private mechanism.

**Proof.** Induct on the finite program tree. Return is sound by terminal preservation. Deterministic value computation and branching preserve equal public values and therefore choose the same syntactic continuation. At an operation call, the client's proof establishes Pre_op. Obligation 1 supplies a terminating execution. Obligations 2–3 match its public result and safe resource debit to an allowed contract branch. Obligation 4 supplies a related successor and the still-valid assumptions. Apply the inductive hypothesis to that continuation. Sequential composition is substitution of a verified continuation at the leaves, so the same induction proves closure under sequencing. The argument applies to every concrete branch, not just a favorable sample. ∎

No separate efficiency advantage is needed for this theorem to be useful. The programmer consumes the exposed contract rather than rederiving private mechanics at each use. Nor is canonical minimality required: a nonminimal but adequate interface can support the same program.

Forward refinement is sufficient for these positive guarantees. It is not sufficient for transferring a negative/no-policy certificate from the interface to a realization: an overapproximate contract can contain spurious adverse branches or omit implementation-specific legal actions. Negative transfer requires the stronger exact-action and exact-joint-successor correspondence of the main theorem, including completeness of the action vocabulary and consistent extension of every adverse branch. The distinction must remain visible in an interface API that offers both successful programs and impossibility claims.

## 4. How the learned record theorem supplies an interface

The main theory has an exact evidence relation K, a public-state guard G, and a proposed retained mechanism-variable set D. Conditional record sufficiency requires that two K-consistent mechanisms agreeing on D give the same full interpreted action record throughout G. It therefore supplies a well-defined reduced record map g(s,theta_D).

The allowed interface records can be the image of the supported D-tuples under g. The exact supported relation supplies the realization obligations for every theta in K. If an action has several local record components, their outcomes must still share a global evidence-consistent witness; independently combining marginal possibilities is not a substitute.

The programmer need not see theta_D or the full relation K. The interface can instead expose operation contracts and certified propositions that the client needs. Hiding the proof machinery from the client does not make its acquisition, construction or verification free: those remain implementation costs. A generic language, automatic interface extractor and programmer-facing tooling have not been implemented in this experiment.

There are two distinct forms of reuse:

- Program reuse: another realization satisfies the same operation contract and initial-state relation, so the same client proof transfers.
- Evidence reuse: further observations restrict K to K' contained in K. An already proved record-sufficiency fact and map remain valid under the same guard and mechanism semantics. The successor interpreter must still use the restricted evidence correctly.

The first is a substitution law. The second is a monotonicity law. Neither says that arbitrary evidence retraction, model change or observation hiding is harmless.

## 5. A concrete program interface from the main witness

The existing four-actuator example has three overlapping pair jobs and exactly twelve energy units, enough for six useful activations and no diagnostic pulse. Its hidden parent selectors range over 47 worlds. All are covered by the same program.

Expose the following operations and values:

- Work(i,stage) and Idle thread the clock, energy, previous-input state and job state. Their result includes the newly arrived report.
- Decode(report,history) is a deterministic calculation licensed by the known measurement and lag semantics. It may return certified edge facts or leave a fact unknown.
- Edge(0,2) and Edge(1,3), once determined by the relevant reports, are ordinary Boolean values. Certified consequences include NoLag(3,2) from Edge(0,2) and the one-parent assumption, and NoLag(3,1) from Edge(1,3) and no reciprocity.

The client idles in slots 0 and 1, works actuator 1 for job 1 in slot 2, idles in 3, works actuator 0 to finish job 1 in 4, and works actuator 0 to start job 2 in 5. The available reports now determine the two edge flags above. The remaining program is:

- If Edge(0,2), work 3,2,1 in slots 6,7,8, assigning the stages to jobs 3,2,3.
- Otherwise, work 2 in slot 6 to finish job 2. If Edge(1,3), work 3 then 1 for job 3; otherwise work 1 then 3.
- Idle in slot 9 to clear the tail.

The Boolean facts can be copied to several pure branch conditions and proof checks. This does not spend energy again, rerun the measurement, or claim an independent sample. Each Work invocation still consumes the one live interaction state and its own energy/time. The branch-specific NoLag contracts justify the consecutive work transitions which the frozen prior could not certify. Other parent details can remain hidden behind the interface whenever the required contracts are established.

The existing independent witness replay checks this program's causal observation use and its execution in all 47 worlds. This note supplies a programming interpretation and substitution obligation; it does not add an independently implemented language/compiler or a new measured program-portability benchmark.

## 6. Defeasibility and invalidation

Attach each exposed fact/operation certificate to its dependencies: evidence identifiers, mechanism/superscope version, structural assumptions, physical-state guard, observation interpretation and resource convention. A client may rely on it only while those dependencies are valid.

If K shrinks while the assumptions and guard remain unchanged, the old universal fact remains true. If evidence is retracted and K expands, or an assumption/version changes, only certificates whose dependencies are demonstrably unaffected may be retained. All affected uses must be suspended or rechecked before execution. A complete dependency map permits sound selective invalidation; it does not promise that the affected set is small. A global assumption can invalidate the whole program.

Suspension is a refusal to rely on a defeated contract, not a general physical safety or completion guarantee. Any fallback, idle or stop action must independently be safe in the current physical state with pending effects, and rechecking consumes its declared time and resources. The ladder's zero-input fallback is safe under its own retained load assumptions; arbitrary interfaces need a separate fallback obligation. Once the theorem's premises cease to hold, its ongoing mission guarantee does not continue by default.

**Concrete failure witness.** After learning Edge(0,2), the example derives NoLag(3,2) from the one-parent law. Suppose the mechanism class is enlarged to allow both 0 and 3 to be parents of actuator 2, with additive lag effects. The earlier reports can still be identical because actuator 3 has not yet run. The old client then works 3 in slot 6 and 2 in slot 7. In the enlarged world the doubled load at actuator 2 in slot 7 is 2+2=4, exceeding the limit 3. The edge flag remained true; its derived exclusion lost its premise. Copying the flag or its old proof does not restore validity.

This is not a claimed failure within the original fixed one-parent universe. It demonstrates why substitution into an enlarged universe requires revalidation. If physical change or premise invalidation happens silently, the theorem provides no automatic detection guarantee. A monitor, controlled configuration change, trusted version mechanism or other separately justified premise must establish that invalidation is noticed before a hazardous use. Stopping after a violating report arrives can be too late.

For stochastic evidence, a defeasible confidence claim also needs its own calibration, dependence and optional-stopping semantics. The deterministic exact benchmark does not prove those by analogy.

## 7. The Markov-category copying connection

In a Markov category, deterministic morphisms are defined by preservation of copying:

    copy_Y composed with f = (f tensor f) composed with copy_X.

They form a cartesian monoidal subcategory. This supports ordinary deterministic programming structure on exposed values. The fact does not say that stochastic computations can be duplicated without changing their meaning. For a fair-bit kernel f from the unit to {0,1}, sampling once and copying gives only 00 or 11, each with probability 1/2; two independent invocations give all four pairs with probability 1/4. The copy map exists, but naturality across arbitrary stochastic morphisms fails.

These are established results: Tobias Fritz, “A synthetic approach to Markov kernels, conditional independence and theorems on sufficient statistics,” Definition 10.1 and Remark 10.13, https://arxiv.org/html/1908.07021v8#S10 . In finite stochastic systems the deterministic maps are ordinary functions. General measurable settings need their usual qualifications; this note uses the finite case.

A stochastic extension of the substitution theorem must preserve the joint law of public result, successor state, costs and hazard/mission labels under the declared contexts. Copy-preserving deterministic interface maps support duplicated value uses. A general stochastic comparison that preserves only a one-use output marginal does not justify substitution into every client that copies an intermediate result or shares randomness. Parallel composition additionally requires ownership/resource and joint-preparation assumptions; a bare product of marginal contracts is insufficient.

The ladder's uncertainty is epistemic uncertainty over fixed deterministic mechanisms, not a probability distribution over mechanisms. Its policy program and deterministic decoders illustrate the value/effect distinction, but do not instantiate a proved general Markov-category reconstruction theorem.

## 8. What this addition establishes

It supplies a precise restricted programming payoff: an interface can serve as a contract against which a causal client is verified, with positive substitution across compatible realizations, explicit validity dependencies and an obstruction when a structural premise is lost. The concrete client uses learned facts to compose useful work rather than reconstructing every hidden parent.

It does not establish that interfaces must be faster than other phenomenological representations. It also does not yet implement a general interface-discovery language, automated runner construction, arbitrary concurrent ownership discipline, or stochastic defeasible-certification calculus. Those are separate technical obligations, not consequences of the word “interface.”

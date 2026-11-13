# Concurrent progress: prior art and scope

2026-10-31. Research and framing notes, not a novelty claim. The prospective acceptance criteria below record the motivation for the final scoped theorem and reconstruction comparison; README.txt and the two theorem sources state the delivered result. Read against `progress_feedback_20261031/excursion_progress_transport.md` and `composition_challenge.md`. Sources below are primary; where only the abstract was checked, that limitation is stated.

## Finding first

The worthwhile next result is **not** that round-robin scheduling plus local drift ensures completion. Nor is progress-preserving abstraction under parallel composition a new general idea. The specific unfinished target is to derive a resource-sensitive concurrent wiring operation on the relevant two-sided cylinders, prove its actual comparison law, and show that a local progress certificate remains meaningful under that law. Existing concurrency theory should supply the progress discipline wherever possible.

The previous serial interface records invocation duration and final exit, even in its strongest full-kernel form. It does not record transient lock ownership, requests, release order, or what another component may do between these events. Consequently its reconstruction theorem cannot simply be reused as a concurrency theorem. An honest extension needs new observations/interventions and a derived assembly operation; it must not hide the entire desired global property inside a “compatible scheduler” assumption.

## Verified primary baselines

### Fair probabilistic concurrency is an old and substantial subject

Hart and Sharir, *Concurrent Probabilistic Programs, or: How to Schedule if You Must* (SIAM J. Comput. 1985), studies finite collections of probabilistic processes on discrete, possibly infinite common state spaces. Scheduling may depend on past random outcomes and internal states. Its fairness convention gives probability one to paths scheduling each process infinitely often; it characterizes worst-case termination probabilities under such schedules. This is not merely independent-module scheduling. Checked introduction and conclusion, not every characterization theorem. [Author-hosted paper](https://math.huji.ac.il/~hart/papers/sched.pdf).

Consequence: neither countable state spaces, probabilistic interference, nor history-dependent fair scheduling is by itself a novel extension. State whether our result quantifies over all admitted schedulers or constructs one particular implementable scheduler.

### Blocking requires liveness obligations, not just safety relies

TaDA Live abstracts blocking operations using environment liveness assumptions and layered subjective obligations. Its section 4.1 client distinguishes spin and CLH locks under weak fairness; its discussion explicitly separates eventual release from mere scheduling. Safety relies describe allowed changes, not the promise that a helpful change occurs. Checked abstract, fairness discussion, and Example 4.1. [Primary full text](https://www.cs.toronto.edu/~azadeh/resources/papers/tada-live.pdf), [arXiv record](https://arxiv.org/abs/1901.05750).

A complementary baseline is Reinhard and Jacobs, *Ghost Signals: Verifying Termination of Busy-Waiting*: modular termination under fair scheduling uses obligations to set signals and a well-founded ordering that excludes circular waiting obligations. Checked primary abstract. [Paper](https://arxiv.org/abs/2010.11762).

Consequence: an acyclic dependency/lock-order or obligation discipline is established machinery. Our scheduler must actually discharge any environment obligations claimed by a local contract; repeatedly polling an unavailable resource does not discharge them.

### Termination-preserving concurrent refinement already exists

Liang, Feng and Shao, *Compositional Verification of Termination-Preserving Refinement of Concurrent Programs* (CSL–LICS 2014), explicitly provides a simulation that is a congruence under parallel composition, with applications to linearizability plus lock-freedom and concurrent optimizations. Checked author-hosted abstract. [Primary record and paper links](https://flint.cs.yale.edu/flint/publications/rgsimt.html).

Lilo (2025) develops higher-order relational concurrent separation logic for liveness, including refinement of nonterminating programs and modular specifications, with mechanized examples. Its basis is fair operational semantics and its range exceeds simple termination. Checked abstract and introduction, not all soundness hypotheses. [Primary paper](https://iris-project.org/pdfs/2025-oopsla-lilo.pdf).

Consequence: “a replacement preserves progress when linked with other threads” is not enough to identify a new theorem. The distinctive obligation is its derivation from the cylinder factorization/comparison construction, with actual observation and resource boundaries stated.

### Probabilistic drift under adversarial choice already has strong results

Chatterjee and Fu, *Termination of Nondeterministic Recursive Probabilistic Programs*, gives soundness and completeness of ranking-supermartingale methods for bounded expected termination time over all schedulers, and separate almost-sure/tail results under additional hypotheses. Checked primary abstract. [Paper](https://arxiv.org/abs/1701.02944).

Related termination work also includes lexicographic supermartingales and state-dependent almost-sure progress rules. Thus finite expected time, geometric tails, and almost-sure completion must remain distinct. A local drift statement must be conditional on the actual selected action and history; isolated marginal drift can be invalid under adaptive scheduling.

### Scheduling plus Lyapunov drift is also queueing theory

Neely's work on queue stability distinguishes rate stability, expected time-average bounds, and probability-one time averages, using appropriate drift and moment hypotheses. Its scheduling literature constructs policies by optimizing bounds on conditional drift. Checked primary abstracts and author-hosted scheduling notes. [Queue stability paper](https://arxiv.org/abs/1008.3519), [author's network optimization notes](https://ee.usc.edu/stochastic-nets/docs/network-optimization-notes.pdf).

Consequence: a scheduler selected to make an aggregate potential decrease is a baseline control construction. Queue stability is not finite-mission completion: a stable system with endless arrivals need never empty, and a backlog bound alone does not guarantee every named job is served.

## Terminology and quantifier checklist (our framing)

* **Deadlock freedom:** absence of a reachable nonterminal configuration with no useful enabled move. This does not rule out livelock or starvation.
* **Starvation freedom:** each relevant pending operation eventually completes under stated environmental/scheduler conditions. Distinguish pathwise from almost-sure versions.
* **Lock freedom:** system-wide progress, allowing one operation to starve; not sufficient for a mission requiring all jobs.
* **Wait freedom:** every operation completes within an appropriate bound on its own steps, independent of other threads' speeds; a physical-time bound still needs service assumptions.
* **Weak fairness:** continuously enabled actions eventually execute. **Strong fairness:** actions enabled infinitely often eventually execute. An always-enabled polling instruction is not an always-available lock acquisition.
* **Chosen-scheduler result:** a concrete controller succeeds. **All-scheduler result:** every scheduler in an explicitly defined class succeeds. The former does not establish the latter.
* **Local service steps:** steps actually advancing that module. **Global ticks:** include other modules, failed polls, and scheduler overhead. **Invocation count:** completed/called excursions. **Wall-clock time:** additionally needs a physical cost model. State the clock in every estimate.
* **Finite mission:** terminal predicate and no unbounded new arrivals/reactivation unless their budget is included. Individual call termination does not terminate a perpetual dispatcher.

These distinctions are definitions/checks for the proposed work, not claims of literature novelty.

## Why the serial summary provably lacks information

Consider two isolated deterministic modules with identical outputs and total duration, each acquiring two locks and releasing them before returning. One acquires A then B, the other B then A. Their isolated duration/exit summaries can agree exactly. Running both together may reach a state where each holds one lock and waits for the other. A same-order pair does not have that circular-wait execution. Internal padding can equalize isolated durations if needed.

This is an obstruction to the **chosen observational interface**, not impossibility of concurrent completion: a scheduler that serializes whole invocations can avoid the state. If the mission permits serialization, claiming mission incompatibility would be unwarranted. A genuine concurrent target must state why overlapping execution is required or what concurrency-sensitive comparison is being established. Likewise a lock-order repair is a valid solution but not a new concurrency theorem.

## Exact interface/reconstruction acceptance tests

1. Specify a local action alphabet and retained resource boundary: request/grant/release, visible state, and any persistent noise needed for conditional validity. Do not infer independence from isolated tests.
2. Give an actual scheduler algorithm using only that retained information. Show its resource safety and service/obligation guarantees from local conditions. If it examines hidden implementation state, implementation independence has failed.
3. Define operational assembly from local kernels and the scheduler; prove finite-prefix evaluation equality or inequalities. This is the step that makes the joint cylinder honest rather than an assumption.
4. Explain precisely which preparation/test rows record progress and interference. Test equality only transports the evaluated rows actually present; it does not turn a formal factorization leg into a stochastic simulation.
5. Prove the actual comparison respects scheduler observations and resource actions. Exact action-indexed operational intertwiners are a useful sufficient baseline; do not claim arbitrary free-Isbell legs carry them.
6. For regrouping/reassociation, retain one scheduler or give an explicit scheduler translation. Independently round-robin scheduling nested groups changes service rates and path laws; categorical coherence cannot equate these without a justified comparison.
7. Use progress to justify the infinite limit, not a presupposed normalized global path law. A finite-prefix equality alone need not give the quantitative clock bound desired.
8. Separate exact realization invariance, monotone certificate refinement, and physical implementability. Resource forgetting may require weaker bounds or lose admission; that is not failure of the refinement law if the new observation regime is explicitly changed.

## Honest likely deliverable

A strong scoped result would provide resource-action enriched cylinders plus a specific scheduler construction; prove that locally certified operational representatives assemble to a joint cylinder with a derived progress estimate; then use the existing genuine comparison calculus to show the estimate and admitted scheduler behavior are invariant under the specified replacements. Include the serial-summary counterexample and an example retaining real interference rather than only hidden serialization.

If the work proves only the stochastic scheduling/drift lemma and an equality of already assumed full joint laws, label the categorical bridge unfinished. If it proves the above derived assembly/comparison law, call it a new result within this project, while leaving publication novelty open pending a more exhaustive comparison with concurrency refinement and coalgebraic/probabilistic process semantics.

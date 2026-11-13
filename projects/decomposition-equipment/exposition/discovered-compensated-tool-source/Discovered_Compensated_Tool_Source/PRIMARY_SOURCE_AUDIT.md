# Prior-art audit: discovering a compensated repair-station interface

**2026-11-02. Scope:** one finite illustrative application, not a novelty claim or a new research contract. Primary sources checked before developing the example. This audit concerns the proposed model with a hidden fixed binary coupling vector, safe dummy probes, and a guarded commit. It does not establish physical robot safety.

## Executive judgment

The example should be presented as an **application and synthesis of established mathematics**, not as a new learning or compositional-verification algorithm. The most important distinction is between (a) learning enough about a fixed, stipulated class to certify a particular surrounding activity and (b) discovering that the actual world belongs to that class. The model supplies (b).

The stronger motivating claim is not that the robot discovers two independent subsystems. It discovers a **compensated interface**: some combinations of interfering work have a predictable joint effect even when each individual effect remains unknown. That permits useful work without full identification. This is a worthwhile, explicit demonstration of the programme, not evidence of a generic gap in existing verification methods.

## 1. Active learning and learned assumptions: already directly applicable

**Angluin (1987), _Learning Regular Sets from Queries and Counterexamples_.** [Primary paper](https://homepages.math.uic.edu/~lreyzin/papers/angluin87.pdf), [DOI](https://doi.org/10.1016/0890-5401(87)90052-6).

L* learns a regular language using membership queries and a teacher that checks conjectures and returns counterexamples. Its exact-learning guarantee is not a guarantee from an arbitrary finite observational record. For the proposed application, the known finite linear family and exact query response replace the general teacher mechanism. We should not describe finite probes alone as generally identifying safe behavior in unseen contexts.

**Cobleigh, Giannakopoulou and Pasareanu (2003), _Learning Assumptions for Compositional Verification_.** [NASA primary preprint](https://ntrs.nasa.gov/api/citations/20030017771/downloads/20030017771.pdf), Sections 3–5, especially Theorem 1.

This is the closest architectural baseline. Finite-state components and a safety property are analyzed by learning environmental assumptions. Model checking implements membership/conjecture answering; the resulting assumption is checked against the environment. Theorem 1 gives correctness and termination. The weakest assumption characterizes environments that preserve the property, but the algorithm can terminate before learning that entire assumption. Thus **learning only enough for the current composition is already part of the baseline**. Our model offers a closed-form, experiment-driven instance, not a new general assume-guarantee principle. Its actual physical probe oracle must be separately justified; model checking a supplied transition system does not supply that justification.

## 2. Frame rules and inferred specifications: do not mistake compensation for disjointness

**Calcagno, O'Hearn and Yang (2007), _Local Action and Abstract Separation Logic_.** [Author-hosted primary paper](https://www.cs.ox.ac.uk/people/hongseok.yang/paper/asl.pdf), Section 3.

Local actions over separation algebras support abstract frame and concurrency rules. The paper relates frame-rule soundness to safety monotonicity and the frame property; these are conditions on the action semantics, not conclusions of isolated testing. For this example, individual background actions deliberately alter shared state. Ordinary disjoint-footprint framing therefore does not establish the desired claim. A proof can instead use a shared invariant recording the accumulated joint effect, or verify the compensated composite action. This is not a refutation of separation logic, nor does it establish a new generalization of its frame rule.

**Calcagno, Distefano, O'Hearn and Yang (2009), _Compositional Shape Analysis by Means of Bi-Abduction_.** [Primary paper](https://www.cs.ox.ac.uk/people/hongseok.yang/paper/popl09.pdf), [author/institution publication record](https://www.cs.ox.ac.uk/publications/publication4984-abstract.html).

The paper already infers procedure specifications compositionally, independently of callers, using separation logic and bi-abduction. The verified abstract/author record is enough for this limited comparison; the PDF endpoint timed out during full-text retrieval. We make no detailed theorem claim from it. Inferring an interface is not itself new. The present application infers a parameter of unknown environment behavior from permitted experiments, rather than deriving a heap specification from analyzed procedure code.

## 3. Runtime assurance: a guard needs an actual safe alternative

**Pasareanu, Mangal, Gopinath and Yu (2023), _Assumption Generation for the Verification of Learning-Enabled Autonomous Systems_.** [Primary manuscript](https://arxiv.org/html/2305.18372v1), Sections IV–V and Appendix A.

The paper synthesizes weakest behavioral assumptions for autonomous-system safety and uses them as monitors. It explicitly distinguishes alphabets containing actual state from implementable alphabets containing only observable estimates. Its evaluated monitor models rejection as an abort state with no outgoing transitions. This closely matches the need to state precisely what our controller observes and what gate closure means. The application must not infer mission completion from safe refusal, or assume hidden changes are observable because a mathematical monitor mentions them.

**Mehmood et al. (2022 version), _The Black-Box Simplex Architecture for Runtime Assurance of Autonomous CPS_.** [Primary manuscript](https://arxiv.org/html/2102.12981v3), Definitions 3–5 and Theorems 2.1–2.2.

This stronger baseline does not require a statically verified baseline controller: a correct decision module maintains a permanently safe command sequence. Its safety theorem requires such a sequence initially and correct acceptance thereafter. Transparency has stronger hypotheses; safety alone allows rejecting everything. Runtime reachability still requires an accurate dynamics model. For our application, the closed gate and safe holding state play the role of a supplied fallback. They must not be inferred from successful probes or assumed physically available without qualification. Deadline completion needs its own proof.

## 4. Exact hypothesis map for the proposed instance (our derivation)

Let the true coupling be a fixed c in F_2^m during a declared epoch. Probes yield consistent evidence Ac=b. Let K={c:Ac=b}. An executed background word has recorded parity vector v. Its effect c·v is constant over K **iff v belongs to the row space of A**. If v=lambda A, the known correction is lambda b. Conversely, outside the row space there exists d in ker A with d·v=1; c and c+d agree on all recorded probes but require different corrections.

This is elementary finite-dimensional linear algebra. It is a sharp criterion **inside the given family and observation regime**, not a new theorem about arbitrary environments. It does not require learning c completely.

| Supplied premise | Why it matters / what cannot be concluded without it |
|---|---|
| Fixed known linear family; same c throughout the epoch | Finite evidence does not exclude nonlinear, delayed, or drifting alternatives. |
| Exact safe dummy probes and reset/initialization | The experiment oracle and safety of acquisition are not learned by the criterion. |
| All interfering operations are addressed and completely logged | The parity v must describe the actual execution, not merely the intended schedule. |
| Known correction action and safe closed gate | Knowledge of the required correction is not authority or ability to perform it. |
| No new production information about c before commit | Otherwise the evidence fibre must be updated; the impossibility witness could cease to apply. |
| Observable declared epoch changes | Epoch labels invalidate certificates only when their changes faithfully reflect the stipulated events; arbitrary silent drift is outside scope. |
| Explicit operation, probe, waiting, and correction costs | Safe refusal or later repair does not imply completion within budget/deadline. |

Adaptive clients are admissible only with their actual observation/evidence updates accounted for. A pending prefix can be uncertifiable even if the intended complete word is certifiable. Completing a partner operation may repair certifiability, but is extra work, not undo of the previous physical history.

## 5. Recommended claim and acceptance boundary

**Claim worth demonstrating:** permitted experiments can expose a reusable, task-relevant compensated interface, whose contextual guarantee depends on a joint constraint rather than separately identified operation effects. The same example should exhibit failure of isolated inference, safe guarded execution, and the cost of interruption or epoch invalidation.

**Do not claim:** new active learning, new assume-guarantee logic, discovery of physical independence, automatic safe experimentation, safety under unmodeled drift, or universal mission completion. Existing methods could verify this finite instance. The programme's value here is organizing and checking all the interfaces, evidence, retained joint possibilities, refinement boundaries, and operational costs in one worked example.

The earlier O5/O7 manuscripts were not available at their suggested local paths in this worker's filesystem. This audit therefore does not independently certify the proposed bridge to those manuscripts; that is a separate source-level check for the parent/integration worker.

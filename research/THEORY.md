# Distributed execution, continuation, and refinement

This is the semantic core for the full program contract, not a declaration of program completion. [Execution.lean](Execution.lean) checks nineteen general declarations. [core_model.py](core_model.py) implements the finite whole-prefix recurrence and independently replays extracted policies. The concrete digital, evidence/physical, and institutional instances must each discharge the adapters stated below; their successful local checks alone do not discharge that assembly.

## 1. Context and operational carrier

Fix a context \(\theta\): physical/protocol/institutional state, initial scenarios, identity and role interfaces, observation architecture, fault family, adversarial information and move order, time scale, mechanisms, and required behavior. A changed mechanism or admitted environment is a different context. All guarantees below are indexed by this data.

The checked core uses the dependent signature

\[
\begin{aligned}
I,X,F &: \mathsf{Type},\\
H,A &: I\to\mathsf{Type},\\
\mathrm{obs}_i &: X\to H_i,\\
\mathrm{correct} &: F\to I\to\mathsf{Prop},\\
\mathrm{Init} &: F\to X\to\mathsf{Prop},\\
T &: F\to X\to\left(\prod_{i:I}A_i\right)\to X\to\mathsf{Prop}.
\end{aligned}
\]

The Lean structure Model contains these fields. Initial membership in the admitted fault family is part of Init; excluded fault indices have no initial scenario. At least one admitted initial pair must be exhibited. The type \(F\) records a fixed unknown joint coalition and any fixed adversarial mode; it is not an input to correct actors. Components with different roles have different local-history and action types. A fixed identity universe may include inactive or spare identities; changing active membership is state, not a silent change in the quantified fault bound.

The state type is unrestricted by the signature. It can contain channel contents, protocol phase, physical variables, resource/capability mode, institutional state, pending inputs, and history. This does not assert that a chosen finite state is adequate for every system. It provides the carrier in which an adequacy argument is made.

For a primitive plant state \(Z\) whose current observations do not retain all relevant memory, take \(X\) to be its nonempty finite execution prefixes
\[
z_0,a_0,z_1,\ldots,a_{n-1},z_n.
\]
The next relation appends one legal action and plant successor. Actor \(i\)'s \(H_i\) retains its initial observation and successive pairs of its own action and next observation, with a locally readable round index in the synchronous specialization. This canonical history lifting preserves all primitive traces and their local indistinguishability by construction. A smaller memory representation requires a separate sufficient-compression or refinement argument.

A correct policy is the dependent product
\[
\pi:\prod_i(H_i\to A_i).
\]
For a global action profile \(a\), Follows means
\[
\forall i,\ \mathrm{correct}(f,i)\Rightarrow a_i=\pi_i(\mathrm{obs}_i(x)).
\]
The induced transition \(\operatorname{Step}_{f,\pi}(x,y)\) exists when some such profile satisfies \(T(f,x,a,y)\). The same policy is used for every admitted fault index. The theorem local_policy_factorization constructs such a policy from any issued-action table that is uniform across all admissible correct occurrences of each local view, using an explicit fallback on unused views. For finite operational prefixes this construction is an executable lookup table; the general theorem uses classical choice. The theorem action_uniform_across_faults proves that equal observations yield equal actions when the identity is correct in two different fault scenarios.

Fixed command alphabets include rejected/ineffective requests when the interface permits them. A policy does not return an action whose type silently depends on hidden state. Physical or institutional infeasibility is handled by the actual transition, explicit rejection/failure states, or an established uniform-feasibility condition. Normatively forbidden actions are not removed from the plant merely because they are forbidden; only an actual enforcement mechanism can exclude their effects.

The reference adversary may use the current global prefix and previously issued actions; it cannot use future choices. Byzantine components jointly select their action profile and the environment selects any admitted successor. Collusion and resource coupling belong to \(T\); they need not factor per actor. A less informed adversary is a separately indexed restriction, not something inferred from the word Byzantine. A transition relation used for a restricted adversary must represent that adversary's actual information and capabilities or be explicitly treated as a sound overapproximation. Environment admissibility is specified independently of whether the controller succeeds.

Nonblocking in the module means every action profile following the correct components has at least one modeled successor at every retained scenario. This is deliberately stronger than an empty-set safety implication. It requires a verdict for every actual command pattern. A rejected request may transition to a failure or no-effect state; rejection is not automatically safe or service-preserving.

Maximal finite executions are handled explicitly by an embedding: a successfully completed finite mission enters a marked terminal state with clocked stuttering, while unexpected deadlock/timeout enters a marked failure state. The mission's predicate distinguishes those labels. A recurring-service mission cannot reinterpret terminal stuttering as delivered service. If finite execution semantics are used directly instead, their completion/failure verdict must match this embedding before the infinite-run theorems are applied.

## 2. Whole-family continuation and compatible local prescriptions

Let \(K:F\to X\to\mathsf{Prop}\) be a nonempty family of possible prefixes. It carries the global alternatives, including fault identity; local actors still receive only their own observations. A prescription \(p\) has the same type as a policy and therefore gives one action to each actor/local-history class. Define the unpartitioned update

\[
\operatorname{Post}(K,p)(f,y)
\iff
\exists x,\ K(f,x)\land \operatorname{Step}_{f,p}(x,y).
\]

All admitted successors remain together. The update does not choose the analyst's actual world, intersect independent known-fault winning sets, or synthesize unrelated continuations after splitting alternatives that an actor cannot distinguish. The property that a prescription depends on the entire family is an offline synthesis fact: the resulting table is computed once and actors execute its local entries.

For a safety predicate \(S(f,x)\), the finite-horizon recurrence is

\[
\begin{aligned}
W_0(K)&\iff \operatorname{Live}(K)\land K\subseteq S,\\
W_{n+1}(K)&\iff \operatorname{Live}(K)\land K\subseteq S
\land\exists p:\operatorname{NB}(K,p)\land W_n(\operatorname{Post}(K,p)).
\end{aligned}
\]

The checked theorem winning_iff_plan proves equivalence with a length-\(n\) sequence of prescriptions whose successive whole-family updates are nonempty, safe, and nonblocking. This is an exact recurrence at the stated horizon, not a necessary-condition approximation. For finite explicitly represented arenas, core_model.py enumerates all assignments to the occurring actor/local-history classes and all legal Byzantine profiles and successors. It returns a plan only after recursive acceptance of the complete successor family, then replays that plan independently. The algorithm is complete for its finite arena/horizon; it is not claimed to decide unrestricted distributed synthesis.

A sequence of round-indexed prescriptions is not automatically a single permitted policy. The Clocked structure requires a time map on states, an actor-computable clock on each local history, initialization at zero, and one time increment per transition. The compiler is
\[
\pi_i(h)=p_{\mathrm{clock}_i(h),i}(h).
\]
Theorems execution_time and compile_run_iff prove exact equality of the generated run classes under the prescription sequence and compiled local policy. An unobservable stage number cannot be supplied by the analyst to satisfy this hypothesis.

For an infinite prescription sequence, Reach iterates Post. Theorems run_in_reach and prescription_safety establish that every admitted run is represented at each depth and inherits the family's safety predicate. Conversely, membership in a reach family has an actual generated finite execution witness. The checked theorem reach_iff_generated proves both directions: at depth zero use the initial witness; at a successor depth, extract the predecessor and action witnesses from Post, apply the induction hypothesis, and append that legal step. The reverse direction follows by the same execution-length induction. Thus retaining all prefixes is an exact representation for these trace queries, not just a coverage estimate.

Under a nonempty safe invariant, nonblocking and transition closure construct an actual infinite run. The theorem infinite_run_exists makes this construction explicit; classical choice selects environmental successors, not a hidden-state-dependent controller. Nonblocking also shows that no retained finite prefix is stuck. Arbitrary admitted causal action choices remain covered by the universal transition closure; existence of one run is not being substituted for safety of all runs.

### Infinite-horizon characterization and its limits

In the general synchronous history model, an infinite safety policy exists exactly when there is an infinite compatible chain of safe finite local tables. Forward direction restricts one policy to increasing history depths. Reverse direction takes the union of the compatible tables and uses the local clock to select its depth entry; the preceding reach/compilation arguments preserve every admitted run. This is a recursive organizing object with a policy transport, not merely renaming an existential winning policy.

When actors, local observation alphabets and action alphabets are finite, with nonempty command alphabets and histories explicitly indexed by their observable length, each level has finitely many possible local history strings. At level \(n\), list all such strings and all action assignments to them; include a fixed default on unlisted/impossible strings. The finite Cartesian product lists every possible depth extension. Keep exactly those extensions for which the whole-family recurrence succeeds. Prefix restriction preserves successful shorter tables.

Consequently these finite tables form a finitely branching tree. If \(W_n(\mathrm{Init})\) holds for every \(n\), the tree has nodes at every depth. The checked theorem infinite_path_of_finite_extensions supplies an infinite path in any such finitely branching tree. Its specialization to the safe-local-table tree is the explicit hand derivation in this paragraph; that table-tree encoding is not separately mechanized. The supporting finite_persistent_choice proof selects a child with arbitrarily long extensions: if each of finitely many children had a failing finite bound, their maximum would bound the parent's depth, contradiction. The reverse implication is immediate by restriction. Therefore, in this explicitly stated class,
\[
\forall n\,W_n(\mathrm{Init})
\quad\Longleftrightarrow\quad
\exists\text{ one infinite safe local policy}.
\]

This argument does not require a finite physical state space, but finite representation of each recurrence test is an additional algorithmic requirement. The compactness result is classical existence; it supplies neither a terminating decision procedure nor a finite-memory controller. The nonconstructive extraction boundary remains visible.

The finite-branching assumption cannot simply be omitted from this proof. Suppose an initial command selects any natural fuel \(N\), after which the plant forcibly decrements it each round and fails below zero. Every finite safety horizon can be met by selecting sufficient fuel, yet every chosen \(N\) eventually fails. The checker replays horizons 1–100; the general obstruction is the arithmetic fact that the chosen finite fuel fails within \(N+1\) decrement steps after selection, not the bounded enumeration.

The closest prior construction is epistemic tracking, which likewise retains compatible prescriptions and may be infinite; a proposed bisimulation quotient does not inherit its strategy guarantees. The present module is a local checked reconstruction/adapter for the program's fault-indexed carrier, not a novelty claim. [Berwanger–Kaiser–Puchala, Sections 3–4 and 6](https://drops.dagstuhl.de/storage/00lipics/lipics-vol013-fsttcs2011/LIPIcs.FSTTCS.2011.387/LIPIcs.FSTTCS.2011.387.pdf)

## 3. Service and state-versus-trace safety

Safety does not imply progress. Fix a positive integer service window \(q+1\) in the declared transition-time scale. Let the history monitor age be zero initially, reset to zero on a service transition, and increment on every non-service transition. By induction, age is exactly the length of the most recent service-free suffix. Hence age \(\le q\) at every prefix is equivalent to the absence of \(q+1\) consecutive non-service transitions. The theorem bounded_service proves that the bounded monitor forces a service event within every such future window.

This converts a bounded service obligation into safety on the augmented state, while retaining the same policy. It does not convert arbitrary eventuality into an invariant or preserve elapsed-time deadlines under arbitrary stuttering. A variable-duration execution needs a clock/elapsed-time monitor and its own finite-representation or analytic argument.

The checker compares the state and trace presentations over all 256 eight-event service sequences for window four. It also exhibits histories ending with the same current physical observation and current service flag but different breach verdicts. Forgetting the age/history monitor therefore changes the consumed judgment. Every monitored state must arise from the prescribed update; independently assigning an age variable is not evidence that the trace property holds.

Bounded-synthesis prior art already keeps implementation tables outside the faulty-set quantifier while allowing fault-indexed proof certificates. Its fixed-bound completeness and increasing-bound semiprocedure do not establish unrestricted finite-memory decidability here. [Bloem–Braud-Santoni–Jacobs, Section 3, Theorem 1 and Corollary 1](https://finkbeiner.groups.cispa.de/publications/BBJ16.pdf)

## 4. Local strategy and trace refinement

Let \(C\) be a concrete model and \(A\) an abstract one over the same global fault index and actor universe. A role change may be represented in state with a fixed universe of active/spare identities. A different fault/identity index requires an explicit reindexing adapter before these fixed-index results apply.

A refinement contains a state projection \(\alpha:X_C\to X_A\), local history maps \(h_i:H^C_i\to H^A_i\), and local action lifts
\[
\ell_i:H^C_i\to A^A_i\to A^C_i.
\]
The implemented policy is
\[
\pi^C_i(h)=\ell_i(h,\pi^A_i(h_i(h))).
\]
Neither map receives the true faulty set or global state. Observation compatibility requires \(h_i(\mathrm{obs}^C_i(x))=\mathrm{obs}^A_i(\alpha x)\).

The analytic action-profile projection may inspect the global state and fault index, because it proves correspondence of runs rather than implementing an honest actor. It must map concrete profiles following the lifted policy to abstract profiles following the abstract policy. Every actual concrete successor must project to an abstract successor; initial scenarios must project to initial scenarios. These are the fields of Refinement, and they are application obligations, not tautologically satisfied by naming a map.

Theorem refinement_maps_run proves:
\[
\mathrm{Run}_C(f,\ell(\pi),r)
\Rightarrow
\mathrm{Run}_A(f,\pi,\alpha\circ r).
\]
With an explicit property decode
\[
\Phi_A(f,\alpha\circ r)\Rightarrow\Phi_C(f,r),
\]
refinement_transports_property transports the abstract guarantee. The time indices are identical in this theorem. It therefore transports a service window only when that index has the same service/time meaning on both sides.

The checked composition composeRefinement composes state projections, actor-local history maps, local action lifts, and analytic action projections. The resulting honest action still depends only on the corresponding concrete actor's history. This supplies an actual composition law for assembled workstreams.

The theorem does not manufacture concrete runs: nonempty initialization and concrete nonblocking remain separate and must be proved for the selected implementation. Nor does it establish physical fidelity from sampled trajectories. A continuous implementation needs a decoded trajectory for each discrete execution plus a tube/solution theorem, as in the selected delayed-control construction.

Feedback refinement provides established source-level machinery for input and successor preservation, but its centralized quantizer does not automatically implement separate local maps. The present adaptation exposes that additional obligation and checks its trace consequence. [Reissig–Weber–Rungger, Definitions V.2/VI.2 and Theorems V.4/VI.3](https://arxiv.org/html/1503.03715)

## 5. Required instance adapters

The remaining program assembly uses the following explicit consumers. These are not marked discharged merely because this file names them.

| Instance | Source and abstraction | Required preservation and non-vacuity |
|---|---|---|
| Digital ledger | Operational signed-message/decision/attestation prefixes to committed values and prefixes. Local maps retain verified receipt, round and own actions. | Initial/step correspondence, no unavailable signatures, agreement/validity/service, terminal-certificate conflict exclusion in unfiltered reachable prefixes, epistemic projection of the same events. |
| Witnessed physical control | Timestamped reports with witness constraints and a committed input FIFO to fault-labelled effect-time envelopes and safe control intervals. | Joint-fault coverage, control-relevant precision, local interval endorsement and support collection, nonempty selection, exclusive realized input, continuous tube and service-rate decode. |
| Institutional recovery | Normative state, installed credentials/configuration, physical isolation/capacity, duty history and actual events. | Power and permission remain separate, unauthorized effects remain expressible, current/historical verifiers differ, mode/configuration transitions preserve the common invariant and actual service. |

A single physical world may have digital, epistemic and institutional projections. Their maps preserve different queries and need not be inverses. Knowledge quantifies over same-view alternatives; controllability quantifies over local strategies and adversarial continuations; permission follows the stipulated institutional transition rules. Keeping the common execution carrier does not equate these quantifiers.

The existing missed-report, duplicate-effect, stale-evidence, hidden-fault and continuation counterexamples are regression tests for these adapters. A proposed map that erases a required queue, epoch, shared fault, or historical monitor must either fail the test or state and prove a changed guarantee. Such failures constrain the theory; they are not reasons to suppress the original executions.

## 6. Verification state

The nineteen Lean declarations compile with only the allowed logical foundations. The finite checker confirms the intended quantifier distinctions: one safe step can fail to extend under hidden information; per-fault policies can exist without one unknown-fault policy; a deadlocking command is rejected despite vacuous successor safety; service monitors retain a trace distinction; and finite-horizon success with infinite action choice does not imply an infinite policy.

The finite recurrence and Lean proofs are coordinator-authored first-pass results until independent semantic review checks their interpretation and adapters. Program closure additionally requires the completed instance constructions and the P1–P16 audit. The active Goal is not complete.

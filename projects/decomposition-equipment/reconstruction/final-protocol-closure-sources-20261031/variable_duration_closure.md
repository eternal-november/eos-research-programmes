# Resumption protocols: variable-duration calls and coherent cut reconstruction

31 October 2026. Scoped operational theorem and proof. This extends the token-context checkpoint by changing the observed primitive from a completed invocation to one charged resumption step. It does not claim new general concurrency theory or an operad action on arbitrary Isbell objects.

## 1. Fixed language and acceptance criteria

We fix a finite typed decomposition tree. Each node has a countable private persistent state. That state may contain a finite stack over a countable frame alphabet, suspended callers, program counters, persistent child-session identifiers, and an unbounded finite interaction history. Thus the set of states remains countable; neither call duration nor attained stack depth is uniformly bounded. The finite *decomposition depth* is distinct from dynamic stack depth. Recursive calls to procedures inside a node are local stack transitions; recursion does not grow the decomposition tree.

A boundary is a countable resumption protocol. Inputs include declared start, resume, manager grant/busy, intervention and cancellation commands. Outputs include running, resource request/effect, yielded, returned(value), and refusal/error. The exact command alphabet is fixed before execution. Illegal commands receive an explicit normalized refusal/error behavior, not an undefined transition. Session and continuation tags distinguish simultaneous pending invocations when admitted. A basic stack discipline may allow one pending invocation per worker slot; the general countable-state semantics does not presuppose reentrancy.

One root microtick executes exactly one charged primitive instruction, or an explicit idle/busy/terminal instruction. Every actual call-push, local work instruction, resource transaction, and return-pop costs one microtick. A push records the callee entry and suspends the caller; it does not execute the callee body on that same tick. A return records the result and enables the caller continuation; it does not execute that continuation on that tick. Repeated child calls and loops therefore require repeated charged instructions. Returning from a compound invocation can take arbitrarily many microticks and may never occur.

Finite-depth routing to the selected instruction, copying declared event fields, and recording that instruction's outcome are structural bookkeeping. They add no independent computation or tick. In particular no randomized loop, procedure evaluation, resource acquisition, or call execution is hidden in routing. A user implementation needing nontrivial routing computation must represent it as charged local instructions. We make no real-hardware wall-clock claim beyond this fixed instruction clock.

A concrete normal form for routing is: at each ancestor, a deterministic read-only selector, using its persistent control state and current boundary input, chooses either its own next charged instruction or a child resumption and its supplied input. At the selected node a normalized countable kernel executes one instruction. Ancestors then perform deterministic finite record/control updates from the returned microstep event. These updates can record that an already charged call returned, but cannot execute the next caller instruction. No random choices occur in routing; a scheduler needing randomness first takes an explicit charged scheduler instruction and records its decision. This restricted normal form is sufficient for the theorem and progress family.

There is ONE authoritative resource manager. Requests, grant/busy responses, ownership changes and releases crossing a reconstructed boundary are explicit protocol fields at their actual microticks. A simultaneous acquire/grant transaction is allowed only under a fixed protocol exposing the pending action before the tick; the root manager computes the grant from its ownership state and commits the corresponding single action. Otherwise request and reply are separate charged instructions. Child nodes never duplicate authoritative ownership. Scheduler state is likewise explicit and retained by a designated node. No reassociation replaces its actual schedule by a new one.

A component can suspend while another component is scheduled. Unselected components have no private transition. If global time is an input observable to a component, its next resumption input includes elapsed time; if it can autonomously evolve every tick, those evolution steps must instead be scheduled explicitly. This language does not silently allow hidden clocks or hidden autonomous resource changes.

Fix a countable declared family of public preparation labels and countable imposed finite control experiments; all countable-carrier assertions below refer to this family. A larger preparation class can be treated pointwise, not falsely asserted to have a countable tagged coproduct. All primitive initial private states are independent conditional on a retained public preparation label. Innovations at charged steps are private and fresh conditional on state/input. Shared sources must be explicit protocol nodes. Interaction across a subtree boundary is exclusively through its declared protocol. These are structural information-flow premises, not an assumption that reconstructed systems already compose.

### What counts as success

(A) Construct normalized finite-prefix laws and actual substitution maps without assuming return. (B) Preserve open and suspended histories under every cut. (C) Obtain a separate derived progress witness for genuinely nested variable-duration calls. (D) State failures when scheduling, resources, or nonreturn are hidden. The independent progress companion supplies (C); this note proves (A)-(B).

## 2. Positive microstep semantics and substitution

A routed microstep visits a finite ancestor chain and exactly one charged instruction. The normalized leaf/local instruction kernel, together with deterministic routing/updates, induces a normalized countable kernel on the product of persistent node states. If an instruction has countably many outcomes, its induced global outcomes are their deterministic images; total mass is one. No invocation is run to completion to define this kernel.

For substitution C[D_1,...,D_n], take the product of all persistent states, including pending calls and stacks. Replace each requested hole resumption with routing into the corresponding D_i; execute precisely its selected instruction. Expanded execution retains every intermediate boundary input and microstep output. Finite tree depth guarantees the structural route finishes. Private countable state spaces and finite products preserve countability.

The flattened kernel is obtained by summing the instruction outcomes yielding each global state/output. Parenthesization changes only the grouping of node-addressed state tuples and routing records. Every fully expanded microstep record names the same selected instruction, same incoming data, same primitive random factor, and same node updates. Consequently the canonical tuple/record bijection intertwines the two normalized kernels. Unit contexts are transparent structural wires, introducing no instruction, session, clock tick, or randomness. Symmetry merely relabels ports. Associativity, unit and equivariance diagrams commute because each canonical map sends a record to its unique node-addressed normal form.

Thus these resumption contexts have substitution coherent up to specified state/record isomorphism. This is semantic: kernels and their entire expanded finite paths intertwine, not merely syntax trees. Compilation preserves charged ticks; a nontransparent wrapper is not a unit. Scheduler decisions are part of the node state/instructions and survive substitution unchanged.

A flat numeric kernel can marginalize internal records. The expanded paths used here belong to the actual given implementation tree. We do not reconstruct a hidden internal log from an arbitrary black box having the same outer kernel.

## 3. Macro calls are first-return observations, not atomic kernels

Fix a declared enclosing controller/input policy pi and its entry state/preparation, including the scheduler and manager; alternatively fix a controlled experiment. For a tagged invocation begun by a charged start instruction, let tau be the number of GLOBAL charged ticks from its start through its matching return (under a stated inclusive endpoint convention), with tau=infinity if absent. Outside ticks while it is suspended count toward this wall-clock duration. An intrinsic own-service duration instead counts only its successful instructions and is a separately marked observation, never implicitly identified with tau. At finite horizon retain the complete prefix, including resource events and an explicit pending/returned status. Normalized microstep laws give normalized finite-prefix distributions even if Pr(tau=infinity)>0. Consistency follows by summing the last normalized step.

The finite-return kernel F_pi(d,z | entry) is the sum of path probabilities under that fixed policy/controller whose first matching return has duration d, with marked return z. Its dependence on pi cannot generally be omitted: entry alone does not determine wall-clock return under changing schedules or interventions. It is substochastic:

    sum_(d,z) F_pi(d,z | entry) = Pr_pi(tau<infinity | entry) <= 1.

Its missing mass is Pr(tau=infinity). The invocation law is never divided by this total. Moreover F alone is NOT an adequate compositional interface when an exterior observer can see intermediate resource effects or schedule other work while the invocation is pending. The primary semantics remains the controlled resumption-prefix law; F is a derived observation.

For a deterministic imposed boundary input word u_1,...,u_n, the subtree controlled law p_v(o_1,...,o_n || u_1,...,u_n;a_v) is obtained from its normalized microstep kernels. It includes all running/effect/return/refusal outputs. Interventions are imposed inputs, not conditioning on naturally selected future commands. A declared idle response handles resumption inputs in quiescent states. An outside scheduler choosing not to resume the subtree contributes an outside tick and no fictitious private transition; elapsed external time, when relevant, enters explicitly on the next input.

Every charged step advances integer time, so infinite instruction execution has infinite elapsed time. There are no zero-time operational cycles. Transparent structural routing is finite and acyclic for each tick. Permitting instantaneous recursive routing would violate this language and require a separate semantics; this is a boundary, not an unproved termination premise.

## 4. History realization with pending calls

For positive controlled prefix h define

    H_v(o | h,u) = p_v(h,(u,o))/p_v(h).

For zero denominator choose any normalized continuation. States are preparation-tagged finite histories, hence countable. A pending invocation is represented by its unmatched start/session tag and observed running/resource prefixes; it is not collapsed into a returned macro-event. A history state can persist forever without a matching return. Resource state not determined by this boundary history must remain in its authoritative exterior manager, not be invented inside H_v.

The following conditional-sufficiency statement is DERIVED. Fix a complete exterior record e, including its private current scheduler/manager state and past, immediately before the next subtree response. It includes the selected resumption input, but not any post-response exterior state or future private tape. For any compatible internal path x and fixed boundary transcript h, grouping primitive factors yields

    weight(x,e;h) = interior_weight(x;h) exterior_weight(e;h).

An exterior instruction contributes a factor depending on internal execution only via its declared boundary transcript. An interior instruction contributes a factor depending on the exterior only through supplied inputs. Suspension contributes no interior factor. Deterministic routed updates are indicators obeying the same separation. There is no requirement that h contain a completed call; this argument applies at every open prefix.

Summing over x and cancelling the positive exterior factor gives

    Law(next subtree microstep output | h,e,u) = H_v(-|h,u).

The same argument remains valid after replacing any disjoint subtrees by their history machines: they also use private innovations and communicate only through boundary messages. Off-support extensions cannot become reachable in a positive global path, by the displayed conditional law. This is the essential compatibility proof; normalized isolated macro return laws would not suffice.

## 5. Actual path maps and coherence at cuts

A tree cut is an antichain meeting every root-to-leaf path. For cut F replace each subtree rooted at v in F by H_v, retaining every original context above F, including its actual scheduler and resource authority whenever above the cut. If the cut encloses the manager, its entire visible effect on the exterior is retained in the cut boundary transcript. No invisible manager copy is inserted.

Let X_T be the countable disjoint union of all experiment-tagged finite expanded paths of the original tree. Experiments specify the retained preparation label, global horizon n, and imposed outer controls. Include initialized, well-typed, history-consistent syntactic paths of probability zero. Record all node-boundary events, including running and local-no-child outcomes, selected/suspended status, charged tick and current session tags. The observable trace includes every externally declared resource effect and elapsed-time mark.

Let X_F be the analogous expanded path carrier for the cut network. The deterministic map q_F forgets all below-cut private states and logs, preserves all above-cut states/events, and accumulates each cut node's actual boundary history including unfinished sessions. Tick positions and unselected exterior steps are unchanged. Induction over global ticks, using Section 4 at a selected subtree and the unchanged exterior kernel otherwise, proves

    (q_F)_* p_T^e = p_F^e.

This preserves the joint exterior private-state law, not merely root returns. If F refines G, define q_FG by the same forgetting and accumulating operation. Subtree cylinders remain the original cylinders by the same induction, so

    (q_FG)_* p_F^e=p_G^e,
    q_FG q_F=q_G,
    q_GH q_FG=q_FH,   q_FF=id.

The last identities are literal normal-form record identities, including pending histories and zero-probability syntactic paths. Forgetting twice never restarts a pending call or loses an elapsed tick. Common refinements handle incomparable cuts. Node-addressed compilation bijections commute with q because they neither change node boundaries nor ticks. Horizon restriction commutes pathwise but reindexes experiments/tests; it is not automatically an arrow of a single unchanged factorization category.

A possible misleading implementation is to instantiate a fresh history state at each resume. This is NOT q: it loses suspended histories and is ruled out by persistent history-state accumulation. Likewise replacing a complete-call return law for H_v loses intervening events and is not the theorem.

## 6. Same-cylinder factorization and two-sided comparison

Fix the same countable outer experiments e and a specified countable separating test family t: singleton finite outer-trace indicators, together with countably many named tick/resource/running/return/terminal predicates and total mass. We do not index the matrix by all subsets of a countable prefix set. Equality on singleton traces establishes equality of the entire discrete prefix laws and hence of arbitrary measurable prefix predicates separately. Let b_F^t be the corresponding indicator on X_F. Since q preserves these traces,

    b_G^t q_FG=b_F^t,
    r_(t,e)=b_F^t p_F^e

is independent of the cut. In a chosen small countable nonnegative matrix category containing these actual objects/maps, every q_FG is an actual arrow in Fact(r). It is not merely equality of unrelated marginal distributions.

The existing source-changing Isbell normalizer construction now sends q_FG to a canonical comparison cell between

    JX_F <-M0 G_F ->E0 R_r
    JX_G <-M0 G_G ->E0 R_r.

Functoriality/orthogonality gives G(q_GH)G(q_FG)=G(q_FH) and identity coherence. Thus reconstruction at cuts and compilation by context substitution have coherent comparisons for this actual joint cylinder. No canonical apex is asserted positive, executable, finite, or a stochastic resource manager. No assumption of full operational CFS lifting is needed.

Exact finite-prefix equality also gives equality of eventual-return probability: {tau<=n} is a finite-prefix event and its increasing union is {tau<infinity}. Nonreturn probability and any derived tail bounds are therefore preserved. This does not require a countable carrier of all infinite paths.

## 7. Sharp limits and scope

1. Schedulers are observable semantics. Nested RR A,C,B,C,... and flat RR A,B,C,... differ already on short scheduling traces. Associativity rebrackets the same scheduler, never substitutes one for the other.
2. Completed calls hide resource incompatibility. Two workers can have equal isolated total duration/output yet acquire locks in opposite orders, yielding deadlock when interleaved. Even finite calls suffice: one component acquires r on tick 1, releases on tick 2, then returns on tick 3; another idles on ticks 1 and 2 then returns on tick 3. They have the same delta_(3,done) return law and empty final holdings, but a waiter interleaved between their ticks observes busy versus grant. Equal macro laws do not imply equal controlled resource-prefix laws.
3. Missing finite-return mass is not successful return. A process returning after one tick with probability 1/2 and otherwise looping forever has finite-return mass 1/2. Conditioning on return fabricates a surely returning process. More strongly, a component acquiring r then looping forever and one idling forever both have zero finite-return kernel and nonreturn mass one. A waiter for r nevertheless sees different behavior. Adding a single divergence bit to a completed-call interface does not recover the missing prefix effects.
4. Independent private sources are substantive. A context retaining a fair private bit Z and a component outputting that same hidden Z cannot be replaced by an independent fair output merely because isolated output marginals agree. Either expose the source/correlation or establish the stronger conditional law directly.
5. All charged instructions have positive duration. Instantaneous recursive routing and zero-time Zeno runs are excluded explicitly, not erased by normalization. Genuine physical variable-cost instructions require additional cost labels and estimates; this theorem's variable durations are unbounded counts of real charged microsteps.
6. Arbitrary environment interference, hidden clocks, duplicated managers, and changed schedulers are not covered. The reconstruction is exact and potentially infinite; discoverability, finite evidence and physical implementation remain separate obligations.

The result is the fixed bounded extension: variable-duration open calls, actual coherent cut comparisons, a separately derived progress family, and counterexamples to unlicensed stronger readings. It is not a proposal for another extension.

# Discovered assurance frames: scoped theorem candidate

29 October 2026. Pre-experiment mathematical draft. This is not a novelty or efficiency claim. In particular, generic assume-guarantee composition, automaton minimization, version-space learning and incremental verification are established mechanisms. The candidate contribution must be an effective interaction between **discovered recursive interfaces, retained joint uncertainty and justified replacement frames** in an independently accepted family.

## 1. Supplied semantics versus discovered structure

Supplied: finite port/action alphabets and finite observation bins; causal timing and unit meanings; physical calibration/dynamics envelopes; a finite effective universe M of possible subsystem mechanisms; permitted observer/interface programs Q with explicit memory, read permissions and budgets; safe diagnostic protocols; permitted replacement and controller languages. A mechanism includes its persistent parameters, initial-state relation, joint innovation law and causal update. Shared innovation occurrences and persistent unknown parameters may not be independently recopied. Physical semantics are not inferred from correlation.

Not supplied: actual mechanism; actual input scopes, source-sharing partition, memory quotient, useful exported assurance state or valid replacement frame. The family can restrict these structurally without supplying their values. Q contains bounded transducers and primitive claim adapters, not an oracle for whole-environment verification.

A physical mechanism may be infinite-state outside its finite record interface. Its relation to that interface is a supplied/checkable simulation envelope. Unobserved physical hazards cannot be validated by the record fit.

## 2. What a discovered interface actually certifies

For a candidate set K subset M, an assurance interface I is a finite executable causal transducer q of raw records, a boundary alphabet B, and the following **uniform witnesses** checked for every m in K:

1. A relation R_m between concrete source/physical states and the transducer state. Its initialization and update commute for every permitted action and every source outcome on the declared context domain D. Observer updates, not only one-step predictions, must descend. The deployed transducer cannot read m or a hidden selector.
2. Primitive typed exports (not final whole-system verdicts): e.g. a timestamped distance enclosure, a timed request/acknowledgment automaton relation, an engagement-delay/braking envelope, or a conditional joint observation kernel. Exports specify their originating events, assumptions, coverage, units and state relations.
3. A persistent joint uncertainty relation K_I. Different exports are projections of one retained mechanism/source witness. A statistical marginal does not establish independence; alternative fixed parameters cannot be reselected at each use. A hidden parameter is an uncertainty coordinate, not a controller observation.
4. Learned scopes for the export maps **and their recursive updates**, with explicit separation of shared source and shared parameter coordinates. For a product context domain, a coordinate may be omitted only after proving invariance under all changes to it with other arguments held fixed. On a non-product reachable domain, require a relational noninterference witness instead; minimal supports need not be unique there.
5. A frame domain: the controller/replacement contexts under which items 1–4 hold. It is closed under the admitted boundary interventions, or it comes with a proved escape gate. Old-controller reachability alone does not establish a replacement frame.

The witnesses may be large. A compact interface claim additionally requires explicit bounds on the transducer, joint relation, separator tables and proof checker. Neither the mechanism selector nor an arbitrary full environment verifier may be hidden inside one nominally small type.

All witnesses are finite decidable objects in the chosen universe (rational probabilities, finite state tables, finite relation/simulation checks). An interface cost orders candidates by declared executable representation cost, with deterministic tie breaking; no intrinsic unique smallest decomposition is presumed.

## 3. Constructive acquisition theorem

Let E be a finite menu of resettable diagnostic experiments. Each e has a finite complete transcript alphabet Z_e, including failure/termination records. Its certified reset restores the declared initial source state without changing the persistent m. For the fixed-menu theorem below it has a physical safe-execution witness for **every** m in the initial M, including reset, diagnostic and final tail; otherwise it is not a safe menu element. An adaptive extension may certify against the currently retained set instead, but then acquisition safety itself is conditional on the simultaneous event retaining truth. Conditional on m, repeated resets produce independent samples with a fixed transcript law p_m^e. This premise is substantive and not available for arbitrary uncontrolled physical drift.

Assume rational finite M and a separation lambda>0: whenever p_m^e differs from p_n^e for some experiment, at least one coordinate in some e differs by at least lambda. This lambda can be computed from the supplied finite universe, but may be extremely small. Let D_Z=sum_e |Z_e|. Take

    N >= (8/lambda^2) log(2 D_Z/delta)

samples per menu element and retain

    K = {m : max_z |p_m^e(z)-p_hat^e(z)| <= lambda/4 for all e}.

Hoeffding plus a coordinate union bound gives an event E_conf of probability at least 1-delta on which the true m belongs to K, and every retained model has the same complete experiment-law signature as the truth. (The empirical estimate is within lambda/4; two retained distributions differ by at most lambda/2, excluding any separated pair.) All costs, including |E|N resets, transcript processing and model/interface enumeration, count.

Enumerate I in Q and retain exactly the interfaces satisfying Section 2 for every m in K. Return the least-cost valid interface, or abstain if none meets the declared budget/usefulness constraints.

**Theorem A (safe discovery, with the identifiability limit exposed).** Under the preceding premises and supplied physical envelope, acquisition is physically safe, and with confidence 1-delta the returned interface is sound for the actual mechanism throughout its frame domain. If the true experiment-signature class has an interface in Q meeting the budget and usefulness constraints, the procedure returns one. No experiment-signature class can be split by this menu, however many samples are taken; any promised success requiring such a split is unjustified.

**Proof.** Safe protocols and their reset/tail witnesses concatenate. The concentration event retains truth and removes all separated signatures. Exhaustive interface checking is therefore sound for truth and complete relative to Q and the remaining signature class. The indistinguishability statement follows from identical laws for every menu experiment, also under adaptive menu selection. QED.

This is a constructive existence theorem, not an efficient generic learner. The model and interface enumeration can be exponential or worse in the natural size parameters. A substantive positive family must replace it with a structured algorithm and charge that algorithm's actual costs, or honestly use this only as a specification.

**Adaptive maintenance.** At acquisition episode j, use a confidence allocation delta_j with sum_j delta_j<=delta_total. Conditional on the previous history, the selected reset experiment and sample size must satisfy the concentration premises for the actual stationary episode mechanism. Conditional failure bounds and a union bound then yield simultaneous validity. This is not permission to stop a fixed-sample test arbitrarily or assume stationarity across replacements. Any carried-over evidence needs an unchanged-mechanism witness for its actual scope.

## 4. Heterogeneous semantic composition

Each native certificate c has a semantic assertion Phi_c in its own model language and a translation witness T_c connecting that language to a common causal execution omega. Statistical certificates assert properties on a named training-confidence event; timed automata assert event-order/clock properties; dynamics certificates assert physical trajectory enclosure on a named physical-premise event. Their meanings stay different even though the witnesses can be checked together.

The finite composition proof checks that pullbacks T_c^*Phi_c discharge the actual assumptions of dependent claims on the **same** execution. Shared events/parameters are identified, not multiplied as independent copies. A proof that each component separately has some favorable model is insufficient; one persistent joint realization must witness their simultaneous use. If statistical claims use a union bound, it is on distinct failure events with their actual bounds; duplicate use of one event does not create a new independent probability factor.

A segment certificate must cover action through its promised endpoint or stopping tail. If a lease expires earlier, admission requires a separately justified reserve from which a certified backup can complete. Merely detecting expiration or emitting an invalidation signal is not a physical safety proof. Without the lease or reserve, the result is assurance loss.

**Theorem B (composition and refinement).** On the simultaneous confidence event and physical premises, a valid interface plus a checked translation/composition proof implies its stated physical guarantee for every admitted causal controller in the frame domain. If K' subset K and the physical meanings, interface permissions, budgets and frame domain are unchanged, every old universal certificate remains valid; the set of certifiable controllers cannot shrink. Strict improvement requires a separate witness: an admitted controller whose obligation holds for all K' but fails for some K. No such strictness follows from refinement alone.

**Proof.** Section 2 relates actual execution to the exported primitive claims by induction over every causal update. Their checked translations give the actual assumptions of the composition proof. Apply that proof, including every complete physical segment. Set inclusion preserves universal obligations. QED.

A statistical failure-risk conclusion remains conditional on confidence unless explicitly converted: if on E_conf, P_deploy(B | learned artifact) <= rho plus separately modeled physical failure eta, this does not mean rho, delta and eta are three interchangeable per-step costs. Repeated deployment needs its own specified probability statement.

## 5. Non-monotone maintenance and the actual frame law

Evidence expiry, changed calibration or a replacement may expand the candidate set, not merely shrink it. Old validity then does not follow from refinement.

For an existing proof c, let J_c be its **semantic support**: the primitive boundary processes, recursive state relations and shared/persistent uncertainty constraints actually used in its checked proof. The certified domain A_c is a set of their joint contextual behaviors, not a list of node names or independent marginal intervals. Let Proj_J(K,D) denote all their projected behaviors under the admitted contexts D, with parameter persistence retained.

**Theorem C (contextual reuse under revision).** If c is proved for every behavior in A_c and

    Proj_Jc(K_new,D_new) subset A_c,

then c remains valid after the revision, provided its physical/event translations and lease assumptions remain valid. In particular, equality of the old and new joint projection is sufficient. If the inclusion cannot be established, withdraw c before its next use (with the lease/reserve obligation above). Matching currently observed values or each exported marginal separately is not sufficient.

**Proof.** Every new actual projected execution belongs to the domain universally covered by the same proof. QED.

This law is intentionally simple; the difficult constructive obligation is to establish the projection inclusion **locally from a discovered frame**, rather than calling whole-system verification to decide it.

### A finite local sufficient witness

A certified separator B splits retained semantic constraints into an unchanged side U and revised side R. Store the unchanged-side relation/kernel as a conditional table over B, including the shared persistent selector and source history needed by U. Its derivation proves that all dependencies crossing the cut occur in B, on the whole frame domain. Then a changed R can be checked against this fixed table by joining its new boundary relation/kernel with the table. No factor or evidence that constrains both U and R may be silently assigned to only one side; it belongs to B or the revised join. For stochastic kernels, normalization, conditional support and initial joint law must be checked; multiplying independently normalized marginals is generally wrong.

A replacement preserves U's local proof without rederivation if U's own mechanisms, proof premises and conditional boundary semantics are unchanged and the new boundary behaviors satisfy its assumptions. The aggregate assurance conclusion may still require a new join/risk computation. A new controller can open new contexts: the stored table must cover them or be expanded, and its cost charged.

This is not a claimed novel incremental engine. It specifies the discovery target that an ordinary incremental engine needs and may otherwise be handed by a modeler.

## 6. Mandatory prospective witness and cost accounting

Before experiments, exhibit (i) two initial mechanisms observationally consistent with available raw records but needing different assurance summaries; (ii) safe permitted experiments that separate the relevant alternatives; (iii) a useful controller admitted after discovery but not before, or a strict rechecking cost separation; (iv) a replacement whose effect crosses a non-obvious learned dependency, so naive component-label caching is wrong; (v) a replacement with a proved small frame, so the legitimate reuse is not merely a global refusal.

Count D discovery + C initial certificate construction + sum_j(U_j update/invalidation + Q_j new composition/query) + runtime monitoring/storage. Compare against a coherent whole-system checker and a serious incremental checker using the same learned evidence. If both are supplied the same discovered frame, a standard incremental engine may match us; then the contribution is the discovery of its prerequisites, not a faster engine.

A possible conditional cost witness: an exact bounded-width factor/junction representation with fixed topology admits cached separator recomputation along a balanced tree in O(log n) affected nodes per local leaf replacement, versus O(n) from scratch, with table-size factors explicit. This is standard and only applicable if the discovered graph, width, unchanged proof premises and balanced decomposition are actually certified; hidden shared parameters can destroy the width bound. It does not establish overall savings until the charged extra discovery/maintenance cost is amortized. No such witness is currently claimed for an executed family.

## 7. Relation to existing witnessed-decomposition work

The existing `reusable_environment_discovery_20261029/theory/Witnessed_Feedback_Composition.md` supplies concrete operational common-response witnesses: initialization coupling, shared response occurrences, commuting recursive updates, positive joint laws and licensed local accesses. Those are suitable *ingredients* for Section 2, and its coverage warning applies here. Its Section 6 fibre criterion explains why one-step report equivalence alone is insufficient for a recursive quotient.

That note's original-C5 bridge requires a finite licensed update schedule and faithful finite interface enlargement; arbitrary crossing operational covers are not automatically original planar refinements. This draft has not supplied an original-C5 encoding of heterogeneous native judgments or proved that every semantic bridge is a permitted original cell. It makes no original-contract discharge or formal embedding claim. Such a bridge, if useful, must be constructed against those definitions rather than inferred by analogy.

## Status

Theorems A–C are scoped mathematical candidates. They make hidden assumptions and failure boundaries explicit but do not yet constitute the needed independently accepted substantive family. No new outcome experiment has been run. The open target is an efficient structured discovery algorithm whose learned scope/history/joint frame genuinely enables heterogeneous replacement or controller reuse beyond a supplied-interface baseline.

## 8. Exact restoration after evidence withdrawal (finite relational lemma)

This section separates *maintaining candidate consistency* from *checking a physical/probabilistic conclusion*. It supplies a concrete local implementation of part of Theorem C, not a new generic truth-maintenance algorithm.

Let persistent variables theta=(theta_v) have finite alphabets of size at most d. An immutable structural prior is a conjunction of factors r_a(theta_Sa). Each acquired evidence item e has its original factor f_e(theta_Se), its confidence/premise event and validity predicate. Active evidence A defines

    K_A = {theta : all r_a(theta_Sa) and all f_e(theta_Se), e in A}.

These are epistemic possible worlds; there is no implied probability distribution over theta. A fixed-world stochastic law remains attached to each theta. Existential projection of K_A is appropriate for retaining possibilities; sum-product averaging over theta would silently invent a prior.

Assume a supplied-or-discovered **certified supergraph** has a join tree T of clusters C_t, satisfying running intersection, containing every original structural and admissible evidence scope. Each factor is assigned once to a containing cluster. The graph's validity may itself depend on named structural evidence, which is kept separate from the factors maintained under that graph. Suppose max |C_t|<=w+1 and degree bounded by a constant. Store every factor, not only its effect on current marginal candidates; store both directed separator messages.

For adjacent clusters t,u, the Boolean message is

    m_(t->u)(theta_(C_t intersect C_u))
      = exists theta_(C_t minus C_u):
          local_factors_t AND all m_(v->t), v adjacent t, v != u.

It denotes exactly the projection of the conjunction of all factors on t's side of the cut. This identity follows by induction on that subtree, with running intersection ensuring no omitted shared variable crosses the cut.

**Lemma D (one revision from a calibrated cache).** Assume all directed messages are initially current. Replace, add or withdraw one evidence factor assigned at cluster r. (Withdrawal replaces it by true, not by its formerly projected marginal.) For a query at cluster q, recomputing directed messages along the unique path r to q and the query marginal produces exactly Proj_Cq(K_Anew). All incoming off-path messages needed for this query remain correct. Other directed messages can become stale. This holds for both narrowing and widening of K. Cost is O((dist(r,q)+1) d^(w+1)) Boolean table operations for bounded degree, plus actual local factor evaluation/storage costs. For multiple queried clusters, recompute the union of needed directed paths; there is no constant-time promise for n affected conclusions. If T is in fact a balanced bounded-degree tree of logarithmic diameter, one query has logarithmic path length. An arbitrary low-width graph does not automatically provide such a balanced tree at the same width.

**Proof.** A directed message whose source-side component omits r has unchanged defining factors, hence remains correct. Along the path from r, each next message receives correct off-path messages and the just-corrected path message. Induction establishes the displayed identity at each edge. Joining at q therefore yields the exact projected relation. The enumeration bound is the number of cluster assignments per recomputed message. QED.

**Repeated updates require version tracking.** The lemma is not an O(distance) guarantee for every arbitrary subsequent update/query: after updating only r-to-q, other directed messages remain stale. Retain factor/message versions or dirty-source sets. Before a later query, recursively recompute every stale incoming message needed by it; equivalently include paths from all not-yet-incorporated revised factors. Charge the union of those affected paths, potentially the whole tree. Alternatively recalibrate all messages after each update at O(|T| d^(w+1)). Fixed-root queries with updates propagated to that same root admit the familiar path update bound for rootward messages, but cannot then answer arbitrary new-root queries as if reverse messages were current.

A native local certificate depending on theta_Cq can now be reused if every assignment in the **new** projected relation lies in its previously certified domain. This condition may fail after withdrawal even if the current observed physical values are unchanged. Native proof/risk checking is charged separately; this lemma does not assert that every heterogeneous assurance claim has a local small-scope predicate.

**Critical limitation.** If expiration undermines the evidence that justified the supergraph itself, Lemma D cannot be applied to the old graph. Reconstruct the graph and separator relation from retained structural hypotheses/evidence, or fall back to a certified broader representation; this may require global work. A learned absence of a queue-sharing edge is not immutable merely because it was once inferred. Conversely, if the physical mechanism is certified invariant for an entire lease, statistical sample age alone need not invalidate its law: the actual model of drift determines expiry. Arbitrary time-to-live conventions must not be mistaken for physics.

**Why forgetting is dangerous.** Suppose a persistent bit g is constrained to zero by an expiring calibration. Under g=0, subsystem outputs depend only on their own inputs; under g=1, all outputs may also depend on a common latent source. A graph pruned using g=0 can be correct while that evidence is valid. When it expires, all previously suppressed source-sharing possibilities return. Retaining only independent local output marginals cannot reconstruct them. Keep the original g-conditioned factors and source identity, or explicitly escalate/reacquire. There is no universally local restoration theorem without an invariant superscope or a supported graph-expansion procedure.

A full truth-maintenance/incremental checker given the same factors and tree should match Lemma D. Our candidate research question is whether a useful such structure and its scope of invariance can be **discovered safely from the allowed records**, and whether its charged acquisition cost pays for actual subsequent matching/reuse.

## 9. Telemetry-specific semantic cautions for the proposed family

The statistical translation must refer to **capture/window events**, not merely packet delivery times. Overlapping averages can reuse the same noise occurrence; duplicated/retransmitted packets do not provide fresh calibration samples. A new polling policy changes the sequence and overlap of windows, so an old sampling-law certificate transfers only if its conditional/anytime premises cover that policy. If fresh error innovations are independent of the pre-capture history, causal adaptive polling may preserve a suitable conditional bound; this must be the stated source premise, not an empirical independence inference.

A queue-state summary must retain the payload or the uncertainty relation of already captured pending packets. Storing only queue length and latest delivered value is generally insufficient when capture-at-request is possible. A finite averaging observer retains the requisite ring buffer or an exactly justified equivalent recursive state. A finite impulse-response physical model retains pending input tails through its largest still-possible lag. These memories are separate, and can cross different component boundaries.

A sparse direct influence graph does not itself imply a local replacement effect in feedback: a changed report can alter another controller's commands, those can alter another zone, and so on. For a local substitution theorem, the complement must already be verified against a boundary trace contract broad enough to cover the replacement, or the proof must compute the actual finite-horizon causal cone. A direct-neighbor-only invalidation rule without either justification is unsound. The costs of checking/enforcing the boundary trace contract and maintaining initial queue/physical residue count.

## 10. Prospective expiry versus retrospective retraction

A scheduled lease ending at time t does not undo uses proved within its valid interval; it changes which future uses may be admitted. In contrast, discovering that a calibration/model premise was false or its data corrupted can undermine earlier assurances. Such retraction requires explicit assurance-loss/reclassification of affected historical claims, not merely new generation IDs for the future. The risk ledger never refunds past exposure, but a ledger alone cannot repair a historically invalid source-law assumption. Future replacement epochs preserve historical packet/source identities and introduce fresh IDs with their own prospective law/calibration premises.

# Budgeted interaction compatibility: exact restricted theorem and scope

Status: proposed theorem package, 2026-10-30. This is a restricted constructive foundation, not a claim to solve general discovery or computationally bounded planning. Its familiar ingredients are finite-horizon knowledge games and exact relational join-tree propagation. The intended application-level interface result is Section 5: evidence can justify shrinking the support needed to check an action, with a checkable criterion, monotone reuse rule, and explicit invalidation condition. Whether this yields an empirical advantage remains to be measured against an equally informed relational global method.

## 1. Object being assessed and quantifiers

An instance consists of (i) a mathematical universe of mechanisms, (ii) permitted public observations/actions, (iii) a mission monitor and physical safety interpretation, (iv) an initial evidence relation, and (v) a resource budget. Compatibility belongs to this entire interaction, not the environment in isolation.

For the exact initial specialization, mechanisms are static tuples theta in a finite product D_1 x ... x D_m. Variables may include unknown parent/scope selectors, delays, and local response tables. The prior is not permission to supply the actual mechanism or its actual scopes. The finite universe must be declared; guarantees are relative to it.

The public state s=(x,z,b) records observed physical state x, mission automaton z, and remaining resource vector b, including time. An action a has a finite outcome alphabet. For a fixed mechanism and public state its execution produces a deterministic record

F_a(s,theta) = (o, x', cost, hazard, mission-label).

A record covers the entire action interval and its delayed consequences required by the safety contract, not merely its end point. Unknown disturbances can be included as explicit universally quantified finite adversarial choices; the deterministic presentation is simpler and is what the propositions below initially prove. Stochastic/rare-event safety requires separate conditional-law/risk semantics, not replacing probabilities by marginal bounds.

Every nonterminal action spends at least one time unit. The public successor s' is determined by the visible record, action, current mission state and budget. Hazard need not be observed: it is checked universally over compatible mechanisms before acting. If some physical variable is not observed, it belongs in the latent relation together with its transition; static-parameter filtering below cannot simply be reused unchanged.

After public history h, K_h is the nonempty set of mechanisms consistent with the prior and all observed records. Evidence is retained exactly; an acquired fact cannot be treated as independent of the history that produced it. The information state is q=(s,K_h). An observation-based strategy chooses from q, or equivalently from the complete public history. No access to theta is allowed.

A strategy wins if, for every theta in K_h, all actions are safe, all resources remain feasible, and the mission reaches acceptance before the deadline. This is a uniform guarantee. It is stronger than: for every theta there exists a successful strategy knowing theta. Failure of the uniform guarantee does not imply failure in the actual world.

## 2. Exact three-way decision semantics

An action is robustly legal at q if its full interval hazard is false and its resource consumption is feasible for every theta in K_h. A legal action and visible result r induce

K_r = {theta in K_h : visible(F_a(s,theta)) = r}.

Only nonempty K_r are successor branches. Budgets and physical/mission states update using r. If costs are hidden, either use the worst-case debit or retain cost/resource uncertainty in the latent state; do not debit an unobserved favorable cost.

Define W(q) by backward induction on remaining time:

- Accepted, safely terminated states are winning. Acceptance must include any outstanding delayed-effect obligations.
- A nonaccepted state with no remaining feasible completion time is losing.
- Otherwise W(q) holds iff there exists a robustly legal action a such that W(q_r) holds for every feasible visible result r.

**Proposition 1 (exact knowledge-game decision).** This recursion is equivalent to existence of a winning observation-based strategy in the declared finite model.

Proof: induction on remaining time. A winning strategy's first action must be robustly legal and every possible observation continuation must win. Conversely choose the witnessing first action and attach each inductively winning continuation. The information state is sufficient because mechanism consistency and the observed persistent state determine every legal action and successor. Strictly decreasing time makes the construction finite. Randomization does not improve an all-world sure guarantee: every action used with positive probability must itself satisfy the same universal continuation condition.

This is standard game reasoning, not the novelty claim.

A solver returns exactly one of:

1. **WIN with certificate:** a finite policy DAG, each internal node choosing one legal action and covering every feasible outcome, all leaves accepting safely.
2. **LOSE with certificate:** a finite AND-OR refutation. At each nonterminal losing node every syntactically permitted action is either ruled out by a feasible hazard/resource witness, or is robustly legal and has a feasible successor with a losing certificate. Leaves violate the deadline/mission condition. The action list must be complete for the declared action universe.
3. **UNKNOWN:** neither certificate has been established within the computation limit.

A losing refutation may choose different consistent mechanisms for different counterfactual branches/actions. This is sound: for any fixed policy it selects one root-to-leaf history; nested finite nonempty version spaces along that history have a common mechanism at its leaf. It is not permission to switch mechanisms during an actual execution.

A certificate for no uniform winning policy is not automatically a certificate that the actual world is individually impossible, nor that no larger strategy language would win.

## 3. A validated relational cover

Let bags B_v form a tree J with the running-intersection property. For each bag store a finite relation R_v on theta_{B_v}. Require exactness:

K = join_v R_v.

There is no probabilistic independence assumption here. Relations on overlapping bags retain correlations through shared variables. For a model-selector variable or long-range coupling that appears in several bags, running intersection must include it along the intervening path.

The source evidence and mechanism equations remain authoritative. A proposed smaller cover must carry an exact lossless-join justification, not merely match unary marginals. A dense valid cover always exists for finite K but may defeat the desired efficiency. Building a good cover from raw observations is part of acquisition cost, not free input.

Assume that, at the current guard of public states, every action record F_a depends only on theta in one bag B(a). This includes safety, resource consumption, physical transition, mission labels, and observation generation, not just reported output. A global resource constraint may depend on public s without violating this condition. Simultaneous actions involving distant bags must be represented by a larger action bag or checked with their joint relation; checking each separately is insufficient.

An observed record adds a relation C_{a,s,r} to B(a), so that K_r is represented by replacing R_{B(a)} with R_{B(a)} intersect C_{a,s,r}. Evidence retraction is not covered by this intersection rule: retain the unfiltered evidence factors and restore/recalibrate all affected messages.

For each directed edge v->u, compute the message consisting of separator assignments extendible to all relations in the component of J-vu containing v. Two passes compute these messages exactly. The supported bag relation is

P_v = R_v intersect intersection_{u neighbor v} lift(M_{u->v}).

**Lemma 2 (global-extension lemma).** P_v is exactly projection_{B_v} K. Every tuple in P_v extends to a global theta in K.

Proof: delete v from the tree. Each incoming message certifies an extension in a distinct subtree agreeing on its separator with the chosen tuple. Running intersection implies different subtrees share no variables outside B_v. Their extensions therefore glue to one global assignment. Necessity follows by restriction of any global assignment. The same argument recursively justifies message computation.

This is the established acyclic relational consistency/join-tree property; it is not new.

## 4. Exact compositional certificate verification

**Theorem 3 (local-support game preservation).** Under Sections 1–3, replacing global-world enumeration by supported action-bag relations produces exactly the same robustly legal actions, feasible visible outcomes, and successor version spaces, hence the same winning and losing states and the same valid policy/refutation certificates.

Proof: every possible full record is obtained by evaluating F_a on a tuple in P_{B(a)} because F_a has the declared dependence. Conversely every such tuple extends to a global world by Lemma 2. Thus record enumeration is neither optimistic nor pessimistic. Filtering conjoins precisely the observed-record relation, preserving exactness on the same tree. Induct on remaining time and use Proposition 1.

The theorem concerns the equality of complete decision semantics, not independent local winning decisions. Physical resources, mission ordering, public state and shared budgets stay in q. They can create global strategic dependence even with width-zero mechanism evidence.

A WIN verifier enumerates each supported action-bag record and checks legal safety/resource use plus a covered successor. A LOSE verifier checks the complete action list and each claimed unsafe world or losing successor. A local tuple is a valid negative witness only after its extension to the complete evidence relation is justified. This is why rectangularizing or dropping separators can invalidate impossibility certificates as well as successful ones.

If there are n bags, each variable has at most d values, and bag size at most w+1, a full calibration can be performed by table scans of order n*d^(w+1), up to tree degree, record-evaluation and hashing costs. Each action's records can be obtained by scanning at most d^(w+1) supported tuples. A policy/refutation with N distinct information nodes can therefore be verified using O(N*n*d^(w+1)) table work plus action-count factors and certificate storage, instead of necessarily scanning d^m worlds at every node.

This is a representation/verification upper bound. It does not establish superiority to a dense *symbolic* relational solver. N may be exponential; synthesizing the policy may dominate all verification work. Incremental recalibration can still propagate globally along the tree. Report measured times, table cells, certificate size, and acquisition cost separately.

### 4.1 Simultaneous actions with factored records

The single-action-bag condition can be relaxed for simultaneous actuator vectors. Suppose a full action record is assembled from finitely many local records F_{a,i}(s,theta_{B_i}), with global hazard equal to a known Boolean combination of local hazard flags, and with resource costs/mission updates computed from the public state and those records. For the usual conjunction of local safety inequalities, robust safety is checked row by row using exact supported bag tuples. Public power and energy are checked directly.

The *joint observation tuple* r=(r_i) is feasible exactly when

join_v R_v intersect intersection_i {theta : visible(F_{a,i}(s,theta))=r_i}

is nonempty. Local outcome feasibility does not imply joint outcome feasibility. Add all observed row constraints to their bags, then calibrate. This preserves the exact global transition game for the same reason as Theorem 3. Every full-world successor has a feasible tuple, and every accepted joint tuple has a global mechanism witness. A complete positive certificate must cover all feasible joint tuples; a negative certificate needs one such feasible tuple per robustly legal action.

One may enumerate joint tuples by relational backtracking or a symbolic partition representation. Their number can be exponential in the number of observed rows even at bounded evidence width. The theorem promises efficient checking of a proposed tuple and local safety queries, not polynomial enumeration of every observation branch. Certificate bounds must include the number of branches explicitly. A global safety predicate that is not rowwise separable requires its own factor/elimination support; checking local marginals alone is then insufficient.

## 5. Discovering a smaller sufficient interface during execution

An actual physical parent set is not the same as the currently necessary checking interface. Some parameters may remain unknown but cease to affect a particular action's mission-relevant record under the accumulated evidence.

Let G be an explicit finite guard of public states, a an action, and D a proposed subset of its current support bag. Define conditional record sufficiency:

(CRS) For all s in G and theta,theta' in K, theta_D=theta'_D implies F_a(s,theta)=F_a(s,theta').

If the desired interface omits irrelevant aspects of the raw record, replace F by an explicitly declared interpreted record, but retain every safety, budget, observation, and successor dependency needed by the policy. Full future sufficiency requires recursive closure, not just equality of an immediate terminal score.

**Theorem 4 (evidence-certified interface shrinking).** CRS is necessary and sufficient for a well-defined map g_{a,G,K} from s and the supported D-tuple to the action record. Such g gives exactly the same legal-action and outcome checks as F on K. If K' is a subset of K and s remains in G, the same certificate and map remain sound after further evidence. Retraction to K'' not contained in K, leaving G, changing the mechanism semantics, or changing the interpretation invalidates this reuse unless checked again.

Proof: define g(s,t) by choosing any theta in K with theta_D=t. CRS makes the value independent of the choice; necessity is immediate from functionality of g. Restricting the quantified pair of mechanisms preserves CRS. Exact record equality gives preservation of each action test. Induction along the policy yields recursive preservation when every encountered action has a valid certificate and every guard is respected.

CRS can be checked without enumerating all pairs of global worlds. Form two copies of the exact join tree, combine corresponding bags into B_v plus B'_v, conjoin equality theta_D=theta'_D, and ask whether any supported action-bag pair satisfies F_a(s,theta) != F_a(s,theta'). The resulting bags have size at most 2(w+1); the running-intersection property survives. Emptiness proves CRS; a supported unequal pair extends to two full evidence-consistent worlds and is an explicit obstruction witness. Iterate over the finite guard G. Thus the certificate check has a doubled-width table bound, not an unexplained omniscient scope oracle.

CRS is conditional functional dependence (and can be viewed as certified partial evaluation), not a new general dependence theorem. Its proposed contribution here is its integration with mission-dependent evidence, recursive certificates and measured costs. This is the proposed link from acquired evidence to a reusable compatibility interface. Candidate D can be generated by search, dependency analysis or heuristic learning. Trusted checking establishes sufficiency. Finding the minimum D can be expensive. A safe new observation can make a previously failed CRS test pass while leaving many mechanism variables unidentified.

Do not replace the global evidence relation with D-marginals merely because one action admits this smaller interface. Those correlations may be essential for later actions, for filtering, or for other missions. The live interface can shrink while archived evidence and the authoritative cover remain available. Any claimed memory saving must distinguish live verification tables from total retained evidence.

The action checker is smaller only if the certified map g and supported D relation are cheap enough to construct and maintain. Amortized benefit must include the twin-copy proof, map construction, invalidations, and acquisition. This is a testable proposition, not a guaranteed experimental result.

## 6. Two exact obstruction witnesses

### 6.1 Budgeted discoverability is stricter than pointwise solvability

Unknown theta is 0 or 1. A public probe takes two time units and reveals theta safely. Service actions a_0 and a_1 each take one time unit; a_i completes the mission safely exactly when theta=i, and otherwise causes failure. Waiting takes one unit, is safe, and reveals nothing. All actions and outcomes have now been specified.

With deadline two, both single-world oracle missions are solvable in one unit. No uniform safe policy exists: either service action is initially unsafe in one compatible world; probing leaves no time for service; waiting cannot remove the ambiguity and consumes time. This is a complete negative certificate, not failure of search. With deadline three, probe then the matching service action is a winning policy. The distinction is produced by the interaction and budget, not the mechanism alone.

This is a small theorem witness, not an adequate performance benchmark.

### 6.2 Omitted joint information changes the answer

Let two unknown bits have evidence K_equal={00,11} or K_opposite={01,10}. Both have identical unary supports {0,1}. A one-tick action 'same' completes safely exactly when the bits are equal; an action 'different' completes safely exactly when they differ. Deadline is one and no probe fits.

The exact evidence certifies 'same' for K_equal and 'different' for K_opposite. Replacing either relation by its product of unary projections yields {00,01,10,11}, under which neither action is certifiable. Any interface that identifies these two evidence states but claims to preserve the safe-completion decision is invalid. This is an obstruction to that interface, not a statement that all decompositions fail. An equality/parity separator restores sufficiency.

A scalar budget cannot be forgotten either: identical evidence and physical configurations with deadlines two and three differ by Section 6.1. Independent local feasibility likewise does not imply shared-budget feasibility; two one-unit jobs sharing one unit of total service time cannot both complete.

## 7. Discovering discoverability and the limit of the claim

There are at least three questions:

- Pointwise physical feasibility: an oracle knowing theta can complete.
- Uniform learn-and-complete feasibility: a public-history strategy works for every theta compatible with current evidence.
- Epistemic classification: the observations available under the budget can distinguish hypotheses on opposite sides of a stated property, such as pointwise feasibility.

The game decides the second in its finite specialization. It can incorporate classification as a mission by adding a final claim action whose correctness is checked for every theta in K. It must not treat a truthful classification of 'no uniform strategy' as physical completion of the original mission.

For a property P(theta), a sound final yes/no classifier must stop only when P is constant on K. A safe experiment decision tree identifies P within budget iff all its leaves have this constancy property. The same finite game handles the budget and physical effects of those experiments. If every permitted experiment history leaves two compatible worlds with different P, no sound total classifier exists in that regime. Choosing P, the regime and whether classification or service is required is part of the mission definition.

### 7.1 Option-preserving diagnosis of world-dependent feasibility

To avoid circularly renaming the belief-game solver, fix a reference state s_0 and budget b_0 *before* diagnosis. Define P_0(theta) to mean that a fully informed controller could safely complete the mission from this reference configuration within b_0. This is a world-dependent predicate; it is not the current belief's uniform-winning predicate.

An option-preserving diagnosis-and-service policy must be safe in every compatible world and must, within the original budget:

- complete the mission whenever P_0(theta) is true;
- otherwise return a sound certificate of initial pointwise impossibility, stopping at a leaf K contained in the false set of P_0.

The policy may learn while doing useful work. On a positive leaf its continuation is a uniform completion strategy for all compatible initially feasible worlds; it cannot rely on learning after the deadline. A negative leaf claiming *initial* infeasibility must not merely show that the policy has spent so much time that completion is now impossible. Anchoring P_0 at s_0 prevents this self-created failure from counting as successful diagnosis.

This is a conditional mission objective on the same partial-observation game, with terminal acceptance depending on theta and a declared classification flag. The exact factor-game theorem applies only when this terminal truth predicate is also checked exactly (possibly by a separate oracle certificate rather than a local bag). The construction remains a standard contingent-game formulation; its value here is correct task semantics, not a novel general solving algorithm.

A simple strict separation uses three possible mechanisms L, R and broken. A two-unit safe probe identifies which one is present. In L or R, a corresponding one-unit service completes safely; in broken no service can complete. With three units, pure completion is not uniformly possible because broken is possible. Diagnosis-and-service is uniformly possible: probe, complete in L/R, otherwise certify broken. With two units, a probe can classify but consumes the completion option in L/R, so it fails the stronger objective. A negative result from the diagnosis game is distinct again from a negative result for pure completion.

In a completely known finite hypothesis model, an unbounded outside solver can already decide at the root whether either conditional policy exists. Runtime experiments discover which world-dependent feasibility class applies and which contingent continuation is appropriate; they do not change this mathematical fact. Computationally bounded discovery of a certificate is an additional metalevel problem. If the task instead permits a certificate of *current robust non-guarantee* as a successful stop, explicitly state that weaker objective: a mixed feasible/infeasible root may satisfy it immediately, without any experiment. Such a benchmark would not demonstrate discovery of world-dependent discoverability.

Computational budget is not automatically physical time. The theorem gives existence and checkability, not a deadline guarantee for arbitrary solver computation. A deployable protocol must debit actual or certified worst-case computation/communication time, retain a previously certified safe fallback, and refuse late certificates. A solver timeout is UNKNOWN. A negative result for a finite controller grammar or memory cap must state that restriction. We have not proved an impossibility theorem covering every symbolic representation under a general computational budget.

## 8. Recommended implementable specialization

Use persistent finite-state multistage jobs, shared power/energy, explicit time/deadlines, and unknown local coupling/delay/scope selectors. Offer multiple safe informative actions that also do work, plus pure probes whose resource consumption can close later opportunities. Actions reveal local physical transitions but may leave mechanism ambiguity. Use exact rational/integer semantics initially to permit an independent checker.

Keep four distinct mechanisms in the comparison:

1. Exact full-world belief-game baseline where tractable, serving as a semantic oracle.
2. Equally informed coherent symbolic/global relational planner, to prevent attributing ordinary compression to the proposed decomposition.
3. Exact join-tree checker/planner using the same evidence, with discovered CRS interfaces and full accounting for their certification/maintenance.
4. No-learning and full-information references, explicitly different information regimes.

A successful research result needs a family where service starts before full identification, remaining hypotheses are genuinely distinct, deadlines make acquisition choices matter, and CRS interfaces shrink enough to repay their construction or enable a specified representation bound. Include WIN, exact LOSE, and UNKNOWN separately. Vary unknown support patterns, seeds and budgets prospectively. Compare whole admitted policies, not only successful selected runs. Include evidence retraction/version changes as separate experiments if implemented, not an unsupported promise.

## 9. Related machinery and originality boundary

- Observation-based qualitative games and the memory costs of partial observation are established: Chatterjee, Doyen and Henzinger, https://arxiv.org/abs/0909.1645 . Our finite robust reachability formulation is a specialization, not a new general game theorem.
- Exact acyclic joins and separator extension are established. A current primary-source survey is https://drops.dagstuhl.de/storage/00lipics/lipics-vol365-icdt2026/html/LIPIcs.ICDT.2026.25/LIPIcs.ICDT.2026.25.html .
- The supplied categorical reconstruction notes explain why behavior-preserving composition does not force canonical predictive-state reconstruction to commute with wiring. The present construction uses a sufficient evidence representation; it does not demand a canonical minimal predictor.

The credible new target is evidence-certified support reduction integrated with persistent mission execution, preserving both constructive and obstructive judgments with measured benefits. The generalization to discovered heterogeneous quantitative assurances remains open unless separately instantiated and proved.

## 10. Exact small-instance regression checks

`check_theory_instances.py` checks all 3,375 triples of nonempty binary relations on a three-edge path against brute-force global projection. Of these, 2,799 joins are nonempty. It compares 11,196 doubled-tree CRS checks against direct pairs of globally consistent worlds, with a record containing both an observation and a physical-transition component. Five probe/deadline/diagnosis assertions and the omitted-correlation witness also pass. Results are in `theory_instance_checks.json`. These are executable theorem sanity checks, not evidence of a scalable algorithm or a nontrivial mission benchmark.

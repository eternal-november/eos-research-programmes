# Distributed Invariant Control Across the Constitution Boundary
## Program synthesis, v1.1

**Status.** Synthesis note. It replaces the four July 15 notes as the program statement and absorbs the two later problem statements (`doctrine_question_note.md`, `bft_public_warrant_problem.tex` with its review) as modules. Nothing here is a finished theory. Claim typing: **[def]** definition, **[law]** structural claim with a named falsifier, **[thm-t]** theorem template with proof obligations named, **[frag]** discharged fragment (sketch-level), **[conj]** conjecture, **[rec]** design recommendation, **[hyp]** research hypothesis (notably every novelty claim). **v1.1 changes:** κ declared engineered and socially maintained, with κ-lifting as a response class (§1, §6.4); institutional-stability condition on Law B and tightened monotone-fragment conjecture (§3.2); induced-paralysis template (§4, template 8); stratification demoted from forced to motivated, with the joint-fragment alternative named (§3.1); import criterion for the expressiveness audit pinned (§3.1); rational-adversary kernel re-declared with leak points marked (§2.4); Law C retyped as schema with completeness target (§5); STPA bridge restored (§9); worked \(L_2\) instance added (§8.1).

**Name.** *Distributed Invariant Control* (DIC); the Byzantine-qualified subproblem is *B-DIC*. The name marks the controlled object, not the disturbance model.

**Lineage audit** (what was kept, corrected, dropped — the residual obligation of a synthesis is showing that nothing dropped was load-bearing):

| Source | Kept | Corrected or demoted | Dropped |
|---|---|---|---|
| `bft-research-note-long-1` | authority decomposition; proportionality rule; endogeneity insistence | coercion demoted from primitive to derived compensation (§6.3) | manifesto register; uncited literature claims |
| `distributed_invariant_control_research_note` (B-DIC) | intervention algebra; effective exclusion; fault vector; seven closures; pressure manifold; metrics; propositions | product ontology \(X_P\times X_C\times X_I\times X_E\) demoted to per-invariant candidate; closures demoted from criterion to diagnostic; architecture demoted to reference pattern | copy-paste LLM brief (this note is the instrument) |
| `distributed_invariant_control_lifting_note_v2` | audit rule; epistemic envelope; disturbance typing; failure taxonomy seeds; glossary seeds | — | superseded formulations (note 4 versions kept) |
| `from_bft_to_generalized_state_control_research_note` | **spine**: three reconstructions; relation \(R\); constitutive classification; adequacy test; result forms; procedure; benchmarks | — | redundancy with lifting v2 |
| `doctrine_question_note` | Law A (§3.1); stratified assignment | — | — |
| `bft_public_warrant_problem` + review | Law B (§3.2); D3 formalization program; solved fragment; graded warrant | variance, vacuity, coincidence, monotonicity repairs applied as stated in the review | — |

---

## 1. Thesis

Classical BFT controls a state that its own decisions *constitute*: once a quorum-valid commit exists, the committed state simply is what the protocol says it is. Within that regime, agreement, trace admissibility, and justified commitment are three coordinates of one event, warrant is monotone, and the control problem is invisible because deciding and effecting coincide.

**The program is to hold the guarantee form fixed — a specified invariant preserved against a capability-specified adversary — and move the controlled object outward across the *constitution boundary*: from variables agreement constitutes, through variables agreement reaches only via contracted interfaces, to variables agreement can only sense and influence. The theory of distributed invariant control is the theory of what that crossing costs.**

**[def] Constitution index.** For an invariant-relevant variable \(v\) (relative to claim class and protocol), let
\[
\kappa(v) \in \{\textsf{constituted}, \textsf{mediated}, \textsf{autonomous}\}
\]
according to whether a valid protocol decision makes \(v\)'s value true within the model, causes it through an interface whose behavior is contracted or verified, or merely correlates with it through sensing and actuation. Mixed variables are classified per transition. A system's *profile* is the multiset of \(\kappa\)-values over its invariant-relevant variables; the benchmark ladder (§8) is ordered by profile.

**κ is engineered and maintained, not found.** The index is relative to an institutional arrangement, and it is itself controlled state: tokenization, complete mediation, interlocks, and legal recognition of protocol facts *move variables inward* (κ-lifting, §6.4), and recognition can be revoked or forked away. Constitution is socially maintained — the authority of "what the protocol says" is itself an autonomous variable — so the interior of this space is interior only relative to an institutional envelope living at the exterior. This is the reflexivity requirement (§6.3) recurring at the level of the classification itself, and it is what keeps the interior from becoming a trusted base by another name.

Three regularities index off the boundary, and they organize everything the corpus produced:

- **Law A (doctrine).** The candidate governing doctrines — state/viability, trace/supervisory, epistemic/warrant — are interdefinable on constituted state and open lawful gaps as \(\kappa\) moves outward. Doctrine is assigned per obligation, not elected per field. (§3.1)
- **Law B (warrant).** Public warrant is monotone exactly where truth-makers are monotone — constituted commitments and irreversible events — and becomes defeasible past the boundary. (§3.2)
- **Law C (compensation).** Each step outward voids a guarantee BFT got for free and demands a specific compensating structure; the lift-failure taxonomy is the negative image of the compensation schedule. (§5–6)

BFT is the interior point of this space. A biosecurity custody chain or a power grid is the far exterior. The research object is not any single architecture but the *lifting problem*: which guarantees survive which crossings, at what price, and — equally — which crossings admit no lift at all.

---

## 2. Formal core

### 2.1 Base, extension, lift

**[def]** A base BFT-controlled system is
\[
\Sigma_0 = (S, A, W, T, \{O_i\}_{i \in N}, \Phi),
\]
with state-or-semantic object \(S\), joint actions \(A\), admissible fault/disturbance class \(W\), transition relation \(T\), local observations \(O_i\), and specification \(\Phi\). Distributed policies map local histories to actions. The base object admits three reconstructions as control — agreement-manifold (set invariance on augmented state), trace-language (supervisory restriction), epistemic (control of irreversible commitment) — which by Law A need not be adjudicated at the base.

**[def]** An extension is \(\Sigma_1 = (X, \widetilde A, \widetilde W, \widetilde T, \{\widetilde O_i\}, \widetilde\Phi)\) with a relation
\[
R \subseteq X \times S
\]
(not a projection: one protocol state is compatible with many world states and conversely). The extension is **liftable** when there exists a Byzantine-resilient distributed policy on \(X\) satisfying: (1) property preservation for \(\widetilde\Phi\); (2) refinement — extended executions remain \(R\)-related to admissible base executions; (3) distributed implementability from permitted local histories; (4) **non-vacuity** — the guarantee is not obtained solely by disabling the system unless shutdown is the specified safe behavior.

### 2.2 The invariant drives the ontology

**[rec]** No universal product decomposition of \(X\) is asserted in advance. For a proposed invariant, identify its truth-makers, then admit exactly the variables whose omission can falsify the guarantee. The candidate factors (plant, protocol, belief, capability, authority, evidence, model, environment) are a checklist, not an ontology.

**[def] Adequacy.** For a control abstraction \(\alpha : X \to Z\), require for states co-handled under the same information history:
\[
\alpha(x) = \alpha(x') \Longrightarrow U_{\mathrm{safe}}(x) \cap U_{\mathrm{safe}}(x') \neq \varnothing.
\]
Failure is a modeling error, not an estimation error: the abstraction merged states demanding incompatible actions.

### 2.3 Capability as state

**[def]** For actor \(i\), \(\mathsf{Cap}_t(i) \subseteq A\) is what \(i\) can actually cause at \(t\). Controllers maintain a certified upper bound \(\widehat{\mathsf{Cap}}_t(i) \supseteq \mathsf{Cap}_t(i)\) (safety reasons against it) and sometimes a lower bound (liveness reasons with it). Distinguish declared, certified, and real capability. **[def] Effective exclusion:** an actor's invariant-relevant capabilities are removed, bounded as tolerated disturbance, or compensated — as opposed to *logical expulsion*, removal from protocol membership. Membership is a constituted variable; capability is usually mediated or autonomous. Conflating them is the paradigmatic constitution-boundary error.

### 2.4 The loop and the audit rule

Generalized invariant control separates what the base regime fused:
\[
x_t \to o_t \to e_t \to (B_t, H_t) \to d_t \to u_t \to x_{t+1} \to o_{t+1},
\]
raw observation, admissible evidence, certified information state with live hypothesis set, coordinated decision, realized input, verification. Each arrow has its own fault classes and its own contract.

**[rec] Audit rule.** Every variable the controller uses must be *controlled, soundly inferred, or explicitly assumption-bounded.* "Current state," "independent sensors," "obedient actuator," "bounded adversary," "valid model" each owe a mechanism or a declared trust.

**[def] Solution concept.** With \(\operatorname{Post}(B, u, W) = \{x' \mid \exists x \in B, w \in W : x' \in \widetilde T(x, u, w)\}\) and recoverable set \(\mathcal R \subseteq \mathcal K\): a sound estimator maintains \(x_t \in B_t\); a robust action satisfies \(\operatorname{Post}(B_t, u_t, \widetilde W) \subseteq \mathcal K\) (or re-enters \(\mathcal R\)); a valid actuation contract makes the realized transition land in the modeled post-set; induction closes the loop. If \(\bigcap_{x \in B_t} U_{\mathrm{safe}}(x) = \varnothing\), consensus has not failed — the epistemic-control interface has, and the admissible moves are probe, degrade, reconfigure, or concede the state is outside \(\mathcal R\).

**[def] Fault structure.** Budgets are a vector over roles, \((f_C, f_S, f_A, f_E)\) for controllers, sensors, actuators, enforcers, with an explicit dependency model: components sharing a stack, key, operator, model, clock, vendor, site, or incentive are one fault domain, whatever the node count. Replication is not diversity.

**Declared kernel.** Strategic-but-protocol-conforming (rational) behavior is out of scope: no incentive-compatibility claims are made anywhere in this program. Two leak points are marked accordingly — sanction and slashing interventions (§6.2) are carried here only as capability restrictions, and "economic finality" (§3.2) only as graded warrant against a purchased adversary budget. Their incentive semantics belongs to a fourth adversary type with its own budget and doctrine, reserved.

---

## 3. Boundary laws A and B (Law C is §5–6)

### 3.1 Law A — doctrinal divergence and stratified assignment

**[frag] Degeneracy.** On constituted state the three doctrines (D1 state/viability, D2 trace/supervisory, D3 epistemic/warrant) preserve the same distinctions; the commit event is simultaneously a state transition, a trace event, and an epistemic act. Discharge on the replicated register is standard machinery (translations named in `doctrine_question_note.md` §1).

**[law] Divergence.** Each pairwise gap opens at the boundary and hosts a failure family: D1/D3 (state vs. belief — observability, inference), D1/D2 (geometry vs. language — timing, viability), D2/D3 (enforceable behavior vs. justified commitment — authorization, coordination). *Falsifier:* the ladder expressiveness audit (§8) finds a mediated system, level \(L_3\)+, where the doctrines stay interdefinable without importing each other's structure. **[def] Import criterion** (owed by the audit, pinned here): a doctrine states a fact *natively* if it is expressible without extending the base sorts of its standard formalism — state spaces for D1, single runs and languages for D2, run-indistinguishability structure for D3. Monitor products, history variables, and epistemic annotations count as imports. Secondary criterion where the primary is contestable: proof-transport cost.

**[rec] Assignment.** Assign each proof obligation to the coarsest stratum preserving the distinctions its consumers need; owe an explicit translation at every crossing. The strata are *motivated* by cost and *warranted* by native homes. Cost: distributed synthesis under partial information is undecidable in general architectures [17]; common knowledge is unattainable under unreliable communication [15], making quorum certification the attainable surrogate; enforceability characterizations are language-theoretic [19, 20]; actuation and timing limits are viability-theoretic [21, 7]. But cost alone forces *restriction*, not stratification — synthesis on decidable architectural fragments of the joint game is a live alternative — so the load-bearing evidence is that each obstruction family has a unique native doctrine (§4), and theorem 2 (§7) is what adjudicates between stratified and joint-fragment organizations. The unified carrier is three-sorted: an adversarial partially-observed game whose information objects are certificate-valued and whose component boundaries are contract automata.

### 3.2 Law B — warrant monotonicity ends at the boundary

The D3 stratum has a concrete formalization program: the public-warrant problem (evidence-indexed doctrine \(P : \mathsf{Ev} \to \mathbf{Pos}\), witness predicates \(W_c\), acceptance as witnessed conflict-stability; generative admissibility for \(\mathsf{Ev}\) so conflict exclusion is a theorem, not an axiom). **[frag]** The single-shot quorum case is discharged: two \(\ge 2/3\)-weight certificates overlap in \(\ge 1/3 >\) corrupted weight, so an honest signer would have equivocated; soundness \(\mathsf{Wit} \Rightarrow \mathsf{Acc}\) follows in two lines from persistence plus conflict exclusion.

**[law]** *Conditional on constitution maintenance:* warrant is monotone under evidence extension exactly where the claim's truth-maker is monotone — protocol-constituted commitments (certificates cannot be un-signed) and irreversible world events with unforgeable witness channels. The condition is not decorative: a contentious hard fork is a base change that un-constitutes committed state and violates persistence at \(L_0\) itself; forks are to constitution what reconfiguration is to epochs, one level up. Reconfiguration is the crack inside pure BFT — monotonicity survives only fiberwise per epoch, transported along checkpointed base change (weak subjectivity). Past the boundary, warrant for mediated and autonomous claims is *defeasible*: later evidence defeats earlier warrant, monotone reindexing fails, and the doctrine must change logic (graded, default, or revision-theoretic). *Falsifier:* a sound, monotone, freshness-free warrant semantics for a genuinely autonomous claim class.

**[conj] Maximal monotone fragment.** The claim classes admitting sound monotone public warrant are exactly the constituted commitments plus irreversible events whose witness channel is tamper-evident. Both conjuncts are necessary: an irreversible event with a forgeable witness — a blown fuse attested by a spoofable sensor — admits defeat of the *evidence* even though the *event* cannot un-happen. Proving or refuting this characterizes, from inside D3, where the constitution boundary runs — making the boundary itself a theorem target rather than a classification convention.

**[rec] Graded warrant.** Double-index the doctrine over adversary structures, \(P : \mathsf{Ev} \times \mathcal A^{op} \to \mathbf{Pos}\), acceptance antitone in adversary strength. "Final against \(<1/3\)," "accountably final against \(<2/3\)" [26, 27] become fibers of one object, and the fault vector of §2.4 enters warrant natively. The consumer is concrete: light clients and cross-institution verification compute \(\mathsf{Acc}\); the historical bridge failures were acceptance-without-witness events; a solved doctrine is their specification.

---

## 4. Obstructions before mechanisms

**[thm-t]** Eight non-lift templates, each with its native stratum. A serious program proves these before proposing architecture; each is stated for the weakest useful model, then weakened conditions are sought that block it.

1. **Indistinguishability (D3).** If states \(x, x'\) with \(U_{\mathrm{safe}}(x) \cap U_{\mathrm{safe}}(x') = \varnothing\) generate identical correct-controller histories through the last safe decision time, no observation-based distributed policy preserves the invariant from both.
2. **Abstraction (D1/D3 seam).** If \(\alpha(x) = \alpha(x')\) but the states differ in invariant truth or safe-action sets, no controller through \(\alpha\) can guarantee the invariant. Blocks fake generalizations that omit control-relevant hidden variables.
3. **Unmediated escape (D1).** If an admissible actor retains a transition forcing exit from \(\mathcal K\) faster than any correct preemption or compensation, no informational protocol guarantees the invariant. The formal content of "the ledger cannot stop the valve" — and the license for §6.3.
4. **Timing (D1).** If observation, inference, agreement, authorization, and actuation cannot complete inside the escape time from the recoverable set, safety fails under that architecture. Scalar latency sums are diagnostics; real theorems use reachable sets and delay-robust kernels.
5. **Decoupling (D2).** If contracts assumed independent share a failure mechanism the adversary can exploit, the composed theorem is unsound. The main way generalized claims become fictional.
6. **Recovery (D1/D2 seam).** If containing or removing a faulty component eliminates indispensable sensing, actuation, authority, or service capacity, the defense destroys the defended system. Exclusion and substitution are dual; neither is analyzed alone.
7. **Warrant vacuity (D3).** If admissibility of evidence is defined by the safety property it is meant to prove, acceptance is a relabeling. (The generative-\(\mathsf{Ev}\) repair, §3.2.)
8. **Induced paralysis (D3→D1).** If an admissible adversary strategy can, at bounded cost, keep the certified envelope action-empty (\(\bigcap_{x \in B_t} U_{\mathrm{safe}}(x) = \varnothing\)) or repeatedly trigger interventions whose cumulative service cost violates the mission specification, then safety-preserving policies exist while the mission is unachievable — and no safety-only analysis detects it. The cheapest attack on an invariant-control system is often its own defense machinery: weaponized conservatism, false-evidence-induced wrongful exclusion, denial of service via the safety system. Consumers: the wrongful-exclusion and service-floor metrics (§8); liveness-under-attack results.

**[rec]** For every proposed positive result: first construct the smallest execution in which the base mechanism succeeds and the generalized property fails; classify it against these templates; then add the weakest condition that blocks it. Differential analysis over architecture proposal.

---

## 5. The compensation schedule

**[schema, with a completeness target]** Each crossing voids a specific coincidence of the constituted regime and demands a specific compensating structure; absence yields a named failure with a named obstruction. This table is the program's spine — Law C in full. Typed honestly, C is a catalogue, not a law: its law-form is the completeness claim that *every non-lift at every ladder level is classified by some row*, its falsifier is an unclassifiable failure, and finding one extends the table — the intended failure mode. (Tolerances, budgets, and dependency models instantiate per task.)

| Voided freebie | Obligation created | Compensating structure | Stratum | Failure if absent | Template (§4) |
|---|---|---|---|---|---|
| state = decided state | sound belief under adversarial sensing | certified envelopes \(B_t\); diverse sensing; resilient estimation [4, 5] | D3 | observability/inference | 1, 2 |
| single explanation | act under causal ambiguity | hypothesis sets \(H_t\); safe probing (dual control); agreement-on-disagreement | D3 | diagnosis | 1 |
| decision = effect | commands bound realized transitions | actuation contracts; reference-monitor mediation; receipts; post-action verification | D2→D1 | actuation/verification | 3 |
| membership = capability | effective exclusion | capability bounds; revocation, interlocks, isolation, custody | D1+D2 | semantic realization | 3 |
| logical time | act inside escape horizons | delay-robust recoverable sets; reaction-margin budgets | D1 | timing | 4 |
| independence by node count | compose without shared causes | contracts \((A, G, F, \tau, D)\) with dependency annotations [8] | D2 | decoupling | 5 |
| free replacement | survive one's own defenses | substitution/continuity contracts; service floor; degraded modes [6, 9] | D2/D1 | recovery | 6 |
| exogenous enforcer | reflexive closure | meta-invariants; authority typing; proportionality; audit and appeal (§6.3) | all | capture | 3 + regress |
| private belief suffices | public acceptance | warrant doctrine, graded by adversary (§3.2) | D3 | acceptance-without-witness | 7 |

## 6. Three compensations in prose

### 6.1 Certified information states

The bridge from BFT to control is not consensus over commands but agreement over a *safe epistemic envelope*: the honest claim is \(x_t \in B_t\) and \(u_t\) safe for every member, not "\(u_t\) is safe for \(x_t\)." The coordination object is often \((B_t, H_t)\) — remaining states and remaining explanations — not a point estimate and not a premature accusation. Detection, attribution, containment, and punishment are distinct operations; invariant preservation typically needs containment before attribution settles.

### 6.2 Interventions and the minimal-coordination question

The intervention algebra (evidence, decision, capability, operational, continuity, custodial, repair, constitutional families) is retained from B-DIC as a checklist whose necessity is *derived per domain* by computing safe predecessors — no domain owes every family. "Remove node" expands to: evidence → fault certificate → authority revocation → channel isolation → actuator preemption → substitution → repair. Conversely, the program should test whether generalized control sometimes needs *less* consensus than replication: compatible local envelopes with a common action certificate may suffice where point agreement is unnecessary (flagship theorem 1, §7).

### 6.3 Coercion, derived; the enforcer, interior

**[rec]** Nonconsensual capability restriction is licensed only by the unmediated-escape obstruction: where an actor's retained transition can defeat the invariant faster than compensation, the options are narrowing the adversary model, weakening the guarantee, restricting the capability, or moving the variable inward (κ-lifting, §6.4) — and only the last two are control. Where mediation can be designed in (complete mediation, interlocks, leases, fail-closed defaults), prefer it; physical and institutional force is the residual actuator, not the primitive. Authority over such actions is typed — epistemic, decisional, actuator, membership, coercive, constitutional — and governed by the **proportionality rule**: authorization strength, evidence threshold, audit depth, and appeal capacity scale with the action's irreversibility, world-coupling, latency, and scope. The enforcement layer re-enters the model (fault budget \(f_E\), capture scenarios mandatory); the assurance recursion must end *visibly* — in a trusted primitive, a bounded fault assumption, a physical constraint, or a weaker property that survives failure of the assurance layer.

### 6.4 Moving the boundary

**[rec]** κ-lifting is the strongest response class: re-engineer the variable inward — tokenize the asset, interlock the valve, mediate the channel, obtain legal recognition of the protocol fact. Done fully, it discharges schedule rows wholesale rather than compensating them one by one. Its cost model is institutional as much as technical: recognition is revocable, mediation must be maintained against drift and bypass, and lifted status inherits the fork risk of §3.2. A design that κ-lifts a variable owes the same audit as any other compensation — who maintains the lift, under what fault budget, and what happens to the invariant when the lift lapses.

---

## 7. Flagship theorems

The program should be judged on cross-stratum results; single-stratum results mostly exist in the adjacent fields.

1. **[thm-t] Minimal coordination (D3→D1).** Characterize the weakest coordination object — received reports, admissible evidence, compatible local envelopes, joint envelope, action certificate — whose D1 shadow suffices for invariance. **[conj]** Strictly weaker than point agreement in nontrivial cases, since the D1 consumer needs only nonempty intersection of shadowed safe-action sets.
2. **[thm-t] Adversarial separation (all strata).** Conditions under which estimator (D3), coordination interface (D2), and controller (D1) can be synthesized separately and composed — and minimal counterexamples where an adversary couples correct modules into an unsafe whole. **Program reviser:** if coupling is generic, stratified assignment fails as an organizing principle and a genuinely joint doctrine is needed; that negative result would supersede this note.
3. **[thm-t] Effective-exclusion criterion (D1+D2).** Necessary and sufficient conditions under which logical expulsion plus a named intervention set yields effective exclusion while the remainder retains sensing, actuation, authority, and service floor.
4. **[thm-t] Delay-robust margin (D1).** Relate composed latency budgets (\(\tau\)-components of contracts) to the geometry of the delay-robust viability kernel; recover the scalar inequality \(\sum \tau < \tau_{\mathrm{escape}}\) as its first-order shadow.
5. **[thm-t] Recursive enforcement closure (reflexive).** Any system-level invariant theorem relying on an enforcer with invariant-relevant capability is incomplete unless the enforcer is inside the fault model, proved correct, or declared a trusted base. (Elementary threshold warm-up: unauthorized-safety plus authorized-availability under \(f_E\) Byzantine enforcers requires \(f_E < q \le n_E - f_E\).)
6. **[thm-t] Warrant characterization (D3).** The acceptance operator is terminal among operators grounded in witnessing, persistent, and conflict-stable; graded version over \(\mathcal A^{op}\). Plus the maximal-monotone-fragment conjecture (§3.2), which would make the constitution boundary itself a theorem.
7. **[frag] Degeneracy (D1 ≅ D2 ≅ D3 at the interior).** Discharged at sketch level; promotion is a work item.

---

## 8. Benchmarks, audits, metrics

**[rec] One ladder, one worked object.** Levels add one crossing each: \(L_0\) replicated register (fully constituted); \(L_1\) one external variable, trusted interfaces; \(L_2\) Byzantine sensing; \(L_3\) ambiguous diagnosis (probe vs. act); \(L_4\) Byzantine actuation; \(L_5\) dynamic capability and membership; \(L_6\) shared fault causes; \(L_7\) recovery, adaptation, mobile faults; \(L_8\) multi-institution custody and legal authority. B-DIC's domain strata (ledger, cloud-agent, microgrid, fleet, infrastructure) are instantiations, not a second ladder. The **pressure manifold** (sensors, valves, manual bypass; invariant \(p \le p_{\max}\)) is the canonical worked object from \(L_2\) through \(L_5\): the manual bypass *is* the constitution boundary made physical, and the design options — mediate it, narrow the adversary, or weaken the guarantee — are exactly the §6.3–6.4 response set (mediating the bypass is κ-lifting in the flesh).

### 8.1 Worked instance: the schedule firing at \(L_2\)

Manifold at \(L_2\): three pressure sensors, at most one Byzantine (\(f_S = 1\)); controllers correct; actuation trusted at this level. Sensor 3 reports low while true \(p\) rises.

*Row 1 fires (state ≠ decided state).* Point estimation is the counterexample generator: if correct controllers agree on a fused point value, the corrupt reading biases it — consensus succeeds, every correct controller holds the same false \(p\), the valve stays open, escape. That is the level's shortest consensus-succeeds-invariant-fails trace, and it is the schedule's row-1 failure, not a consensus failure. Compensation: a certified envelope — with at most 1-of-3 corrupt, the median lies between honest readings, so \(B_t = [\mathrm{med} - \epsilon, \mathrm{med} + \epsilon]\) with noise bound \(\epsilon\) is sound whichever sensor is corrupt.

*Row 2 fires (single explanation).* The disagreement underdetermines cause: \(H_t = \{\)sensor-3 corrupt, local gradient, calibration drift\(\}\). A probe discriminates — cross-check against flow conservation on an independent channel. Acting does not wait on attribution: containment before attribution.

*Timing row fires.* Escape time from the upper edge of \(B_t\) versus composed latency \(\tau_{obs} + \tau_{agree} + \tau_{act}\): when the margin approaches the budget, take the robust action (throttle, safe for every \(p \in B_t\)) on the envelope, not on the diagnosis — template 4 avoided.

*Decision row.* The coordination object is \((B_t, u)\) under an action certificate — a D3 object whose D1 shadow is \(\operatorname{Post}(B_t, u, W) \subseteq \mathcal K\). Point agreement on \(\hat p\) is never needed: the minimal-coordination question in miniature.

*Dormant rows.* Actuation contracts, capability, continuity, and meta-control do not fire — trusted or absent at \(L_2\). The schedule is level-indexed, not monolithic.

*Template 8 preview.* The corrupt sensor's best *legal* strategy is not the big lie but perpetual plausible dissent: readings divergent enough to keep \(B_t\) wide, forcing indefinite throttling. No safety violation ever occurs; the mission erodes. Only the service-floor metrics see it.

**Per level, three audits:** (i) shortest counterexample killing the previous level's theorem, then the weakest blocking condition; (ii) the Law A expressiveness audit — which obstruction facts each doctrine states and proves without structure-import; (iii) the assumption ledger — what remains outside the modeled boundary, stated, not footnoted.

**Metrics with consumers** (report these, not throughput): tolerated fault vector \((f_C, f_S, f_A, f_E)\) with dependency model; recoverable-set volume or approximation quality; worst-case reaction margin; fraction of invariant-relevant actions under complete mediation; authority concentration and quorum diversity; wrongful-exclusion and false-intervention rates under uncertain evidence; service floor after each admissible exclusion; evidence completeness and independent verifiability; recovery/reintegration success.

---

## 9. Relation to prior work; novelty as hypothesis

The parts are mature: Byzantine agreement and SMR [1, 2, 3]; fault detection, accountability, proactive recovery [10, 11]; resilient/secure estimation [4, 5]; controlled invariance, CBFs, viability [7, 21]; Simplex-style runtime assurance and shields [6, 9, 12]; supervisory control under attacks [13]; resilient constrained consensus [14]; assume-guarantee network safety [8]; fault-containment architecture [22]; epistemic foundations [15, 16]; enforceability [19, 20]; justification logic [23]; verified BFT [24]; finality, accountability, and light-client verification [25, 26, 27]. The practitioner bridge is STPA [28]: safety as a control problem, accidents from unsafe control actions and broken feedback. This program reads as STPA's adversarial, distributed, formally synthesizable extension — "what unsafe control actions exist" becomes "what if the unsafe control action is strategically generated, quorum-certified by compromised participants, or issued by a captured enforcement layer" — and STPA is the door to the system-safety audience alongside formal methods and control.

**[hyp]** The unification gap — treating *controlled-object lifting itself* as the object of study, with dynamic authority, capability reduction, effective exclusion, recursive enforcement, and public warrant as first-class variables of one invariant-preservation problem — has no canonical owner. This is a hypothesis, not a conclusion. **Kill-search targets:** Byzantine partially-observed games; distributed runtime enforcement; resilient active diagnosis; supervisory control with dynamic membership; capability-security formalisms; institutional multi-agent systems; justification logic applied to consensus; categorical protocol semantics; refinement relations between replicated and physical state. A hit does not kill the program — it relocates it to the found field's open problems; what it kills is the naming rights.

**Program-level revisers:** (a) kill-search success (above); (b) generic adversarial coupling (§7, theorem 2); (c) instability of the constitution index — if \(\kappa\) cannot be assigned stably per variable-and-claim in real systems, Laws A–C lose their common index and the synthesis reverts to the corpus's separate instruments.

---

## 10. First-paper packet and work-item DAG

A credible first paper is narrower than this note:

1. one precise B-DIC model with the constitution classification and audit rule (§2);
2. two impossibilities in minimal models: indistinguishability and unmediated escape (§4, templates 1 and 3);
3. one composition theorem: estimator–controller with explicit envelopes, finite state (§2.4);
4. one minimal-coordination instance: action-certificate agreement suffices where point agreement is not needed (§7, theorem 1);
5. the pressure manifold as counterexample generator: shortest trace where consensus succeeds and the invariant fails, per added crossing;
6. explicit trusted assumptions, including the enforcement layer's.

**Work items, dependency-ordered.** (a) Discharge degeneracy on the register (half-day; unblocks Law A). (b) Promote the single-shot warrant fragment to a full proof; recast Tendermint locking as the conflict-exclusion lemma [25] (first P6 instance). (c) Run the expressiveness audit at \(L_0\)–\(L_3\). (d) Formalize the indistinguishability and unmediated-escape templates in a finite-state partially-observed game. (e) Attempt minimal coordination in that same model. (f) Attempt separation or construct the coupling counterexample. (g) Draft the defeasible-warrant problem statement (the epistemic face of the lift; sequel to the warrant note). (h) Execute the kill-search. Items (a)–(d) are unblocked today; (e)–(f) depend on (d); (g) depends on (b); (h) is parallel.

---

## 11. Operating protocol (for applying this note to a system or continuing the theory)

One extension at a time. (1) Fix the base object and reconstruction; write safety and liveness without the word "consensus." (2) Add one variable or interface; classify it by \(\kappa\); define \(R\). (3) State the target property and its truth-makers; separate safety, recovery, service, epistemic objectives. (4) Propose \(\alpha\); attack it with the adequacy test. (5) Specify the loop arrows with per-arrow fault classes and the dependency model; count correlated components as one domain. (6) Identify the minimal coordination object before assuming global consensus. (7) Define actuation semantics: authorized command vs. realized effect, delays, bypasses, residual capabilities. (8) Compute or characterize recoverability; if empty, probe, degrade, reconfigure, or weaken honestly. (9) Attempt compositional proof through annotated contracts; audit timing against escape. (10) Produce the smallest failure trace; classify against §4; add the weakest blocking condition. Every pass yields: a model with a visible assumption boundary, one lift or non-lift result, one minimal counterexample, one executable benchmark, and the assumption ledger.

---

## 12. Glossary

**Constitution index \(\kappa\).** Per-variable classification: constituted / mediated / autonomous (§1). **Constitution boundary.** The locus where truth-making leaves the protocol; equivalently (conjecturally) where warrant monotonicity ends. Alias: *mediation boundary* in `doctrine_question_note.md`. **κ-lifting.** Re-engineering a variable inward across the boundary (§6.4). **Lift / non-lift.** Extension of a base guarantee to a generalized object; a counterexample showing it fails. **Certified information state \(B_t\).** Sound, assumption-indexed envelope containing the true (abstracted) state. **Agreement on disagreement.** Consensus on remaining states/hypotheses \((B_t, H_t)\) rather than on a point. **Capability envelope.** Certified upper/lower bounds on what an actor can cause. **Effective exclusion vs. logical expulsion.** Capability removal vs. membership removal. **Public warrant.** Institutionally checkable license to accept a claim, grounded in artifacts, adversary-indexed. **Graded warrant.** Warrant fibered over adversary structures. **Stratified assignment.** Obligation-wise doctrine choice (D1/D2/D3) with owed translations. **Compensation schedule.** The obligation-for-freebie exchange table (§5). **Proportionality rule.** Authorization, evidence, audit, and appeal scale with irreversibility, coupling, latency, scope. **Assumption ledger.** The explicit list of what remains unmodeled.

---

## References

[1] L. Lamport, R. Shostak, M. Pease. "The Byzantine Generals Problem." *ACM TOPLAS* 4(3), 1982.
[2] M. Castro, B. Liskov. "Practical Byzantine Fault Tolerance." *OSDI*, 1999.
[3] D. Dolev, N. Lynch, S. Pinter, E. Stark, W. Weihl. "Reaching Approximate Agreement in the Presence of Faults." *JACM* 33(3), 1986.
[4] A. Mitra, S. Sundaram. "Byzantine-Resilient Distributed Observers for LTI Systems." *Automatica* 108, 2019.
[5] Y. Shoukry, P. Nuzzo, A. Puggelli, A. Sangiovanni-Vincentelli, S. Seshia, P. Tabuada. "Secure State Estimation for Cyber-Physical Systems under Sensor Attacks." *IEEE TAC* 62(10), 2017.
[6] D. Seto, B. Krogh, L. Sha, A. Chutinan. "The Simplex Architecture for Safe On-Line Control System Upgrades." *ACC*, 1998.
[7] A. Ames, X. Xu, J. Grizzle, P. Tabuada. "Control Barrier Function Based Quadratic Programs for Safety Critical Systems." *IEEE TAC* 62(8), 2017.
[8] Y. Chen, J. Anderson, K. Kalsi, A. Ames, S. Low. "Safety-Critical Control Synthesis for Network Systems with CBFs and Assume-Guarantee Contracts." *IEEE TCNS* 8(1), 2021.
[9] U. Mehmood, S. Stoller, R. Grosu, S. Roy, A. Damare, S. Smolka. "A Distributed Simplex Architecture for Multi-Agent Systems." *SETTA*, 2021.
[10] A. Haeberlen, P. Kouznetsov, P. Druschel. "The Case for Byzantine Fault Detection." *HotDep*, 2006.
[11] M. Castro, B. Liskov. "Proactive Recovery in a Byzantine-Fault-Tolerant System." *OSDI*, 2000.
[12] R. Bloem, B. Könighofer, R. Könighofer, C. Wang. "Shield Synthesis: Runtime Enforcement for Reactive Systems." *TACAS*, 2015.
[13] Y. Wang, A. Bozkurt, N. Smith, M. Pajic. "Attack-Resilient Supervisory Control of Discrete-Event Systems." *IEEE OJCSYS*, 2023.
[14] X. Wang, S. Mou, S. Sundaram. "Resilience for Distributed Consensus with Constraints." arXiv:2206.05662; *IEEE TAC*. **[verified this session]**
[15] J. Halpern, Y. Moses. "Knowledge and Common Knowledge in a Distributed Environment." *JACM* 37(3), 1990.
[16] R. Fagin, J. Halpern, Y. Moses, M. Vardi. *Reasoning About Knowledge.* MIT Press, 1995.
[17] A. Pnueli, R. Rosner. "Distributed Reactive Systems Are Hard to Synthesize." *FOCS*, 1990, 746–757. **[verified this session]**
[18] M. Clarkson, F. Schneider. "Hyperproperties." *J. Computer Security* 18(6), 2010.
[19] P. Ramadge, W. Wonham. "Supervisory Control of a Class of Discrete Event Processes." *SIAM J. Control Optim.* 25(1), 1987.
[20] F. Schneider. "Enforceable Security Policies." *ACM TISSEC* 3(1), 2000.
[21] J.-P. Aubin. *Viability Theory.* Birkhäuser, 1991.
[22] J. Lala, R. Harper. "Architectural Principles for Safety-Critical Real-Time Applications." *Proc. IEEE* 82(1), 1994.
[23] S. Artemov, M. Fitting. *Justification Logic: Reasoning with Reasons.* CUP, 2019.
[24] V. Rahli, I. Vukotic, M. Völp, P. Esteves-Veríssimo. "Velisarios: Byzantine Fault-Tolerant Protocols Powered by Coq." *ESOP*, 2018.
[25] E. Buchman, J. Kwon, Z. Milosevic. "The Latest Gossip on BFT Consensus." arXiv:1807.04938, 2018.
[26] V. Buterin, V. Griffith. "Casper the Friendly Finality Gadget." arXiv:1710.09437, 2017.
[27] P. Sheng, G. Wang, K. Nayak, S. Kannan, P. Viswanath. "BFT Protocol Forensics." *ACM CCS*, 2021.
[28] N. Leveson. *Engineering a Safer World: Systems Thinking Applied to Safety.* MIT Press, 2012.

**Verification note.** [14] and [17] were checked against the published record during this program's sessions. Remaining entries are settled pre-2025 literature cited from memory and cross-consistent with the sibling notes' bibliographies; confirm bibliographic details before external circulation. No reference is load-bearing for the structure of the program; several are load-bearing for §3.1's cost argument ([15], [17]) and §4's templates ([4], [5]).

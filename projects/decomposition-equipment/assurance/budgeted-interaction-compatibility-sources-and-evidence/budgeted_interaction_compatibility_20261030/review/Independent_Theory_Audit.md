# Independent theory and strict-gate audit

Audited 2026-10-30. This audit covers the stated restricted mathematics and the small strict gate, not a later main benchmark implementation or a general novelty claim.

## Verdict

PASS under the explicit finite-model hypotheses. No blocking defect was found in the exact knowledge-game recursion, persistent-model refutations, join-tree extension lemma, local action-record preservation theorem, doubled-tree conditional-record-sufficiency (CRS) test, or monotone evidence-restriction reuse. The simultaneous-record clause correctly requires joint feasibility, not a Cartesian product of marginal outcomes.

The theorem package explicitly credits standard game, acyclic relation and conditional functional-dependence machinery. It is not by itself a new general compatibility algorithm. The original execution gate sought learned interfaces and demonstrated savings against a comparable coherent symbolic implementation. The user subsequently clarified that a distinct efficiency advantage is not required: a programmable learned interface with justified client substitution is itself relevant. Efficiency measurements remain descriptive and any advantage claim still requires a fair comparator.

## What the proof actually establishes

1. Public information state must contain all observed physical memory, mission progress, remaining resources and the exact persistent-model evidence relation. A fixed finite hypothesis universe and deterministic mechanism semantics are assumed. General hidden physical-state filtering and noisy confidence are not established.
2. WIN covers every feasible observation under one causal action choice. LOSE covers every permitted action by an actual unsafe/resource witness or a feasible losing continuation. UNKNOWN is incompleteness of computation, not a semantic truth value.
3. A negative certificate may use different worlds for different counterfactual policies. Along a selected finite branch, nested nonempty version spaces ensure one persistent world witnesses failure. This is not a switching-adversary model.
4. Exact supported bag tuples extend to global mechanisms only because the cover is a running-intersection tree and its join equals the authoritative evidence relation. Unary marginal agreement is insufficient.
5. CRS is conditional functional dependence of the complete interpreted action record on retained variables. Shrinking is sound under further evidence only while the guard and semantics remain valid. Keeping the full evidence archive is essential for later filtering and other actions.
6. The single-bag complexity bound is conditional on the record-support hypothesis. Simultaneous observations can have exponentially many feasible joint outcomes; Section4.1 correctly excludes a polynomial branch-enumeration claim. Shared resources can also make the policy itself large.
7. Physical hazard labels are included in the interpretation rather than assumed publicly observable. This avoids confusing public predictive equivalence with safety equivalence.
8. Section7.1 correctly anchors the world-feasibility predicate at the initial state/budget. Otherwise an algorithm could consume the opportunity and claim its self-created failure as successful diagnosis. The exact game does not itself solve general computationally bounded recognition of discoverability.

## Independent executable checks

The script review/independent_theory_check.py imports none of the author's solver, model or validator. It reconstructs the three persistent worlds, finite action space, energy, observation timing, stage credits and delayed tail in a separate interpreter.

- All three saved certificates independently pass, including exact legal-action coverage and the actual claimed unsafe witness: early acquisition WIN (11 nodes), late acquisition LOSE (101 nodes), no prerelease acquisition LOSE (31 nodes).
- Twelve start-time/energy combinations were solved independently. Early access with energy5,6,7 is winning; energy4 is losing. Late or no prerelease acquisition is losing at energies4 through7. These extra variants are audit regressions, not the preregistered benchmark.
- 2,040 finite conditional-support cases agree with direct equal-fiber functionality; 9,683 nonempty evidence restrictions preserve each established map. 1,363 candidate supports are rejected.
- All full-power prerelease controls remain in the legal action space when energy permits. Their inability to meet energy5 is derived, not silently excluded.
- Final acceptance requires the delayed input tail to be cleared. Useful stages must occur in slots2 and3, and no observation is used before the next slot.

The author's certificate checker recomputes transition safety rather than verifying the stored unsafe witness itself. That is sufficient for decision soundness if the transition implementation is trusted, but is not independent evidence that the archived witness fields are correct. The independent interpreter checked those witness fields too.

## Required empirical distinctions

A potentially consequential attribution risk is that the ladder output F_i = u_i + u_parent(previous) becomes constant whenever all candidate parents carried the same previous input. This happens for many idle rows even under the initial prior. Consequently, a smaller action interface can result from action sparsity without any learning.

Report separately:
- support reductions valid under the initial prior/current action;
- additional reductions enabled by acquired evidence;
- the cost of proving and maintaining each reduction;
- ordinary constant folding available to the equally informed symbolic comparator.

Otherwise a speedup against a full-row scanner would demonstrate only avoidable scanning, not discovered decomposition. The implementation author and parent were notified before the main runs.

The theorem allows worst-case debiting when a resource cost is hidden. Exact equivalence then refers to that explicitly conservative budget semantics; it must not be described as exact for the original hidden actual-cost budget without retaining the latter in the latent state.

## Source snapshot hashes

- theory/Budgeted_Interaction_Compatibility.md: 44d105fcd27e615c19cbe62125da62bdb358855ecedcba4182b3bbb8b4e66a3d
- design/Benchmark_Proposal.md: 07a2ef76f71cb815c062a8b2d6edbb92e03579a47ac0c1ea3cb1bbe634e181e9
- TARGET_GATE.md: 7c1c9487bef0c4a76a3d55460e689ea47ac0bec78268bda0d4410224a4fc87f2
- example/strict_pair_gate.py: def507f87965281f01be4838f699b77100a1bf21ccc7accf3d56a2105d5f9cc5
- example/strict_pair_gate_results.json: 1b7a85e76a4d05699640e107a93410b4a45add448fd06020de95e36c9480d4d5
- example/exact_search.py: 5dbcde2e566084bb30fc0bb3b6912c919974f2d2b29f331e179d96e2a5356a95
- example/check_certificate.py: a8ec541c4678e14ac29fe1a24ea9f63b88deda4dfe1c11922c6a03abe6ece6eb
- review/independent_theory_check.py: 6fa211eb6f4794e78f7da9ad0421267ae64529f0215059cb6ff0f5cad489ab25
- review/independent_theory_checks.json: 1fed4f4abbb3a4458a7473e7d2bc0ccc2ddb855a6e30997ae983078e5fd89490

## Supplemental audit: productive-evidence main witness

Audited 2026-10-30 00:24 UTC. PASS for frozen main case n4_s731_p2_r1_e0. The explanatory policy is causal: choice at slot 6 depends only on observed rows available at ends of slots 3 and 5. One-parent and no-reciprocity implications used to make consecutive stages safe are valid. All six stage credits are distinct, released, sequential within each job, and before their deadlines; zero diagnostics and energy 12 exactly. The final slot 9 flush discharges the tail.

Independent script review/independent_productive_evidence_audit.py imports no benchmark or designer code and passes 47-world causal replay, 282 stage-credit checks, 16 full-work transition comparisons and an 82-state exhaustive frozen-evidence scheduling DP. The DP includes all productive stage assignments and idle gaps. Energy 12 equals the minimum useful energy, so diagnostic pulses or uncredited full-power actions cannot appear in any successful schedule; their exclusion in this independent DP is justified by the energy lower bound, not a new action restriction.

The analytic color-block refutation is also sound. All candidate cross-color edges exist in the prior; any consecutive cross-color work therefore has an unsafe compatible world. Six mandatory stages in slots 2 through 9 permit at most 2 separator slots. The first color block cannot contain J2 or J3 work, forcing three stages into the middle block; J3 release delays its end until at least 6, then a separator forces J2 completion to at least 8 after its deadline 7. Extra diagnostic-energy allowance cannot create more time slots, so the stated stronger frozen-checker argument remains valid.

This refutes the declared frozen-initial-evidence checker class, not arbitrary history-aware controllers. The positive policy itself demonstrates why the latter class is stronger. The witness establishes useful-work learning matters for completion; it does not establish decomposition speedup, diagnostic acquisition savings over an equally informed planner, or lifetime partial identification.

A transient executor transport error prevented the first independent script launch; availability check showed no script had been created. The retry succeeded.

Supplemental hashes:
- design/Existing_Mission_Learning_Witness.md: b08ea9ff11783c40b0cb0f5a927332c34fdedb71f7a6eb36f4b0663fb79c96f9
- design/check_productive_evidence_witness.py: e43bec42915a4020a6db5d968849e01f074683b187de3df7de78b076f2c92537
- review/independent_productive_evidence_audit.py: 32152738741d1e0ecd75a17a5ee47d80df8279e839b26c7d36faabd5ef61c1e6
- review/independent_productive_evidence_audit.json: eaecf8de9f095ffa1331c620fa0d34c30712b0ae605b656ddd264dc081dbe2ef

## Supplemental audit: programmable, defeasible interfaces

Audited 2026-10-30 00:46 UTC. The restricted positive substitution theorem is sound as standard finite-client forward simulation, conditional on every call satisfying its public precondition and validity guard. Typed results, publicly computable state updates, successor simulation, nonblocking bounded execution, conservative resource/hazard interpretation, and preserved assumptions are substantive requirements. They rule out choosing the next public state using hidden information and rule out a vacuous safety proof based on deadlock or divergence. A successor must remain in the next call's valid guard, or obtain a separately validated replacement contract.

Forward refinement alone does not transfer an interface-level impossibility result. An abstract operation may allow both good and bad outcomes while a refining implementation allows only good. Every concrete behavior is then abstractly allowed, but the abstract no-guarantee verdict does not apply to the implementation. The note correctly demands complete action correspondence and exact/backward joint-successor support for negative transfer, retaining persistent model consistency.

The client in Section 5 uses decoded edge predicates obtained from reports, not a truth oracle. The earlier independent causal replay already tests this distinction in all 47 worlds. Copying these established values supports repeated pure calculations; it does not create a second independently sampled observation or duplicate the live physical resource state. The latter restriction is a programming ownership discipline, not a claim that a Markov category lacks copying maps. The cited Fritz Definition 10.1 and Remark 10.13 were independently checked in the primary source: https://arxiv.org/html/1908.07021v8#S10 . They support copy preservation for deterministic morphisms and their cartesian monoidal subcategory; they do not establish arbitrary physical resource duplication or general runner equivalence.

The explicit invalidation counterexample passes independent arithmetic. Worlds with parent set {0} and {0,3} at actuator 2 generate identical records through slot 6 under the proposed client. At slot 7, the original doubled load is 2 and the enlarged model's is 4, above limit 3. The new world lies outside the original one-parent universe, so this is an assumption-retraction witness, not a failure of the original guarantee. The check is reproducible via review/check_programmable_counterexamples.py.

An audit-requested clarification is included in Section 6: suspension after invalidation is not itself a safe physical fallback or continued mission guarantee. Any stop/idle operation needs its own valid pending-effect safety argument, and rechecking consumes resources. Silent physical drift is not automatically detected. The numerical benchmark was not rerun for this programming interpretation.

Following the user's updated criterion, this programming payoff does not require a separate measured speedup. Baseline fairness and attribution cautions above remain applicable to any efficiency claim that is actually made. No general language/compiler, automatic interface extractor, concurrency ownership calculus or stochastic defeasible-confidence system is claimed implemented.

Final guard clarification was checked in obligation 4: each next call requires preserved or re-established validity, and a changed guard/version requires a separately validated replacement contract. The final programmable-interface note passes with no outstanding proof blocker.

Final supplemental hashes:
- theory/Programmable_Defeasible_Interfaces.md: ef63da66122604bafbd7af52238ecdfdd5174ceaaec5fcefc2c71b1a9d991c94
- review/check_programmable_counterexamples.py: 0cee5d754ba3aa836ddd8bfdbe3935a832b339dc051f096ef6a3762a80801c85
- review/programmable_interface_counterexamples.json: 479ba2148ac8859c8a905eff5107a63fd9771c5b67719372f6b7c6ac481eb1e4

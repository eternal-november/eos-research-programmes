# Completion audit: fallible distributed enforcement

Verdict: the completion contract is met at the declared discrete-model scopes. Independent mathematical and program-semantic reviewers found no remaining mandatory gap after checking the corrected current-invocation conduct rule and its matched-world witness. The final integrated evidence is reproduced and bound in verification.json. This audit concerns the [new completion contract](../ENFORCEMENT-CONTRACT.md), not the historical protected-interface package or repository acceptance.

## Result being audited

The result is a theory for declared discrete actual-effect models, with a parametric independently actuated peer-brake family, unbounded safety/service proofs, exact bounded synthesis, local realization and composition laws, and scoped impossibility boundaries. It does not assert that every shared-world invariant is enforceable, that general distributed synthesis is decidable, or that a physical flood-control installation has been validated.

The central positive construction does not mediate every effect through an authorization gate. A rogue motor keeps its independent input. Peer brake engagement physically changes realized motion after a delay, and every brake/planner identity can fail in an admitted scenario. Faulty braking can occur without a lawful command. The controller must protect motion and accumulated heat, preserve actual delivered service through surviving faultable motor/output chains, and justify compliant issued interventions from local evidence.

Its trust statement is bounded and explicit: no inventoried individual motor/output chain, brake planner, brake actuator or source in the defining redundant-source subfamily must always be correct. Surviving capacity, source coverage, timing and physical laws remain premises. This is distributed tolerance of declared faulty mechanisms, not elimination of all substrate assumptions.

## Contract evidence

| Obligation | Supporting artifacts and audited scope |
|---|---|
| E1: semantic core | [THEORY](THEORY.md) fixes component faults, policy-before-fault quantification, causal move order, local observations, queues, global protected outcomes and actual-output epochs. [FINITE](FINITE.md) handles deadlock, absent invocation, initial service ages and finite history monitors explicitly. |
| E2: positive family | [BRAKE-PROOFS](BRAKE-PROOFS.md) derives the identity/downward-quantized parameter theorem and nonempty regimes. [Brakes.lean](Brakes.lean) proves the integer delayed invariants from primitive stream assumptions. Parameters materially change authority, timing, sensing, service, population and thermal allocation. |
| E3: boundaries | [BOUNDARIES](BOUNDARIES.md) proves policy-independent information, authority, initial-delay, joint heat/speed and persistent-enforcement obstructions at named scopes. FINITE adds exact integer policy classification and separate blind/timing obstructions. Identity-quantizer lower bounds are not silently transferred to floor dynamics. |
| E4: effective subclass | [finite_model.py](finite_model.py) implements finite causal verification and exhaustive local-table synthesis. The general theorem is complete for the declared finite kernels, local information interface and memory bounds. The concrete integer family, rather than an unrelated example, passes through it. |
| E5: assembly/realization | FINITE gives the sensor-fault quotient, local frontend, fixed FIFO-to-TwoAct map, integer parameter embedding, and actual-output product certificate. THEORY/BRAKE-PROOFS separately derive shared thermal allocation. Neither an unproved pointwise action lift nor reuse of one shared resource as independent copies is accepted. |
| E6: adversarial coverage | The model retains wrong reports, faulty planners, independently faulty actuators, command refusal, wrongful engagement, withheld output, pending effects and aggregate heating. Executable comparisons retain forbidden effects and record actual failure. The substrate inventory below limits the coverage claim. |
| E7: support | The package has 26 Lean theorem declarations, complete axiom reports, exact-rational checks, exhaustive finite results and independently implemented searches. Written parametric/assembly proofs remain written proofs; a successful finite test is not described as proving them. |
| E8: integration/audit | [ENFORCEMENT-SOURCES](../ENFORCEMENT-SOURCES.md) records primary predecessors and import boundaries. Separate contract, mathematical and program-semantic reviewers challenged the assembled result. Source-bound reproduction and the reconciled contract ledger record closure. |

These entries are evidence, not numerical scores. A missing mandatory obligation would prevent completion regardless of the number of passing examples.

The final corrective code candidate independently reviewed was 1f7f80ca37ba2d871f9cde5ea6e234231f7de7b8. Reviewed context clarifications and the final status/evidence records are carried by the subsequent integration commit; verification.json identifies the exact proof/model/contract inputs. Both fresh reviewers explicitly supported the final scoped verdict, subject to the coordinator reproducing those inputs.

## Independent checking and reproduced evidence

The contract reviewer rejected three potential acceptance loopholes before construction: disconnected finite examples, a vacuous global-rights predicate, and a family obtained merely by renaming instances. The contract now requires concrete linkage, actor-independent outcome witnesses and material parameter variation. Unbounded service and an effective bounded procedure are explicitly chosen commitments, rather than falsely attributed universal requirements of the motivating statement.

A fresh mathematical reviewer reconstructed the parametric median, startup, delay-envelope, service, quantizer and thermal arguments. It compiled the Lean file and inspected all 26 dependency reports; dependencies are subsets of propext, Classical.choice and Quot.sound. It separately checked 15,147 sensor triples and an independently implemented reduced queue/effect model: 149 states and 3,682 edges for a rogue motor, and 79 states and 356 edges for a normal motor. These counts concern that reviewer's smaller representation, not the maintained checker's graph.

The same reviewer independently classified all 64 binary memoryless policy families, checked all ten positive integer force coefficients, a 308-case thermal step lemma, and the 512-table count for a two-state local memory interface. The four winning profiles match the maintained synthesis: every low output is OFF, and at least two planners have high output ON. These are policies at the declared LOW/HIGH interface, not every possible raw-report policy.

A separate fresh program-semantic reviewer tested all seven anti-gate criteria and independently reconstructed the integer model with separate planner and actuator faults. That implementation found 4,129 reachable states and 108,821 edges. Its edge encoding differs from the maintained model's treatment of observations/output events. It also reran the maintained positive checker and product construction, obtaining the exact maintained figures.

The maintained [finite results](finite_results.json) contain:

- 4,129 reachable states and 258,135 enumerated observation/effect transitions in 20 reduced static fault classes for the all-threshold policy;
- all 64 memoryless table families, exactly four winners;
- explicit negative and sensitivity cases, without changing their verification scope;
- a two-device, at-most-one-faulty-motor product certificate covering 300 joint fault combinations and 18,125 checked boundary effect profiles.

The product's 9,275,697-state figure is the size bound of a constructed Cartesian closed-set certificate. The full global graph was not enumerated. Its preservation argument uses coordinate projection and actual output sums; independent reviewers also reconstructed the arithmetic of this bound and the boundary profile count.

The generic checker was separately challenged with missing continuations, absent invocations, nonzero initial service age and a service-free cycle that is not a bottom component. The program reviewer tested that a faulty actuator's effect remains present despite a lawful OFF command, that an intact planner's unlawful ON is rejected even when its actuator stays OFF, and that faulty planner commands enter an intact actuator's queue.

Reproduce the integrated evidence from the repository root with:

```powershell
C:\Python312\python.exe -B theories-and-designs/byzantine-control/enforcement/verify.py --check
```

[verification.json](verification.json) binds the theorem, model, result and governing-document inputs by normalized-text SHA-256 and records fresh outputs. The checker compiles all Lean declarations, checks their axiom reports, reproduces arithmetic witnesses and reruns exhaustive finite evidence. It rejects changed inputs before comparing results. Its own implementation is reviewed code, not a separately mechanized trusted verifier.

## Corrections that affect reuse

Independent review found and repaired substantive issues rather than merely confirming the proposed design.

The parametric upper proof needed \(\tau^0\le T\) for normal as well as faulty motors. Without it, a normal motor can overwhelm every brake while satisfying the other displayed margins. That counterexample is retained in the exact boundary checks. Released initial queues also need startup headroom; an initially safe speed at the upper boundary can already be losing before delayed engagement.

Source faults cannot be used to remove an intact planner from its response duties. Redundant evidence is therefore local to every intact planner, including one behind a faulty actuator. Common-source faults count by their actual affected paths. The blind information comparison changes the nominal observation map visibly instead of silently corrupting all sources while claiming the same truthful-majority premise.

The real lower-bound impossibilities require identity quantization. Floor dynamics can create safe plateaus and erase small accumulated heat inputs; their separate integer results are retained rather than reported as failed searches. Positive downward-quantizer preservation uses different, explicitly proved one-sided inequalities.

The observation-to-command frontend loses raw-report distinctions. Its computation remains inside the faultable planner, and the finite completeness claim is limited to the declared frontend/information interface. Sound implementation transport does not automatically give strategy reflection at the same memory bound.

The stale-observation correction fixes the conduct predicate to actual current invocation speed while leaving old samples as local inputs. The all-policy timing obstruction then uses two indistinguishable histories, not an implicit change to a historical-evidence conduct law. A selected policy's first discovered stale-evidence failure is kept separate from that universal proof.

Separate thermal stores and a single shared cooling process are different plants. The finite product wrapper proves the former; the parameter theorem's summed heat inequality proves the latter under its stated dynamics. A shared-capacity counterexample demonstrates why the distinction matters.

## Primitive coverage and residual assumptions

| Primitive interface | Admitted failures or uncertainty | Remaining premise or limitation |
|---|---|---|
| Motor and output chain | Unknown faulty chain can drive, refuse, switch input and withhold actual output. | Bounds on input/effect range; fewer faulty output chains than the service allocation tolerates; intact output relation is stipulated motion/transport service. |
| Brake planner | Arbitrary issued commands when compromised; intact planners may receive faulty source data. | The joint planner/effect union bound must leave sufficient actual influence. |
| Source, calibration, delivery and identity path | Arbitrary faulty values, substitutions and missing values within each local affected-path bound; different local vectors. | Distinct source paths, surviving correct-epoch coverage, bounded intact error, and the actual dependency structure must be justified by an application. |
| Brake effect and timing path | Refusal or engagement independent of the issued command, including wrongful engagement. | Declared physical force alphabet; intact FIFO timing; unbounded jamming, severed mounts and concealed bypasses are not tolerated. |
| Local invocation | Missing invocations are represented by the generic finite semantics. | The positive peer-brake subclass assumes regular intact invocation and bounded effects; arbitrary missed calls are not silently covered. |
| Thermal/material substrate | All admitted engagement contributes actual heat, including malicious intervention. | Passive dissipation, unilateral motion, quantization and force/heat relations are model laws, not empirical validation or fault-free programmable enforcers. |
| Supply, resources and startup | Loss of selected drive/output paths is faultable; bad startup and resource balance have explicit obstructions. | Sustained normal supply and declared initial membership are necessary. Finite fuel, wear and common-cause total loss need additional state and a new proof. |
| Specification and authority | Factive compliant-response duties coexist with unconditional world-level protections. | Rules and protected interests are fixed. Universal legality of Byzantine acts and legitimacy/governance of the rules are not solved. |

These are genuine bounds on the theorem. They do not leave a hidden obligation to implement an always-correct global selector, command gate or service dispatcher. They do leave application-specific obligations to validate the plant, information and timing relations. The result therefore supports a mathematical family of distributed invariant enforcement mechanisms; it is not evidence of a safe deployed hydraulic or societal system.

## Repository and completion boundary

The retained integration branch is codex/byzantine-control-20261021 at C:\Users\Sean\.codex\worktrees\byzantine-control-research\eos-garden. Concurrent writers used separate finite/proof worktrees and returned explicit commits. The historical protected-interface proof/checking packet is unchanged. The primary checkout's unrelated dirty paths and index remain outside this work; no primary merge or remote push is part of this delivery.

Goal completion means E1-E8 are discharged at the scopes above. It does not accept the theory on the repository owner's behalf, close all future research, or reinstate the earlier broad completion claim about independently acting communities in general.

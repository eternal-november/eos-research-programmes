# Existing research against the revised Byzantine control contract

Verdict: the existing package is a substantial reusable foundation, but it does not discharge the revised [contract](DOWNSTREAM-CONTRACT.md) and [fault coverage](FAULT-COVERAGE.md). The largest substantive gaps are complementary distributed inference, consequential changing compromise with retained state/knowledge, and their assembly with coupled control, constrained enforcement, resources and service. This is not a verdict that the prior scoped mathematical results are false. Nor does their earlier completion audit establish completion under the revised target.

The remaining work is organized in [REMAINING-PROGRAM](REMAINING-PROGRAM.md). No new Goal is created by this audit. Repository acceptance remains separate.

## Audited snapshots and evidence

Requirements snapshot: 37cc72365152b74591196ec86f3f5230980b7974 on codex/byzantine-program-enactment-20261022, including DOWNSTREAM-CONTRACT and FAULT-COVERAGE. Science snapshot: bcf7c9837a2f4ac9b55f3e13a6e0a550e6d6cc41 on codex/byzantine-control-20261021, in C:/Users/Sean/.codex/worktrees/byzantine-control-research/eos-garden. Both checkouts were clean when inspected. The current formulation worktree contains an older worker copy of the science, so this audit reads the separate integration snapshot; relative links into that older copy are not used as evidence of the latest result.

Fresh work: three complementary read-only audits inspected maintained documents, theorem signatures, source interfaces and selected executable paths across research, enforcement and integration. The coordinator inspected the synthesis, source ledgers, core/scoped constructions and verification runner, reconciled their returns, and independently recalculated every normalized source digest in integration/verification.json. All 101 bound sources matched; the record reports verification_passed=true and 260 declarations across the retained and integration packages. This confirms identity with the previously checked package. It is not a fresh rerun of every proof or executable enumeration, and declaration counts are not a measure of conceptual completion. The unmaintained exploratory research-note-slop directory is not treated as checked evidence.

The audit is primarily a fresh scope/refinement assessment. Historical mathematical checking remains evidence at its stated trust boundary. No new proof defect is established here; most findings are missing scope or unsupplied internal services. Definitions and source expressibility are credited separately from a construction or a proved source application.

## Evidence bundles

All science links below refer to the integration worktree at the pinned science commit. Git supplies immutable recovery if that checkout later changes.

| Key | Existing evidence | What is reusable |
|---|---|---|
| S1 | [CORE](C:/Users/Sean/.codex/worktrees/byzantine-control-research/eos-garden/theories-and-designs/byzantine-control/integration/CORE.md), CoreBridge.lean, Unclocked.lean and research/Execution.lean | Local initialization, observation/history uniformity, masked absent/faulty calls, actual effects, failure completion and static source/run correspondence. |
| S2 | [EVIDENCE](C:/Users/Sean/.codex/worktrees/byzantine-control-research/eos-garden/theories-and-designs/byzantine-control/research/EVIDENCE.md), Evidence.lean and evidence_model.py | Fault-labelled hypotheses; robust decisions; witnessing/attribution separations; scalar timed interval inference and packet scope/freshness checking under the old protected schedule/effect premises. |
| S3 | [Enforcement THEORY](C:/Users/Sean/.codex/worktrees/byzantine-control-research/eos-garden/theories-and-designs/byzantine-control/enforcement/THEORY.md), BRAKE-PROOFS, FINITE and [BOUNDARIES](C:/Users/Sean/.codex/worktrees/byzantine-control-research/eos-garden/theories-and-designs/byzantine-control/enforcement/BOUNDARIES.md) | Recurrent independent-effect braking, static joint role faults, local robust scalar sensing, delays, actual output service, heat/admissibility bounds and physical/information obstructions. |
| S4 | [STRUCTURE](C:/Users/Sean/.codex/worktrees/byzantine-control-research/eos-garden/theories-and-designs/byzantine-control/integration/STRUCTURE.md), Structure.lean and Assembly.lean | Exact fixed-interface/supplied-envelope local-policy relations, constructive join-tree gluing, source transport, shared decision variables and compatibility failures. |
| S5 | [EXCHANGE](C:/Users/Sean/.codex/worktrees/byzantine-control-research/eos-garden/theories-and-designs/byzantine-control/integration/EXCHANGE.md) | A real same-plant, same-mission removal of a torque limiter, failure of the old policy, and an independently enforced replacement. |
| S6 | [ENACTMENT](C:/Users/Sean/.codex/worktrees/byzantine-control-research/eos-garden/theories-and-designs/byzantine-control/integration/ENACTMENT.md) and [APPLICATIONS](C:/Users/Sean/.codex/worktrees/byzantine-control-research/eos-garden/theories-and-designs/byzantine-control/integration/APPLICATIONS.md) | Static-fault physical capacity substitution, false readiness/failed installation, key versus executor compromise, actual overlap/service, source-field maps and retained pending effects. |
| S7 | [ALIGNMENT](C:/Users/Sean/.codex/worktrees/byzantine-control-research/eos-garden/theories-and-designs/byzantine-control/integration/ALIGNMENT.md), research/DIGITAL and QUORUM-ALIGNMENT | Operational signed BFT baseline, actual issuance/receipt, quorum distinctions, evidence-to-effect rows, a small active-probe service-cost example. |
| S8 | [HIERARCHY](C:/Users/Sean/.codex/worktrees/byzantine-control-research/eos-garden/theories-and-designs/byzantine-control/integration/HIERARCHY.md) | A sound finite source-to-game route with complete-arena information checking and an imported synthesis theorem. Its physical instance assumes timely common report delivery; the imported synthesis algorithm was not executed. |
| S9 | [TIMED-RECOVERY](C:/Users/Sean/.codex/worktrees/byzantine-control-research/eos-garden/theories-and-designs/byzantine-control/research/TIMED-RECOVERY.md) and research/INSTITUTION | Queue drain/restart/reservation lemmas, institutional distinctions and retained-key counterexamples under explicitly protected gate/isolation/installation roots and a static coalition. |
| S10 | [Integration AUDIT](C:/Users/Sean/.codex/worktrees/byzantine-control-research/eos-garden/theories-and-designs/byzantine-control/integration/AUDIT.md), verify.py and verification.json | Historical independent checking, real repaired defects, source binding, axiom restrictions and executable verification infrastructure. |

## Verdict by revised obligation

| Obligation | Existing support | Remaining burden |
|---|---|---|
| BC1 common faults/control | Substantial static semantic core; local information and actual effects carefully preserved. | Extend or soundly relate evolving support, contaminated re-entry, retained secrets, acquired privileges and changing dependencies. Fixed correct:F→I→Prop is not yet a changing-compromise theorem. Map the new taxonomy into actual source behaviors. |
| BC2 information | Useful general soundness/refinement laws; real scalar timed inference, robust local fusion and epistemic separations. | Major constructive gap: complementary heterogeneous information obtained through actual exchanges/fallible inquiry before a deadline, with uncertain independent actuation and compromised inference executors. |
| BC3 feasibility/coordination | General local-uniformity characterization, finite fixed-interface synthesis, substantive force/time/heat boundaries and permission supports. | Tie structural information/influence/resource/time comparisons and coordination weakening to the new positive family; current supplied-Q results do not construct missing information services or a maximal winning region. |
| BC4 positive control | Strong reusable recurrent gate-free enforcement with simultaneous bounded sensing/effect faults and faulty decision executors. | The revised combined family is not established: locally sufficient scalar frontends and supplied compound observations do not satisfy complementary inference, costly fallible inspection and their resource/capability changes. |
| BC5 assembly/exchange | Genuine gluing/source-program laws and a real limiter replacement; more than shared terminology. | Construct and preserve the missing information/transition interfaces under the same faults. Current composition assumes their useful frontends and supplied invariant envelopes. |
| BC6 capability changes | Substantive make-before-break substitution, false/failed readiness, retained hostile effects and continued service under static faults. | Major new result: bounded acquired/mobile compromise, released-but-contaminated state, accumulated authority/knowledge and locally justified restoration. Static roster/keys and intact-path persistence do not suffice. |
| BC7 specialization/realization | BFT/quorum recovery and static source maps are largely reusable; meaningful representation checks already exist. | Transport the new mechanisms and scopes, recheck time/state/locality after evolution, and close new source/assurance mappings. No reason to rebuild the BFT baseline or invent a universal synthesizer. |

No whole BC obligation is marked discharged here: each either lacks a central construction or depends on the new combined realization. This does not erase successful subresults or require repeating unchanged proofs.

## Decisive scope findings

**Information is the largest old-intent gap.** Evidence.lean's actual_hypothesis and robust_decision_sound are useful general facts, but source-law soundness and sufficiently discriminating evidence remain premises. shared_honest_source_bound requires a surviving source already to constrain the consumed distinction. The timed scalar construction predicts using a known committed gate-published input schedule, authentic synchronized time and an exclusive input/service interface. Gate-free planners instead receive redundant measurements of their own sufficient scalar threshold. Neither supplies the required complementary distributed information construction.

ALIGNMENT's evidence experiment has one compliant planner; intact sensors directly report the bad-actuator mode. Its active probe changes the observation stage to a full report vector while consuming a service tick. This usefully establishes that information acquisition costs service, but does not construct a fallible informative inspector or a recurrent distributed inquiry mechanism. HIERARCHY's public-report specialization supplies timely common reports as an assumption. Reusing it as the missing information service would reproduce the original burden displacement.

**Independent enforcement is earned and should be retained.** S3 permits compromised planners, arbitrary affected readings, independent malicious brake/motor effects, queues and physical heat. The same static joint scenario can impair evidence and realization. Its permissions do not filter harmful hostile effects. These facts must not be reported as absent merely because the required richer information layer is missing.

**Composition is substantive but indexed.** S4's join is exact for a supplied envelope Q, chosen observation/memory interfaces and local initializers; recurrence may use a supplied rank. It constructs local tables and transports them to actual source runs. Its shared-planner construction has genuinely shared policy variables and incompatible-duty examples. However, the compound PAIR_HIGH signal arrives through a supplied frontend, and private paths already suffice for protection. This is useful compositional machinery, not evidence that complementary information has been acquired or finite inspection resources managed.

**Handover is not mobile recovery.** S6 proves surviving-effect counts across old/spare pairs, tolerates false READY and failed installation, preserves pending commands, and allows a released bad actuator to continue bounded effects. A premature-retirement trace demonstrates real harm. But the actual Fault record is fixed; historical READY supports later action by an intact warm-path persistence condition. There is no acquired-knowledge/contamination state or later transition from compromised execution back to warranted compliant state. Old S9 recovery explicitly assumes protected isolation and clean-key/installation roots. Its useful queue lemmas do not close M41.

**Some new coverage duties genuinely strengthen the old scope.** The old package did not construct cleansing or mobile recovery: its older conditional recovery theorem used protected isolation and clean-key/installation premises, and the newer static enactment construction did not inherit them as achieved capabilities. Its failure to discharge the newly mandatory bounded changing-compromise duty is not evidence that its static theorem was false. By contrast, complementary sensing and maintained information-to-effect construction were central to the motivating intent but previously satisfied with narrower artifacts. The remaining program must distinguish extensions from repairs rather than treating every gap as the same failure.

## Mandatory family status

R means a substantive scoped result is reusable; P means only part of the listed modes or required interpretation is supported; G means the decisive new result is absent from the maintained package inspected. These are support grades, not completion percentages. Even an R result must be transported into any changed family before its guarantee is reused. S1–S10 identify the evidence above; remaining work is assigned to W0–W6 in REMAINING-PROGRAM.

| Family | Grade and evidence | Remaining obligation / destination |
|---|---|---|
| M01 initialization | P; S1/S3/S6/S9 establish explicit nonempty safe starts and restart boundaries. | Contaminated initialization/re-entry and recoverable regions for evolving faults; W1/W3. |
| M02 source/refinement omission | R within checked encodings; S1/S7/S8/S10 repaired real information/event/time losses. | Actual new source interpretation and coverage mapping; W0/W5/W6. |
| M03 common/model error | P; S2 calibration alternatives/obstructions and nominal uncertainty. | Useful heterogeneous model alternatives/common-mode validity in the new family; W2/W5. |
| M04 specification meaning | P; S3/S6 separate world harm, conduct and actual service; fixed-rule conflicts exist. | Complete reference-meaning and nonvacuity audit for changed monitors; W0/W6. |
| M05 assurance errors | R for the historical package; S10 source checks, axiom guards, independent defect repairs. | Rebuild affected checks and independent adequacy review; W6. |
| M06 sensing error | R for scalar/path bounds; S2/S3. | Complementary heterogeneous observations and source mapping; W2. |
| M07 evidence fabrication/selection | R for attributed static sources; S2/S3/S7 admit arbitrary affected values and omissions. | Preserve selection/provenance in actual new exchanges/probes; W2/W4. |
| M08 inspection | G for required positive fallible acquisition; S2/S7 provide separations and a deterministic probe-cost example. | Faultable informative inquiry with time, damage and service costs; W2/W4. |
| M09 clocks/freshness | P; S2 scoped age/epoch checking; S3 timing-path faults count against bounds. | Establish/reduce consumed timing and freshness bounds under admitted faulty paths; do not assume an unexplained successful synchronization service or infer freshness from untrusted timestamps. Legitimate intact timing primitives remain allowed; W2/W5. |
| M10 history corruption | P; S1/S6/S9 retain queues, scopes and history. | Restored execution with contaminated memory/history; W1/W3. |
| M11 inference corruption | R for bad physical planners; S3/S6. | Fault tolerance of the new complementary inference mechanism itself; W2/W4. |
| M12 semantic mismatch | P; S1/S7/S8 strong representation checks are mainly assurance evidence. | Operational referent/unit/schema and duplicate-domain interpretation; W1/W2. |
| M13 decision executors | R; S3/S6 tolerate consequential planner/authority failures. | Preserve this through the new evidence layer without a trusted fusion root; W4. |
| M14 transport | P; S2/S7 actual faulty reports, selective delivery, stale/duplicate handling. | Timely complementary exchange and load/escalation semantics; W2/W4. |
| M15 equivocation | R under static attributed interfaces; S2/S3/S7. | Preserve correlated local views in the new mechanism; common-report hierarchy is not a replacement; W2/W5. |
| M16 partition/delay | P; S6 administrative delay can be indefinite; control paths retain timing bounds. | Actual information-path loss, availability margins and source-valid limitation; W2/W4. |
| M17 scheduling | P; S1 absence semantics, S3 queues, S6 idle administrative choices. | Consumed computation/inspection resources and timing interface mapping; W2/W4/W5. |
| M18 concurrency/TOCTOU | P; S6 real installation overlap and queued effects. | Evidence becoming stale under compromise/mode changes and shared resources; W3/W4. |
| M19 identity independence | P; S3 physical paths/shared owners; S6/S7 distinct-signer scope. | Explicit alias/domain reduction and common-owner obstruction used by inference; W1/W2. |
| M20 credentials | R for static key/executor distinction, scope/replay/dedup; S6/S7/S9. | Accumulated stolen authority and evidence applicability after changing compromise; W1/W3. |
| M21 authority abuse | R for fixed response rules, arbitrary bad effects and conflicting duties; S3/S4/S6. | Reuse under the selected new mechanism's actual authority interpretation; W4/W5. |
| M22 monitor tampering | P; S6 separates actual world/provenance from reported registration. | Explicit mapping of faultable operational classification to reference mission; W1/W4/W6. |
| M23 uncommanded effects | R; S3/S6 retain autonomous and post-retirement hostile effects. | Map coupled source channels/changed reach faithfully; W4/W5. |
| M24 failed realization | R; S3/S6 include refusal and bounded wrong engagements. | New target/actuation modes require matching source maps; W4. |
| M25 dynamics | R for declared delayed discrete recurrences and heat; S3/S6; protected continuous support S2/S9. | C04 realization if continuous claims are made; W4/W5. |
| M26 resources | P; S3 has real cooling/service margins and persistent-heating failure. | Resource-consuming sensing/repair/provocation and cumulative reserves in the joint loop; W4. |
| M27 local conformance | R for shared heat/decision and incompatible-duty joins; S3/S4. | Apply to the new coupled information/resource boundaries; W4/W5. |
| M28 changing topology | P; S4 switching force modes and S6 old/spare changes. | Loss/restoration of an information dependency and acquired reach; W1/W3/W4. |
| M29 environment | R for bounded drive/thermal assumptions and boundary counterexamples; S3. | Preserve common stress and new primitive coverage; W0/W4/W6. |
| M30 harmful enforcement | R scoped; S3 heat/conduct and S6 false-readiness-induced release matter physically. | Jointly link heterogeneous false evidence and fallible inquiry to these effects; W2/W4. |
| M31 runtime assurance | P; S6 faultable authorities/installers/keys; S3 faulty planners. | Active inspector/inference/monitor services in the combined family; W2/W3/W4. |
| M32 detection/attribution | P; S2 precise separations/obstructions. | Recurrent decision/inspection policy, false alarms and actual service; W2/W4. |
| M33 nonblocking | R; S1/S3/S6 actual effects, failure completion and service/holding arguments. | Recheck changed evolution and acquisition loops; W3/W4/W6. |
| M34 fallback denial | P; S3 persistent heat/service and S6 indefinite failed-install holding. | Repeated costly inspection/repair and protection depletion; W4. |
| M35 development/common defects | P; S3/S6 arbitrary fixed compromised code/effect/installer behaviors. | Common-domain interpretation and changes of support after malicious updates; W1/W3. |
| M36 contaminated repair | P; S6 false/failed installation and S9 contamination boundaries. | Genuine local restoration without a clean-state oracle; W3. |
| M37 transfer/handover | R for scoped static substitution, pending effects and key-scope checks; S6. | Changing compromised support and retained state/evidence; W3/W5. |
| M38 exclusion | R for residual hostile force and loss of necessary capacity; S3/S6. | Consequences for useful observation paths and changed compromise; W3/W4. |
| M39 correlated faults | R static; S1–S7 use one joint f and affected-path accounting. | Extend the same joint support through inference and evolution; W1/W4/W5. |
| M40 adaptive tactics | R; S3/S6 quantify state/current-command-aware causal adverse choices. | Do not confuse this with acquiring new control; preserve timing order in new reductions; W1/W4. |
| M41 evolving compromise | G; S9 has residual-key witnesses, but S1/S6 use static support. | New evolution semantics and consequential bounded positive restoration; W1/W3. |
| M42 propagation/escalation | G for acquired support; arbitrary outputs alone are insufficient. | Represent changed accessibility/privilege and preservation or boundary; W1/W3. |
| M43 dormancy/intermittence | R within fixed compromised powers; S3/S6 may imitate correct action indefinitely. | Release/reacquisition and regained duties belong to W1/W3. |
| M44 leakage | P; S3 already tolerates strong current-state/command knowledge, S6 stolen keys. | Formalize redundant leakage versus new enduring capability; W1/W3/W5. No privacy claim follows. |
| M45 certificates | R for static issuance/scope/freshness and physical applicability; S2/S6/S7. | Applicability after corruption, schema, model or capability change; W3/W5. |

The row inventory is a completeness aid for this audit, not a sum of independent research projects. The majority of remaining rows share the same missing information, evolving-state, and joint-resource constructions.

## Conditional activation and exclusions

| Profile | Current disposition and continuation rule |
|---|---|
| C01 open admission | Inactive for the fixed physically indexed roster. Identity/domain accounting M19 remains mandatory. Activates if the new mechanism needs untrusted new identities or constructs an attacker-sensitive population relation. |
| C02 probability/randomness | Inactive for deterministic positive control. A probability-one impossibility discussion does not create a probabilistic positive result. Activate if a mechanism consumes random/private/statistical assumptions. |
| C03 learning | Inactive: current nominal models are supplied, not learned by a resilient adaptive process. Mutable compromised inference still counts under M11. |
| C04 continuous/hybrid | Active for retained S2/S9 continuous claims under their stronger premises. The new gate-free discrete family has no automatic continuous realization; any such source claim needs its own intersample/time argument. |
| C05 privacy/additional properties | Standalone secrecy/noninterference inactive. Existing world safety, conduct and service remain mandatory; leakage that changes adversarial capability is M44. |
| C06 computational security | Existing signatures are ideal interfaces. No cryptographic-library security result is claimed. A quantitative computational guarantee would activate its additional proof. |
| C07 arbitrary-state stabilization | Inactive. Explicit safe starts/restart regions are not universal self-stabilization. |
| C08 evolving governing rules | Inactive for fixed rule sets; changing recognized state under them remains mandatory BC6 work. |
| C09 platform-specific attacks | Inactive absent a platform security/deployment claim. Abstract escalation and source applicability remain mandatory. |
| C10 asynchronous/renewal continuation | Static recurrent service and failed-install holding have scoped proofs. No asynchronous partition-healing or indefinite mobile renewal is established. Any such extension needs its actual opportunity, rate, resource and recurrence proof. |

E01–E07 remain legitimate exclusions of stronger solution tasks, not ignored effects. Their boundaries are partly documented in the old package, but the new mechanism must preserve the same responsibility test. A fixed cohort does not solve identity creation; ideal cryptography does not solve key retention; correct proof checking does not establish adequate source modeling; a force bound does not justify erasing a source bypass. The planned result map keeps these distinctions explicit.

## Are the targets adequately refined

Yes, materially and demonstrably better than the old handoff. Old R2's requested model, separation and inference certificate could be met by the existing scene/scalar work. Revised BC2 correctly refuses to treat that as the required complementary distributed information result. The old static handover result was expressly bounded; M41 now identifies the precise additional state and positive transition duty instead of permitting static-to-mobile inference. The revised contract also rejects artificial separation of evidence/enforcement faults, hidden decision roots, zero-budget positive coverage, silent quiescence, and result modes chosen after observing success.

The refinement is sufficient to govern selection and checking of the next research targets. It is not a mechanical guarantee that future interpretation will be faithful. The remaining discretion lies in choosing a primitive structural family, matching concrete result modes to shared theorems, and validating source abstractions. W0 and the named result targets in REMAINING-PROGRAM make those choices reviewable before expensive proof work. They are operationalization of the existing obligations, not a request for the user to redesign the intent or approve each technical detail.

Recommendation: proceed from this contract and audit-derived program rather than enlarge the taxonomy again without a consequential unmapped failure. Use an independent reviewer to reject inadequate family choices before construction, and preserve the original fault-tolerance questions at closing review. The governing target remains provisional for repository acceptance; this audit does not accept it on the user's behalf.

## Review of the audit and remaining program

The three read-only auditors also reviewed the coordinator's consolidated audit and proposed program. They supported the reuse/gap distinction and identified concrete repairs: correct the shared signal name to PAIR_HIGH; allow justified primitive timing rather than require universal clock reconstruction; require complementary information at the relevant responders without forbidding every more-informed actor; distinguish inspection construction from deriving sensing physics; challenge false completion credit rather than prohibit oracle comparisons; preserve a common mission/accounting basis without erasing the new mechanism's real effects; make propagation-to-acquisition transport explicit; separate safe holding from functional restoration; and close the information/repair/control proof cycle through initialized joint induction. Those changes are integrated.

The relative-effort range in REMAINING-PROGRAM is a coordinator planning judgment informed by the three audits, not an empirically validated productivity estimate. Reviewers found its stated denominator, shared-work accounting and uncertainty qualifications appropriate. Source-class admission, successful constructive mechanisms, and eventual scope closure remain future evidence obligations. This audit has not manufactured their completion from the strength of its review process.

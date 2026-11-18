# Byzantine control with permissive authorization and bounded physical influence

This document remains the checked discrete increment. The full continuation, including general semantics, timed control, institutional recovery and program-level audit, is maintained in [PROGRAM.md](PROGRAM.md).

## Result and scope

This research increment constructs a distributed controller that preserves an integer inventory invariant and delivers one unit of service at every modeled epoch despite noisy sensing, recipient-dependent Byzantine reports, Byzantine authorizers, and hostile physical flow. Its authorizers need neither the true inventory nor the faulty identities. They need not agree on a single proposed action. They endorse all actions safe for their own evidence; a trusted gate selects and realizes one sufficiently endorsed action.

The distinguishing result is an assembly theorem with constructed premises, together with an obstruction to a simpler coordination interface. For the same plant and fault family, no two median-only singleton selectors can always produce matching locally certified actions. The permissive protocol nevertheless always supplies a certificate and preserves the invariant indefinitely. The effect of reducing coordination is therefore a proved change of interface, not a claim that agreement never matters.

Fourteen declarations in [Control.lean](Control.lean) check the core arithmetic, certificate safety and availability, invariant induction, the singleton obstruction, and two general fault-family access theorems. [check_models.py](check_models.py) exhausts finite attack classes, reconstructs a two-round signed Byzantine broadcast baseline, and tests epistemic delivery correspondences and failure witnesses. [results.json](results.json) is reproducible output. [SOURCES.md](SOURCES.md) records the delegated prior-art assessment and import boundaries. [COMPLETION.md](COMPLETION.md) separates kernel proofs, executable evidence, semantic review, and remaining work.

**Verification does not enact repository acceptance.** This is a checked discrete research fragment, not an accepted general theory, a new consensus algorithm, a complete HotStuff proof, or a verified physical deployment. No novelty claim is made for quorum systems, bounded synthesis, epistemic tracking, or event models with postconditions.

The source program asks how ledger-state control extends to generally specified state. Here the extension replaces a replicated value's conflict-exclusion requirement with a robust action-permission requirement. That replacement is justified only because an explicit realized-effect model and exactly-once gate preserve the physical invariant. Conversely, applying multiple individually certified commands defeats the theorem. The generalization is a law for composing evidence, permission, selection, and effect, with the distinctions that its application must retain.

## Common execution contract

The semantic center is a distributed adversarial transition system. Correct components choose their actions from local histories; the analyst's global state and faulty set are never runtime inputs. A fixed joint coalition is chosen before execution and remains fixed. The adversary can correlate all its reports, omissions, endorsements, and physical interventions, observe the current state and completed correct actions, and choose the current bypass accordingly. It has no access to future environmental choices. The initial scenario family is nonempty.

The digital and physical instantiations share this contract but have different identity universes and transition mechanisms. Recovery of the digital instance means preservation of its stated agreement, validity, and termination properties under its own context, not literal equality of physical and digital traces.

The physical context \(\theta_P\) is as follows.

| Field | Binding and consumer |
|---|---|
| State and safety | \(x_t\in\mathbb Z\), with \(S=\{2,3,4,5,6,7,8\}\). All initial states in \(S\) are allowed. Safety is checked at epoch boundaries. |
| Correct command | \(u_t\in\{0,1,2\}\), measured in stored-volume units injected during an epoch. These are fixed command alphabets, not hidden-state-dependent types. |
| Realized effect | \(x_{t+1}=x_t+u_t-1+b_t\), where \(b_t\in\{-1,0,1\}\). The \(-1\) is an actually delivered unit through a stipulated reliable service port. |
| Fault family | Six identities, three sensors \(S_0,S_1,S_2\) and three authorizers \(A_0,A_1,A_2\). All \(B\) with at most one sensor and at most one authorizer are admitted. The same \(B\) is used by every component and every epoch. No stochastic independence is assumed. |
| Physical adversary | The same adversary controls \(b_t\) within the stated bound for every \(B\), including the empty set. This additional bounded physical interface is not derived from the six-identity count. |
| Sensing | Each correct sensor chooses a fresh integer \(y_{s,t}\in\{x_t-1,x_t,x_t+1\}\) and sends that same reading to each authorizer. Noise is nondeterministic and may correlate across sensors and epochs. Byzantine reports may differ by recipient. |
| Authentication | Sender identities, epochs, and payloads are bound by ideal unforgeable authentication. A correct identity cannot be impersonated. Multiple packets from one identity never count as multiple inputs or shares. |
| Collection | An authorizer forms a three-entry vector only after the round cutoff guaranteeing all correct reports have arrived. Missing or malformed faulty entries become a fixed integer sentinel, chosen as zero in examples. Multiple faulty values are reduced deterministically to one entry. |
| Realization | A trusted gate receives endorsements, waits until the endorsement cutoff, selects the least certified control, and applies exactly one injection. It rejects stale epochs and duplicate execution. The reliable service port delivers one unit. No unmodeled actuator can bypass these restrictions except through \(b_t\). |
| Timing | Each epoch has sensing/collection, endorsement/collection, and one plant transition. No plant drift occurs between sensing and that transition. The discrete scheduler advances through these phases. This is synchronous logical time; no empirical seconds-per-round or continuous-time bound is claimed. |

All correct reports arriving on time is a **safety as well as service** premise. A sentinel is harmless only when at most one entry lacks the honest error bound. Correct endorsement delivery and execution by the round boundary supply service. Timely communication is stipulated, not proved by authentication.

The service floor is one delivered volume unit per completed epoch, with completion required by the synchronous transition rule. Every \(T\)-epoch prefix delivers exactly \(T\) units. This is stronger than eventual service in this model, but gives no real wall-clock rate until a timing realization is supplied. The inventory reserve permits withdrawal of one unit even if a hostile removal of one occurs first; the theorem still concerns sampled states rather than all intermediate flow orderings. A faulty service port is outside \(\theta_P\).

The representation deliberately drops continuous fluid dynamics, fractional inventory, within-epoch safety, calibration drift beyond the error envelope, packet queues spanning epochs, mobile corruption, key compromise beyond \(B\), adaptive membership, and competing institutional jurisdictions. These are not harmless quotients for every question. The counterexamples below show that fractional state, stale evidence, missed reports, and cumulative effects can already change this theorem's verdict.

## Local policy and the constructed composition theorem

Let authorizer \(i\)'s received vector have median \(m_i\). Its local information envelope and certified controls are

\[
E(m_i)=S\cap[m_i-1,m_i+1],\qquad
C(m_i)=\{u\in\{0,1,2\}:\ \forall z\in E(m_i),\ \forall b\in\{-1,0,1\},\ z+u-1+b\in S\}.
\]

The policy is executable: compute the median, enumerate three controls over at most three integer states and three bypass values, and sign every passing \((\text{epoch},u)\). A correct authorizer treats an empty envelope as inconsistent evidence and issues no endorsement. Under \(\theta_P\), emptiness is unreachable. This off-model rule is not a guaranteed fallback for a changed environment.

The gate validates distinct epoch-bound shares. An action is certified when at least two authorizers endorsed it. The gate chooses the least certified action at its cutoff. A Byzantine authorizer can endorse any subset of the three controls or withhold everything. A Byzantine sensor can make different authorizers obtain different medians. The gate has no sensor and receives no analyst state.

For a nonempty envelope with endpoints \(L,U\), the certificate calculation has the exact closed form

\[
C(E)=\{u\in\{0,1,2\}:4-L\le u\le8-U\}.
\]

The minimum successor is \(L+u-2\), and the maximum is \(U+u\); these extrema prove both directions. More generally, an interval \(E=[L,U]\), safe interval \([\ell,h]\), demand \(d\), hostile bound \(r\), and capacity \(c\) give \([0,c]\cap[\ell-L+d+r,\ h-U+d-r]\), intersected with the command alphabet. That algebraic local certificate is not a complete distributed availability theorem.

**C1 — Coverage.** The median of three numbers, two in \([x-1,x+1]\), lies in that interval. Every correct authorizer therefore has \(x\in E(m_i)\), and \(E(m_i)\subseteq[x-2,x+2]\cap S\). The third report is unrestricted; an omission sentinel is included. The Lean declarations median_bound and envelope_covers check the median bound and coverage. The envelope-width inclusion is their derived arithmetic consequence.

**C2 — A common locally certifiable control.** Define an analyst witness

\[
a(x)=\min(2,\max(0,6-x))=
\begin{cases}2&x\le4,\\1&x=5,\\0&x\ge6.\end{cases}
\]

For every \(x\in S\) and sound median \(m\), \(a(x)\in C(m)\). If \(x\le4\), each envelope lies between 2 and 6, so injection 2 yields successors between 2 and 8. At \(x=5\), envelopes lie between 3 and 7, and injection 1 works. If \(x\ge6\), envelopes lie between 4 and 8, and injection 0 works. These exhaust the integer carrier. The declaration common_certified checks the statement. **No actor evaluates \(a(x)\).** It proves overlap among independently computed endorsement sets.

**C3 — Safety and availability of the same protocol.** Every two-share certificate contains a correct authorizer. That signer's envelope contains the true state and its endorsed action is robust-safe there. Every accepted control therefore preserves \(S\), even when the adversary decides which optional endorsements to send. Conversely, the at least two correct authorizers all endorse \(a(x)\), so their timely messages alone produce a certificate. The gate's deterministic selection has a nonempty domain. The declarations gate_safe and gate_available check the support-level claims.

The formal predicate Accepted overapproximates actual certificate support: a Byzantine signer may support anything, while a correct signer may support only a locally certified action. It is not a signature verifier. The operational map from authenticated shares to this predicate uses distinct identities, epoch binding, unforgeability, and correct checking. The reverse availability map uses transmission of **all** endorsements and timely delivery. These maps have different premises; neither follows merely from defining Accepted.

**C4 — Recurring safety and service.** Starting at any \(x_0\in S\), current measurements construct covering envelopes, C2 constructs overlapping endorsements, and C3 supplies a permitted transition preserving \(S\). New measurements repeat the construction. Integer commands and bypass values preserve the grid. Thus the next epoch has the same enabled interface. There is an infinite execution for every admitted causal adversary: correct readings always exist, messages arrive by the stipulated boundaries, a certificate exists, the least certificate is selected, and the next state is defined. Every such execution is safe and delivers one unit per epoch. The declaration loop_invariant proves safety for every recurrence; the preceding construction, rather than induction alone, discharges nonblocking and service.

The trust argument terminates at explicit premises: the gate and service port function as modeled; sensing and channels satisfy their bounds; authentication preserves attribution; hostile flow respects its cap. Replacing a premise with a monitor would require detection-before-harm and a safe response. No such replacement is silently claimed.

## Information-dependent winning and coordination

An exact continuation problem retains execution-prefix alternatives \((x,B,\rho)\), each actor's local-history equivalence, the plant transition, and the outstanding service obligation. A winning witness is one compatible family of local policies chosen before \(B\), not one controller selected separately for each fault set. General constructions already exist; [SOURCES.md](SOURCES.md) records the relevant imports and finiteness limits.

This fragment admits a smaller sufficient realization. The verification state retains the unknown fixed fault pair, safe inventory, and current phase. Authorizers retain the epoch and their own report vector until computing \(m_i\), then only their endorsement set. The gate retains the epoch, distinct shares, and whether it has executed. It need not know \(B\), \(x\), or which correct authorizers supplied the common witness.

The winning invariant is the family of all epoch-start records with \(x\in S\) and \(B\) admitted, under the fixed phase protocol. C1–C4 prove closure and local implementability. The checker maintains 16 fault fibers and never changes the faulty pair across an edge. Evidence is regenerated from current measurements, so past readings are unnecessary for this safety-and-service claim. They would matter for accountability, delayed control, or richer knowledge queries; the compression is not asserted adequate for those uses.

This is a task-specific sufficient information representation, not a complete synthesis algorithm for arbitrary histories. The distributed certificate has two parts: each local envelope licenses actions, and the actual delivery pattern licenses a gate selection. A pooled set of states would not explain who can issue the necessary messages. A centrally winning plant region would not prove local endorsement overlap.

**C5 — Singleton endorsement obstruction.** Hold the plant, information channel, thresholds, and objective fixed. Restrict each correct authorizer to endorsing exactly one locally certified action as a deterministic function of its median. Even two different selectors cannot guarantee matching endorsements over all admitted states and selective faulty reports.

For any \(x\), correct sensors can report \(x-1,x+1\). The faulty sensor can then realize any median in \(\{x-1,x,x+1\}\) independently at each recipient. For selectors \(f,g\), agreement in these scenarios forces

\[
f(1)=g(3)=f(5)=g(7)=f(9),
\]

using true states \(2,4,6,8\). Yet the envelope at median 1 permits only action 2, while the envelope at median 9 permits only action 0. Contradiction. The declaration no_singleton_median_selectors checks this chain, allowing \(f\ne g\). The checker also exhausts 12 locally valid tables per authorizer and rejects all \(12^3=1{,}728\) three-authorizer profiles.

When the faulty authorizer withholds, different honest single endorsements yield no certificate and violate service. This first-epoch obstruction includes preassigned actor-specific selectors. It does not rule out richer observations, additional rounds, inter-authorizer communication, or randomization. Arbitrary memory has no additional evidence at an identically initialized first epoch, but this statement does not address protocols with an informative setup history.

The permissive policy avoids the obstruction without reconstructing exact state. At \(x=5\), correct readings 4 and 6 and selective faulty reports yield medians 4 and 6. The sets \(\{1,2\}\) and \(\{0,1\}\) share action 1. Signing the whole sets supplies its certificate; selecting minima yields 1 and 0 and stalls.

Full-state/known-fault control, pooled-information control, and the distributed permissive policy all preserve the whole safe region \(S\). This winning-region comparison is exact because states outside \(S\) violate safety at time zero. It does not equate their information: reports all equal to 5 are compatible with states 4, 5, and 6 and different faulty identities behaving honestly. Safe decision succeeds without exact reconstruction or attribution.

Without informative sensing, identical initial local histories can occur at states 2 and 8. Robust one-step safety requires respectively \(u\ge2\) and \(u\le0\). The declaration incompatible_endpoints formalizes the obstruction. Its source interpretation fixes identical gate messages and no additional sensor; a central full-information controller does not refute it.

## Structural quorum generalization

The relevant families are determined by the judgment being protected. They share an underlying fault model but are not three renamed vote counts.

For nonempty fault family \(\mathfrak F\) on \(I\), an accepted support family \(\mathcal A\) has hit safety when every \(A\in\mathcal A\) contains an identity outside every admitted \(B\). Availability requires, for each \(B\), some \(A\in\mathcal A\) disjoint from \(B\). Such a family exists exactly when no union of two admitted fault sets covers \(I\), denoted \(Q^2\).

Necessity: take a live support outside \(B_1\). If \(B_1\cup B_2=I\), that support lies inside \(B_2\), violating hit safety. Sufficiency: choose complements \(I\setminus B\). The declaration gate_family_iff_Q2 checks both directions for predicate-valued families. Its statement also permits empty families and infinite universes; the application's nonempty finite scenario and implementable collection requirements are separate.

For conflicting-certificate exclusion, require every pair of supports to intersect outside every \(B\), as well as availability. Existence is equivalent to \(Q^3\): no three admitted fault sets cover \(I\). Availability supplies supports outside \(B_1,B_2\); a three-set cover would put their intersection inside \(B_3\). Conversely, complement supports work under \(Q^3\). The declaration conflict_family_iff_Q3 checks this reconstruction of established quorum geometry.

With \(n\) identities and all fault sets of size at most \(f\), threshold supports require \(f<q\le n-f\) for hit safety and availability, hence \(n>2f\). Pairwise honest intersection requires \(2q>n+f\) and \(q\le n-f\), hence \(n>3f\). The latter yields exclusion only with a correct-signer rule forbidding the relevant conflicting endorsements. Physical authorizers intentionally sign multiple alternatives; Q3 alone would not make their certificates exclusive.

Apply each condition to the appropriate role projection of the joint coalition. Sensor identities do not count as authorizer shares. In this benchmark, two honest reports bound the median, two endorsements ensure an honest safety checker, and an interval of feasible effects supplies physical capacity. These are respectively an order-statistic inference, an access structure, and a dynamics inequality. Their composition needs C2 and the single-effect gate; none follows from the other two.

For three authorizers with one fault, Q2 holds and Q3 fails. Physical service succeeds because the certificates are alternative permissions and the gate applies only one. An ordinary conflicting-certificate result is recovered by adding exclusive decisions and a non-equivocation signing discipline, where the Q3 theorem applies. This property-indexed comparison does not relax every Byzantine agreement threshold.

## Digital BFT baseline and the preserved boundary

The digital instance has three identities, one fixed leader, binary values, at most one static Byzantine identity, ideal signatures, and two synchronous rounds. Correct messages and processing finish within their rounds. Signatures bind epoch, value, and nested signer chain.

In round 1 the leader signs and sends its input. Each correct follower accumulates all valid leader-signed values received in that round. In round 2 each correct follower signs and forwards every accumulated value to the other follower. A follower accepts an echo only with the leader's signature and a distinct follower's signature for the same epoch and value. Late raw leader proposals are rejected. After round 2, correct followers choose the sole accumulated value if the set is singleton, otherwise default 0. A correct leader outputs its input.

**D1 — Agreement, validity, termination.** If the leader is correct, unforgeability allows only its input to have a valid leader signature; correct followers already receive it in round 1. If the leader is faulty, both followers are correct, so both final sets equal the union of their first-round sets. Decisions agree, and all correct actors decide at the second boundary. The default counts as a completed digital decision; external validity is not inferred.

This is a bounded reconstruction of signed broadcast, with the direct proof above and exhaustive finite execution classes in the checker. It is not an implementation of every SM(m) variant, nor a general consensus theorem inferred from the physical threshold. Repeating fixed slots with fresh epoch tags, unchanged faults, and the same round assumptions gives a binary append-only sequence: induction preserves equal correct prefixes at completed-slot boundaries and correct-leader validity per slot. Between boundaries, committed prefixes remain comparable. This repeated-log interpretation is hand-derived from D1, not separately mechanized.

Preserved queries are correct decision agreement, correct-leader input validity, and one decision per two rounds. The kernel omits arbitrary transactions, membership changes, asynchronous progress, lock/view-change behavior, external validity, and state-machine execution correctness. Full Basic HotStuff remains an exact encoding obligation.

All correct replicas can agree on the bit interpreted as “inject 2” while inventory is 8. If an unprotected interface executes that command with \(b=1\), the successor is 10. Agreement has not established safe effect. The positive extension supplies the missing evidence, effect certificate, and enforcement premises.

## Epistemic and refinement bridges

The epistemic bridge concerns delivery, not the entire strategy space. It uses D1's ideal signature interpretation: a valid signature certifies a historical signing event; its payload need not report physical truth.

**E1 — Enriched event/history correspondence.** Initial worlds record physical truth \(p\), historical signing fact \(h\), and certificate existence \(c\), with \(c\Rightarrow h\) supplied by signature soundness. Neither recipient initially knows which world obtains. Events are skip, or delivery to A enabled by \(c\). Delivery changes A's possession atom. A distinguishes receipt from skip; B sees only a tick. Histories retain these symbols.

The direct execution model appends enabled events. The enriched epistemic product keeps the same enabled world/event pairs, intersects old accessibility with equality of event observations, and updates possession by a postcondition. Flattening product worlds into histories is bijective, preserves atoms, and satisfies

\[
\rho e\sim_i\rho'e'\ \Longleftrightarrow\
\rho\sim_i\rho'\ \land\ o_i(e)=o_i(e').
\]

Structural induction therefore preserves every Boolean/nested-knowledge query over the tracked atoms. The checker verifies valuations, enabled-world correspondence, and every accessibility pair after three updates: 8, 12, and 20 worlds. The displayed factorization gives arbitrary finite iteration for this fixed synchronous append-history construction; the executable coverage is the stated three stages.

After receipt, A knows possession, existence, and the supplied historical fact, but need not know \(p\). B need not know A's possession or certificate existence. This inference uses \(c\Rightarrow h\), not arbitrary payload syntax. Certificate assembly, actual locks, and HotStuff's historical-lock invariant remain unencoded. E1 is a signature-delivery fragment sharing D1's artifact meaning, not a proof that the whole broadcast protocol is a DEL model.

**E2 — Failed announcement encoding.** A compromised signer can send the same authenticated “safe” claim in safe and unsafe worlds. Receipt preserves both alternatives. Truthful public announcement instead deletes the unsafe world; it creates false knowledge in a safe actual world and cannot represent the allowed receipt in an unsafe actual world. A separate 32-world two-stage delivery model checks this and selective delivery.

These bridges have different preservation laws. E1 preserves epistemic queries by a graph isomorphism; it supplies no strategic or timed theorem. C1–C4 transport a concrete local policy to a plant invariant through coverage, support soundness, and realized effects. Each local action map is executable from that actor's history. No hidden-state-dependent action lift is used. Epistemic bisimulation is not assumed to preserve distributed winning strategies.

E1 drops untracked payloads, queues, certificate creation, actuator state, and future choice powers. A query consuming them reopens the encoding. Pure DEL without postconditions cannot update possession atoms; the enrichment is established prior art. A knowledge-of-preconditions import also requires action locality in the same interpreted system. That can fail when alternatives include the acting identity's Byzantine behavior or scheduler-controlled physical execution. Correct-code determinism does not automatically make every physical action locally known.

## Institutional interpretation and effective capability

The minimal normative system is stipulated, not a claim about any jurisdiction. It permits the gate to apply one current-epoch control with two eligible endorsements and obliges it to deliver the epoch's service when the protocol supplies such a control. The bearer is the gate operator/interface; the beneficiary is the modeled service recipient; the trigger is the epoch; the deadline is its realization phase. Outside the stated fault, delivery, and plant premises, joint satisfiability is not claimed.

Separate normative permission, credential verification, and physical effect. An unauthorized raw injection can occur through an unprotected path. Accepted compromised credentials can separate credential acceptance from the facts their owner should have checked. Conversely, a permitted signed action can fail to occur if the actuator is disconnected. The checker records a stipulated unauthorized-but-realized countermodel. It demonstrates logical independence, not a legal conclusion.

The gate couples the rule to effect within its trust boundary. An epoch-bound artifact with two distinct shares publicly witnesses endorsement events and, under C1–C3, robust permission for that epoch's state. Soundness uses an honest endorser; non-vacuity uses the common action and actual transmissions. Evidence is generated operationally rather than defined as “whatever proves safety.”

The artifact does not identify a faulty actor, establish negligence, or prove that service occurred. An authenticated disagreement can result from honest noise. Attribution, appeal, repair authority, and cross-institution recognition are separate consumers. Credential revocation changes the signature path; it does not remove physical bypass capability without an actual isolation mechanism.

## Failure witnesses and assumption replacement

These are changed contexts, not attacks secretly included in the positive theorem.

| Altered assumption | Witness and supported conclusion | Replacement or exact residual |
|---|---|---|
| Each authorizer endorses one action | C5 rejects every locally certified median-only singleton selector pair. | The all-safe-actions policy restores service with the same plant and sensing. Additional communication is unstudied. |
| Correct capacity falls to 1 | At \(x=2,b=-1\), every \(u\le1\) gives \(x'\le1\). Persistent removal drains any finite inventory. | Increase capacity, restrict removal, or weaken service; sensing alone cannot repair it. |
| Bypass removal reaches 2 | \(x=2,b=-2,u\le2\) gives \(x'\le1\). | A physical restriction or larger corrective interface is needed. The Lean result excess_removal checks this bounded witness. |
| A correct sensor is defaulted early | At \(x=8\), reports \(7,0,2\) yield median 2 and certified action 2; \(b=1\) reaches 10. | Retain timely collection or prove a new evidence contract. This affects safety. |
| Error grows to 2 | Correctly widened envelopes at medians 3 and 7, with \(x=5\), allow only 2 and 0 respectively. | This scheme loses guaranteed service; richer exchange or controls might restore it. No universal impossibility follows. |
| Multiple effects occur | At \(x=6,m=5\), both 1 and 2 are individually certified; their sum gives \(6+1+2-1+1=9\). Replaying 2 twice at \(x=5,m=4\) also reaches 9. | Exactly-one enforcement or a cumulative-effect certificate is needed. |
| Evidence is stale | Reusing \(m=4,u=2\) with \(b=1\) gives \(5\to7\to9\). | Retain age and pending commands, and prove a predictive envelope. General delayed control is not disproved. |
| State, readings, and envelopes become real; controls stay integer | At \(x=4.5\), medians 3.5 and 5.5 have safe integer controls \(\{2\}\) and \(\{0,1\}\). Fractional bypass can reach this state. | Continuous commands, wider margins, or another abstraction may work; direct transfer fails. |
| Shutdown substitutes for service | Zero injection from 2 reaches 1 even with \(b=0\); suppressing delivery violates the floor. | A changed mission must explicitly authorize degradation. |

Two faulty sensors can corrupt coverage; two faulty authorizers can certify an unsafe action without an honest signer. These are separate executable witnesses. The role bounds and bypass cap do not imply tolerance of arbitrary two-identity coalitions on the six-actor universe.

## Claim ledger and resumption

The ledger records support, not institutional acceptance.

| ID | Statement and context | Status, support, and residual |
|---|---|---|
| C1 | Current envelope coverage under \(\theta_P\). | proved: median_bound, envelope_covers. Fresh distinct authenticated reports and timely honest delivery remain operational premises. |
| C2 | Shared analyst witness is in every honest local control set. | proved: common_certified. Integer grid is material. |
| C3 | Accepted support is safe and honest transmissions supply support. | proved: gate_safe, gate_available; derived protocol-to-support maps. Cryptographic implementation is assumed. |
| C4 | The same policy preserves all \(S\) and serves every epoch. | proved recurrence invariant; derived nonblocking/service construction; exhaustive replay. Gate and port realization remain assumed. |
| C5 | Median-only singletons cannot guarantee matching honest endorsements. | proved: no_singleton_median_selectors; exhaustive 1,728 profiles. Richer information protocols excluded. |
| Q2/Q3 | Hit/exclusion structures exist under their respective cover conditions. | proved Lean reconstruction. Q3 is established prior art; Q2 is the direct gate specialization. Neither supplies actuation. |
| D1 | Signed broadcast agreement, correct-leader validity, two-round termination. | cited[✓] comparison; derived bounded proof and repeated-slot interpretation; executable model. No full HotStuff or cryptographic verification. |
| E1/E2 | Declared epistemic correspondence and failed truthful-announcement encoding. | derived isomorphism/induction; finite exhaustive checks. Certificate soundness is supplied, strategic/time transport excluded. |
| X | Context changes defeat specified guarantees or this scheme. | proved Lean for capacity, excess removal, endpoint ambiguity; derived and exact checks for other witnesses. |

The parent [TODO](../TODO.md) contains live obligations. [COMPLETION.md](COMPLETION.md) records the completion audit. This increment supplies an integrated positive construction, a same-objective coordination impossibility, digital recovery, structural access results, and transfer failures. Those wider scopes are not claimed by this increment; their developed extensions and remaining boundaries are maintained in PROGRAM.md.

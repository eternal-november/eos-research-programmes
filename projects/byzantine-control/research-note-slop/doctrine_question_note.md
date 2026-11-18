# The Doctrine Question
## Degeneracy, divergence, and stratified assignment in distributed invariant control

**Status.** Position note, deliberately short. It addresses a question the sibling notes leave open — most explicitly `from_bft_to_generalized_state_control_research_note.md` §2, which exhibits three reconstructions of BFT-as-control and instructs: compare on examples, do not choose by taste. The claim here is that the comparison has a determinate outcome that can be stated now, with one genuinely open theorem left over. Each thesis is marked by warrant type: **[T1]** is provable by standard machinery (sketch below, discharge owed), **[T2]** is a structural claim with a named falsifier, **[T3]** is a design rule forced by named impossibility results.

**The question.** Which judgment structure should govern the generalized theory?

- **D1 — state doctrine.** Controlled invariance, viability kernels, barrier certificates, adversarial safety games. Native objects: state spaces, reachable sets, margins. [8, 9, 10]
- **D2 — trace doctrine.** Supervisory control, reactive synthesis, runtime enforcement, contract automata. Native objects: languages, automata, interface composition. [6, 7, 11]
- **D3 — epistemic doctrine.** Knowledge conditions for irreversible commitment, certificates, belief envelopes \(B_t\), agreement-on-disagreement. Native objects: information states, indistinguishability relations. [2, 3]

"Govern" means: the doctrine fixes what counts as state, specification, proof obligation, and composition method for the field. The corpus refuses the election. This note claims the refusal, sharpened, *is* the answer: the trilemma is degenerate where BFT historically lived, comes apart lawfully as the controlled object generalizes, and resolves into per-obligation assignment rather than global election.

**Declared kernel.** A fourth possibility — that none of the three governs and a new doctrine is required (a rational/mechanism-design doctrine for strategic-but-not-arbitrary actors; an institutional doctrine for authority-heavy state) — is held in reserve, not refuted. The corpus's Byzantine framing keeps it out of scope here; it becomes live the moment fault budgets are replaced by incentive models.

---

## 1. [T1] Degeneracy: on protocol-constituted state the three doctrines are interdefinable

**Claim.** For the base BFT object, the three renderings preserve exactly the same task-relevant distinctions, so the election is empty. This is why classical BFT never had to ask the doctrine question.

**Toy.** Replicated register, \(n\) replicas, at most \(f\) Byzantine, quorum commit. Safety: no two correct replicas commit conflicting values at the same position.

*D1 rendering.* Augment the state with histories and certificates (required: instantaneous local states legitimately diverge view-locally, so the invariant lives on the augmented state — the standard monitor-product move). Let \(K_\Delta\) be the set of augmented global states whose correct-replica committed prefixes are pairwise compatible. The protocol is a distributed policy rendering \(K_\Delta\) invariant under arbitrary actions of the faulty set.

*D2 rendering.* \(\operatorname{Trace}(P, W_f) \subseteq L_{safe}\), where \(L_{safe}\) is the prefix-closed language of executions containing no conflicting commits.

*D3 rendering.* Commit-on-certificate as a knowledge condition: replica \(i\) commits \(v\) at position \(k\) only on evidence such that, in the interpreted-systems semantics over the run set [3], no correct replica can ever hold a conflicting valid certificate. Quorum intersection is precisely the mechanism that makes certificate-level knowledge sound — an *attainable surrogate* for the common knowledge that is provably unattainable under unreliable communication [2].

*Translations.* D1→D2 by the trace semantics of the transition system. D2→D3 by interpreted-systems knowledge over the trace set (knowledge = truth in all runs consistent with local history). D3→D1 by making certificates state components, so the knowledge condition becomes a state predicate on evidence. Each translation preserves the safety property's extension.

**Status:** sketch. Discharging it on the register is standard machinery and is this note's first work item.

**Why degeneracy holds.** Commitment *constitutes* the controlled state. The truth-maker of "\(v\) is committed" is itself a protocol event — simultaneously a state transition (D1), a trace event (D2), and an epistemic act (D3). Ontic, behavioral, and epistemic descriptions are three coordinates of one event. There is no fact for the doctrines to disagree about.

---

## 2. [T2] Divergence: the doctrines come apart at the mediation boundary, and divergence indexes world-coupling

Once a variable becomes mediated or autonomous (the constitutive classification of the generalized-state note, §2.4), each pair of doctrines opens a definite gap. Witnesses on the pressure manifold (B-DIC note §10.1: invariant \(p \le p_{max}\), Byzantine sensor budget, remote valves, delays) — three facts, each native to one doctrine and not statable in the others without importing that doctrine's structure:

**Fact A (native D1).** "From belief set \(B_t\), the plant may already lie outside the delay-robust viability kernel: no admissible \(u\) gives \(\operatorname{Post}(B_t,u,W) \subseteq K\)." A quantitative, geometric fact about reachable sets and margins. Untimed language inclusion erases the margin; epistemic logic states the uncertainty but not the dynamics. (Timed automata recover part of it — precisely by importing state-doctrine structure into D2, which supports the thesis rather than undermining it.)

**Fact B (native D3).** "A corrupt sensor coalition can make the fast-pressure-rise history and the sensor-drift history identical for every correct controller past the last safe intervention time, while the two states' safe-action sets are disjoint." A fact about the belief map, quantifying across runs that share local views — hyperproperty-shaped in the sense of [5], hence not an ordinary trace property; and not statable in D1 at all, where "cannot distinguish" has no referent.

**Fact C (native D2).** "Estimator ∥ BFT service ∥ valve supervisor enforces \(L_{safe}\) provided each component satisfies its contract automaton, independent of internal representations." Interface algebra. D1 composition demands shared state geometry across heterogeneous components; D3 knowledge conditions compose notoriously badly. Characterizations of what a monitor or supervisor can enforce are language-theoretic [6, 7].

**Divergence law.** The corpus's lift-failure taxonomy sorts into the gaps: observability and inference failures live in the D1/D3 gap; timing and viability failures in the D1/D2 gap; coordination and authorization-versus-enforcement failures in the D2/D3 gap. The *amount* of doctrinal divergence a system exhibits measures its distance from protocol-constituted state. Degeneracy at ladder level \(L_0\); growth with world-coupling thereafter.

**Falsifier.** An expressiveness-and-provability audit along the benchmark ladder (\(L_0\)–\(L_7\)): at each level, record which of the level's obstruction facts each doctrine can state and prove without importing another's structure. [T2] predicts full interdefinability at \(L_0\) and monotone divergence above it. A mediated system at \(L_3\) or higher where the three doctrines remain fully interdefinable *without* structure-import refutes the thesis. This audit is the second work item.

---

## 3. [T3] Assignment: stratify, do not elect

The strata are forced apart by cost and decidability, not taste:

1. The theory cannot live wholesale in D1: distributed synthesis under partial information is undecidable for general architectures [4]. Scale forces retreat to compositional interfaces — D2's home ground.
2. Coordination limits are natively epistemic: common knowledge is unattainable with unreliable communication [2]; quorum certification is the attainable surrogate. Commitment lives in D3.
3. Actuation and timing limits are natively viability-theoretic: kernels, margins, barrier conditions [8, 9]. They live in D1.
4. Enforceable-property characterizations live in D2 [6, 7].

Each candidate doctrine is the unique native home of one obstruction family. Hence the rule:

> **Assign each proof obligation to the coarsest stratum whose equivalence preserves the distinctions that obligation's consumers need; owe an explicit translation whenever a claim crosses strata.**

| Obligation | Native stratum | Translation owed |
|---|---|---|
| Unmediated-escape impossibility | D1 | belief-set version for D3 consumers |
| Indistinguishability impossibility | D3 | its D1 shadow: the effective kernel shrinks to a belief-space kernel |
| Estimator soundness (\(x_t \in B_t\)) | D3 | contract form for D2 composition |
| Contract composition, monitors, shields | D2 | joint satisfiability of fault assumptions checked in the D1 model |
| Reaction-margin theorems | D1 | freshness/latency budgets as D2 contract clauses |
| Minimal coordination | D3→D1 cross | the theorem *is* the translation |
| Adversarial separation | all three | the theorem is whether the translations commute |

The unified carrier is a three-sorted model: an adversarial, partially observed game (D1 sort) whose information objects are certificate-valued (D3 sort) and whose component boundaries are contract automata (D2 sort). The corpus's proposed first formalism — "a finite-state partially observed safety game" — should be read as the D1 carrier of this model, not as the elected doctrine.

Doctrine becomes a function of the obligation, \(\mathrm{doctrine}(o)\), not a property of the field.

---

## 4. What remains open, and what would kill this note

The reframe's payoff is that the corpus's two flagship questions become posable as cross-stratum theorems. Neither is answerable from an armchair.

**Minimal coordination (D3→D1).** Characterize the weakest D3 object — received reports, admissible evidence set, compatible local envelopes, joint envelope, or action certificate only — whose D1 shadow suffices for invariance. Conjecture, consistent with the corpus: generalized control sometimes needs *less* consensus than state-machine replication, because the D1 consumer needs only a nonempty intersection of shadowed safe-action sets, not point agreement.

**Adversarial separation (all strata).** When can the estimator (D3), the coordination interface (D2), and the controller (D1) be synthesized separately and composed? **Reviser for this entire note:** if adversarial coupling of the strata is *generic* — if the translations essentially never commute in the presence of a live adversary — then stratified assignment fails as an organizing principle and the field needs a genuinely joint doctrine. That negative result would be more valuable than this note.

**Postscript (added later).** The D3 sort now has a candidate formalization program in this folder: `bft_public_warrant_problem.tex` poses acceptance of BFT finality as an evidence-indexed doctrine of *institutional warrant* (public artifacts, not agent knowledge) — see `public_warrant_review_and_extension.md` for review, a solved fragment, and the connection: its safety-only scope succeeds precisely because finality claims are protocol-constituted, and its monotone-warrant semantics is predicted to fail at the mediation boundary, where warrant becomes defeasible. That failure line is [T2]'s D1/D3 gap seen from inside D3.

**Work items, in dependency order.**

1. Discharge the [T1] degeneracy sketch on the replicated register (three renderings, translations exhibited, extensions checked).
2. Run the [T2] expressiveness audit along the benchmark ladder; tabulate divergence per level.
3. Attempt the minimal-coordination theorem in the finite-state case.
4. Attempt adversarial separation, or construct the minimal coupling counterexample.

---

## References

[1] L. Lamport, R. Shostak, M. Pease. "The Byzantine Generals Problem." *ACM TOPLAS* 4(3), 1982.

[2] J. Y. Halpern, Y. Moses. "Knowledge and Common Knowledge in a Distributed Environment." *Journal of the ACM* 37(3), 1990, 549–587.

[3] R. Fagin, J. Y. Halpern, Y. Moses, M. Y. Vardi. *Reasoning About Knowledge.* MIT Press, 1995.

[4] A. Pnueli, R. Rosner. "Distributed Reactive Systems Are Hard to Synthesize." *FOCS*, 1990, 746–757.

[5] M. R. Clarkson, F. B. Schneider. "Hyperproperties." *Journal of Computer Security* 18(6), 2010, 1157–1210.

[6] P. J. Ramadge, W. M. Wonham. "Supervisory Control of a Class of Discrete Event Processes." *SIAM Journal on Control and Optimization* 25(1), 1987, 206–230.

[7] F. B. Schneider. "Enforceable Security Policies." *ACM Transactions on Information and System Security* 3(1), 2000, 30–50.

[8] J.-P. Aubin. *Viability Theory.* Birkhäuser, 1991.

[9] A. D. Ames, X. Xu, J. W. Grizzle, P. Tabuada. "Control Barrier Function Based Quadratic Programs for Safety Critical Systems." *IEEE Transactions on Automatic Control* 62(8), 2017, 3861–3876.

[10] L. Lamport. "The Temporal Logic of Actions." *ACM TOPLAS* 16(3), 1994.

[11] N. Lynch. *Distributed Algorithms.* Morgan Kaufmann, 1996.

[12] M. Castro, B. Liskov. "Practical Byzantine Fault Tolerance." *OSDI*, 1999.

**Verification note.** [4] spot-checked against the published record (FOCS 1990, pp. 746–757); [2], [5], [6], [7], [9] cited from settled literature and consistent with the sibling notes' bibliographies; page numbers for [2], [5], [6], [7] are from memory and should be confirmed before external circulation.

# The Public-Warrant Problem: Review, Solved Fragment, and Placement
**Re:** `bft_public_warrant_problem.tex` · **Status:** review and extension note. Findings are typed: **[E]** error (checkable, with fix), **[V]** vacuous-as-stated clause, **[T]** hidden tension, **[C]** connection thesis, **[U]** upgrade. The solved fragment in §4 is a proof sketch whose promotion to a full proof is the first work item.

## 1. Verdict

The problem statement is better than its author's estimate. It is not at `bft-research-note-long-1` quality; on discipline-per-word it is the strongest document in the folder — scoped, typed, guarded against its own failure modes (the §5 anti-relabeling clause), and equipped with a falsifiable success criterion. It is a different genre from the sibling notes: a *problem statement* rather than a program, and it should be judged as one. As a problem statement it is well-posed after four repairs, and its central design decision — warrant grounded in publicly checkable artifacts rather than agent knowledge — is the right one for this corpus (see §6).

## 2. Obstructions

**O1 [E] Variance inconsistency.** The note posits \(P : \mathsf{Ev}^{op} \to \mathbf{Pos}\), but P1 demands reindexing \(P(s) \to P(t)\) for \(s \preceq t\). A contravariant functor sends the arrow \(s \to t\) to \(P(t) \to P(s)\). The intended maps are the hint's restrictions \(\mathcal P(\uparrow\!s) \to \mathcal P(\uparrow\!t)\), \(U \mapsto U \cap \uparrow\!t\), which are covariant in \(\preceq\). Fix: declare \(P : \mathsf{Ev} \to \mathbf{Pos}\) (Kripke-style monotone predicates), or equivalently keep the hyperdoctrine convention by taking the base to be \(\mathsf{Ev}^{op}\) with the order reversed. Cosmetic in intent, load-bearing for anyone who instantiates.

**O2 [T→E] The vacuity trap, made mechanical.** §5 warns against "relabeling a protocol invariant" but does not name the mechanism. It is this: if admissibility of \(\mathsf{Ev}\) is *defined* by the safety property (states in which no conflicting witnesses coexist), then P3 and the soundness theorem hold by definition and the doctrine says nothing. The repair fixes where protocol content may enter: define \(\mathsf{Ev}\) **generatively** — evidence states are exactly those producible by runs in which validators outside the adversary structure follow the protocol's signing discipline and corrupted validators emit arbitrary *authenticated* artifacts. Conflict exclusion then becomes a theorem about generatively-admissible states (quorum intersection plus the honest signing discipline), not an axiom. Where \(\mathsf{Ev}\)'s constraints come from is *the* design decision of the whole problem; the note should say so explicitly.

**O3 [V] The "stronger result" collapses.** §7 offers extensional coincidence of witnessing and acceptance as the stronger target. But Hint 3 defines \(\mathsf{Acc}_c^s := W_c^s \cap \bigcap_d \Box_s(\uparrow\!s \setminus W_d^s)\), so \(\mathsf{Acc} \subseteq \mathsf{Wit}\) holds by construction and coincidence is *equivalent* to soundness — the stronger clause is empty for the hinted candidate. Repair: replace coincidence with a **characterization theorem**: axiomatize acceptance by the desiderata (grounded in \(\mathsf{Wit}\), persistent, conflict-stable) and prove the hinted operator is the largest — or unique — operator satisfying them. A universal property is also the more genuinely doctrinal result.

**O4 [T] Monotonicity versus reconfiguration.** Desideratum 3 (warrant persists under evidence extension) is false across epoch boundaries under validator reconfiguration: to a fresh verifier, a certificate signed by a superseded validator set warrants nothing without a checkpoint or freshness assumption — this is the long-range-attack / weak-subjectivity phenomenon. The note's own D6 instinct (reconfiguration as indexed base change) is right, but it must be flagged as *modifying* Desideratum 3 — monotonicity holds fiberwise per epoch and is only conditionally transported along epoch morphisms — not as an optional extra stacked on top of it.

## 3. Where the difficulty actually lives

The note's stratification distributes the difficulty misleadingly. Layers I and III are off-the-shelf: upward-closed sets on \(\uparrow\!s\) are the opens of an Alexandrov topology, \(\Box_s\) is its interior operator, the fibers \(\mathcal P(\uparrow\!s)\) are frames (which the nucleus hint needs — **[E-minor]** \(\mathbf{Pos}\) should be frames if Hint 4 is pursued), and the whole future-cone semantics is standard S4/intuitionistic Kripke machinery. The soundness theorem is two lines given the right lemmas: if \(t\) witnesses \(c\) and some \(u \succeq t\) witnessed a conflicting \(d\), witness persistence puts both witnesses in \(u\), contradicting conflict exclusion at \(u\).

So the entire content of the problem concentrates in four places: the generative definition of \(\mathsf{Ev}\) (O2); the per-protocol conflict-exclusion lemma; P6, which for real protocols means re-expressing the locking discipline (Tendermint, HotStuff) as the mechanism behind "no honest participant contributes to conflicting witnesses across rounds"; and reconfiguration base change (O4). The categorical superstructure will not produce new safety proofs — protocol safety proofs already exist, some machine-checked. Its value must therefore be as an *interface* (§5), and the note should claim that value explicitly rather than implying the theorem is the prize.

## 4. Solved fragment: single-shot quorum finality

To show the problem is well-posed, here is the degenerate but complete case.

**Instance.** Validators \(V\), weights \(w\) summing to 1, adversary structure = corrupted weight \(< 1/3\). Claims = values; \(\mathsf{Conf}(c,d)\) iff \(c \neq d\). Honest discipline: sign at most one value. \(\mathsf{Wit}(s,c)\): \(s\) contains valid signatures on \(c\) from distinct validators of total weight \(\ge 2/3\). \(\mathsf{Ev}\): generatively, all authenticated-artifact sets producible under the discipline and budget above; \(\preceq\) is superset extension.

**Lemma (conflict exclusion).** No admissible \(s\) witnesses both \(c\) and \(d \neq c\). *Proof:* two certificate sets of weight \(\ge 2/3\) overlap in weight \(\ge 1/3\); corrupted weight is \(< 1/3\); so the overlap contains an honest validator, who then signed two values — contradicting the discipline that generates \(\mathsf{Ev}\). ∎

**Persistence.** Immediate: artifacts are never removed under \(\preceq\).

**Soundness \(W_c^s \subseteq \mathsf{Acc}_c^s\).** By the two-line argument of §3. With Hint 3's definition, \(\mathsf{Acc} = \mathsf{Wit}\) extensionally on admissible states. ∎ (sketch)

This discharges P1–P5 for the toy and exposes P6's true form: in multi-round protocols, "honest signs at most one conflicting claim" is not a per-validator invariant but an emergent property of locking across views — so P6 reduces to recasting each protocol's existing safety argument as the conflict-exclusion lemma of the doctrine. That is real work, but it is *translation* work, of exactly the cross-stratum kind the doctrine note's assignment table predicts.

## 5. The missing consumer

The note lacks a "so what," and there is a concrete one. The acceptance operator \(\mathsf{Acc}\) is precisely what a **light client** computes: verifying \(\mathsf{Wit}\) from authenticated artifacts without executing the protocol or trusting any replica. Cross-chain verification (IBC-style relaying, bridges) is warrant *transport between institutions*, and the major bridge failures were exactly acceptance-without-valid-witness events. So a solved doctrine is a specification for external verifiers, and the reindexing/base-change structure is the mathematics of warrant portability — across evidence growth (P1), epochs (O4/D6), and chains. This upgrades "institution-sensitive" from flavor to a load-bearing claim with a control surface: what a verifier must check, stated once, protocol-indexed.

## 6. Placement in the corpus

**[C1] This is the D3-stratum program.** Under the stratified assignment of `doctrine_question_note.md`, the warrant problem is a candidate formalization of the epistemic sort: it makes "certificate-level knowledge" precise *institutionally* — warrant grounded in public artifacts — rather than agent-epistemically (interpreted-systems knowledge). That choice is correct for this corpus: the \(B_t\)/certificate objects of the sibling notes are institutional facts, not psychological states. The nearest logical lineage, missing from the note's references, is justification logic (evidence-carrying modalities, "\(t : \varphi\)") [A]; the note's future-cone semantics is roughly a poor-man's justification logic over an Alexandrov frame, and saying so would sharpen both the novelty claim and the kill-search. The kill-search should target: justification logic applied to consensus, machine-checked BFT safety formalizations (e.g., Velisarios [B]) for the lemma layer, and any categorical treatments of protocol evidence.

**[C2] The monotone/defeasible boundary is the constituted/mediated boundary.** The note's scope discipline works for a reason it does not state: finality claims are *protocol-constituted* (in the sense of `from_bft_to_generalized_state_control_research_note.md` §2.4). Witnessing constitutes settlement, so warrant is monotone — a certificate cannot be un-signed — and a safety-only, persistence-based semantics can exist. The moment \(\mathsf{Claim}\) includes world-coupled claims ("the valve is closed," "the collateral exists"), \(\mathsf{Wit}\) no longer constitutes truth, later evidence can *defeat* earlier warrant, monotone reindexing fails, and the doctrine must change logic — defeasible or graded rather than persistent. Note that the one place monotonicity already cracks *inside* pure BFT is reconfiguration (O4), which is exactly the point where constitution weakens (the institution replacing its own foundation). Prediction: the lift of this note — **defeasible public warrant for mediated claims** — is the epistemic face of the corpus's lifting problem, and deserves its own problem statement as the natural sequel.

## 7. Upgrades

**[U1] Double-index over adversary structures.** Make the adversary a genuine index: \(P : \mathsf{Ev} \times \mathcal A^{op} \to \mathbf{Pos}\), acceptance antitone in adversary strength. Desideratum 5 then becomes literal reindexing rather than metatheory, and graded warrant falls out: "final against \(< 1/3\)," "accountably final against \(< 2/3\)" — recovering economic finality [C] and accountable safety / forensics [D] as fibers of one doctrine rather than bolted-on extensions.

**[U2] Characterization over coincidence** (per O3): prove the hinted \(\mathsf{Acc}\) is terminal among operators satisfying the desiderata.

**[U3] Frames, not \(\mathbf{Pos}\)**, if the nucleus viewpoint is pursued (per §3).

## 8. Work items, in order

1. Apply O1's variance fix and O2's generative \(\mathsf{Ev}\) definition to the .tex.
2. Promote §4 to a full proof (single-shot case) — half a day.
3. Recast Tendermint's locking argument as the conflict-exclusion lemma (first real P6 instance).
4. Add the epoch-indexed base change with an explicit checkpoint side condition (O4).
5. Run the kill-search (justification logic × consensus; verified-BFT formalizations; categorical protocol semantics).
6. Draft the sequel problem statement: defeasible public warrant for mediated claims (C2).

## References

[A] S. Artemov, M. Fitting. *Justification Logic: Reasoning with Reasons.* Cambridge University Press, 2019.

[B] V. Rahli, I. Vukotic, M. Völp, P. Esteves-Veríssimo. "Velisarios: Byzantine Fault-Tolerant Protocols Powered by Coq." *ESOP*, 2018.

[C] V. Buterin, V. Griffith. "Casper the Friendly Finality Gadget." arXiv:1710.09437, 2017.

[D] P. Sheng, G. Wang, K. Nayak, S. Kannan, P. Viswanath. "BFT Protocol Forensics." *ACM CCS*, 2021.

[E] E. Buchman, J. Kwon, Z. Milosevic. "The Latest Gossip on BFT Consensus." arXiv:1807.04938, 2018 (for the locking discipline in item 3).

**Verification note.** O1 (variance) and O3 (definitional collapse) are checked directly against the .tex. The §4 lemma arithmetic is checked (overlap \(\ge 2/3 + 2/3 - 1 = 1/3 >\) corrupted weight). References [A]–[E] are cited from memory of settled pre-2025 literature; confirm bibliographic details before external circulation. The weak-subjectivity claim in O4 is standard community knowledge with no single canonical citation given here.

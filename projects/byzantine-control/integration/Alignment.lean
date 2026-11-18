import Structure
import Evidence
import QuorumAlignment
import Digital

namespace ByzantineAlignment
open ByzantineStructure

def Effective (executor key : I → Prop) : I → Prop :=
  fun i => executor i ∨ key i

theorem effective_intact_iff (executor key : I → Prop) (i : I) :
    ¬ Effective executor key i ↔ (¬ executor i ∧ ¬ key i) := by
  simp [Effective]

def OwnGuard (own : V → Prop) (value : V) : Prop :=
  ∀ previous, own previous → previous = value

noncomputable def guardCommand (own : V → Prop) (value : V) : Bool := by
  classical
  exact decide (OwnGuard own value)

theorem guard_command_exact (own : V → Prop) (value : V) :
    guardCommand own value = true ↔ OwnGuard own value := by
  classical
  simp [guardCommand]

def rawIssue (h : ByzantineQuorumAlignment.History I V) (i : I) (value : V) (sign : Bool) : ByzantineQuorumAlignment.History I V :=
  if sign then (i,value)::h else h

theorem actual_issue_equals_import (B : I → Prop) (h : ByzantineQuorumAlignment.History I V) (i : I) (value : V)
    (allowed : B i ∨ ∀ old, ByzantineQuorumAlignment.Seen h i old → old = value) :
    rawIssue h i value true = ByzantineQuorumAlignment.issue B h i value := by
  classical
  simp [rawIssue, ByzantineQuorumAlignment.issue, allowed]

/- Complete own-code facts are needed only when both executor and key are intact.
A key-compromised identity belongs to Effective even if its program follows code. -/
theorem guarded_actual_issue_preserves (executor key : I → Prop)
    (h : ByzantineQuorumAlignment.History I V) (i : I) (value : V) (sign : Bool) (own : V → Prop)
    (history : ByzantineQuorumAlignment.Exclusive (Effective executor key) h)
    (follows : ¬ executor i → sign = guardCommand own value)
    (coverage : ¬ executor i → ¬ key i → ∀ v, ByzantineQuorumAlignment.Seen h i v → own v) :
    ByzantineQuorumAlignment.Exclusive (Effective executor key) (rawIssue h i value sign) := by
  classical
  cases sign with
  | false => simpa [rawIssue] using history
  | true =>
    have allowed : Effective executor key i ∨ ∀ old, ByzantineQuorumAlignment.Seen h i old → old = value := by
      by_cases bad : Effective executor key i
      · exact Or.inl bad
      · have intact := (effective_intact_iff executor key i).mp bad
        have guard : OwnGuard own value :=
          (guard_command_exact own value).mp (follows intact.1).symm
        exact Or.inr (fun old seen => guard old (coverage intact.1 intact.2 old seen))
    rw [actual_issue_equals_import _ _ _ _ allowed]
    exact ByzantineQuorumAlignment.issue_preserves _ _ _ _ history

theorem unsafe_identity_event_preserves (executor key : I → Prop)
    (h : ByzantineQuorumAlignment.History I V) (i : I) (value : V)
    (history : ByzantineQuorumAlignment.Exclusive (Effective executor key) h)
    (unsafeIdentity : Effective executor key i) :
    ByzantineQuorumAlignment.Exclusive (Effective executor key) ((i,value)::h) := by
  have step := ByzantineQuorumAlignment.issue_preserves (Effective executor key) h i value history
  have allowed : Effective executor key i ∨ ∀ old, ByzantineQuorumAlignment.Seen h i old → old = value :=
    Or.inl unsafeIdentity
  rw [← actual_issue_equals_import _ _ _ _ allowed] at step
  simpa [rawIssue] using step

theorem compromised_key_event_preserves (executor key : I → Prop)
    (h : ByzantineQuorumAlignment.History I V) (i : I) (value : V)
    (history : ByzantineQuorumAlignment.Exclusive (Effective executor key) h) (badKey : key i) :
    ByzantineQuorumAlignment.Exclusive (Effective executor key) ((i,value)::h) := by
  have step := ByzantineQuorumAlignment.issue_preserves (Effective executor key) h i value history
  have allowed : Effective executor key i ∨ ∀ old, ByzantineQuorumAlignment.Seen h i old → old = value :=
    Or.inl (Or.inr badKey)
  rw [← actual_issue_equals_import _ _ _ _ allowed] at step
  simpa [rawIssue] using step

def appendKeyEvents (events : List (I × V)) (history : ByzantineQuorumAlignment.History I V) : ByzantineQuorumAlignment.History I V :=
  match events with
  | [] => history
  | event::rest => appendKeyEvents rest (event::history)

theorem adversarial_event_sequence_preserves (executor key : I → Prop)
    (events : List (I × V)) (h : ByzantineQuorumAlignment.History I V)
    (history : ByzantineQuorumAlignment.Exclusive (Effective executor key) h)
    (keys : ∀ event, event ∈ events → Effective executor key event.1) :
    ByzantineQuorumAlignment.Exclusive (Effective executor key) (appendKeyEvents events h) := by
  induction events generalizing h with
  | nil => exact history
  | cons event rest ih =>
    apply ih _ (unsafe_identity_event_preserves executor key h event.1 event.2 history
      (keys event (by simp)))
    intro e he
    exact keys e (by simp [he])

theorem aligned_receipt_exclusion
    (F supports : (I → Prop) → Prop) (executor key : I → Prop)
    (actual : F (Effective executor key))
    (intersect : ∀ Q R, supports Q → supports R →
      ByzantineControlResearch.Hits F (fun i => Q i ∧ R i))
    (issued first second : ByzantineQuorumAlignment.History I V)
    (history : ByzantineQuorumAlignment.Exclusive (Effective executor key) issued)
    (firstSound : ByzantineQuorumAlignment.ReceiptSound issued first) (secondSound : ByzantineQuorumAlignment.ReceiptSound issued second)
    (v w : V) (cv : ByzantineQuorumAlignment.Certificate supports first v) (cw : ByzantineQuorumAlignment.Certificate supports second w) :
    v = w :=
  ByzantineQuorumAlignment.received_certificate_exclusion F supports (Effective executor key) actual intersect
    issued first second history firstSound secondSound v w cv cw

/- An evidence row includes permission, nonblocking and every admitted actual
effect. The same component-fault predicate B occurs in all three consumers. -/
def EffectLegal (allowed : X → (S → Prop) → A → Prop)
    (next : X → (S → Prop) → A → X → Prop) (Q : X → (S → Prop) → Prop)
    (x : X) (B : S → Prop) (a : A) : Prop :=
  allowed x B a ∧ (∃ y, next x B a y) ∧ ∀ y, next x B a y → Q y B

theorem source_hypothesis_row_sound
    (F : (S → Prop) → Prop) (constraint : S → X → Prop)
    (allowed : X → (S → Prop) → A → Prop)
    (next : X → (S → Prop) → A → X → Prop) (Q : X → (S → Prop) → Prop)
    (x : X) (B : S → Prop) (a : A)
    (admitted : F B) (sound : ∀ s, ¬ B s → constraint s x)
    (row : ByzantineEvidence.Robust (ByzantineEvidence.Hypothesis F constraint) (EffectLegal allowed next Q) a) :
    EffectLegal allowed next Q x B a :=
  ByzantineEvidence.robust_decision_sound (ByzantineEvidence.Hypothesis F constraint) (EffectLegal allowed next Q) x B a
    (ByzantineEvidence.actual_hypothesis F constraint x B admitted sound) row

theorem passive_source_refinement
    (F : (S → Prop) → Prop) (old fresh : S → X → Prop)
    (stronger : ∀ s x, fresh s x → old s x)
    (legal : X → (S → Prop) → A → Prop) (a : A)
    (row : ByzantineEvidence.Robust (ByzantineEvidence.Hypothesis F old) legal a) :
    ByzantineEvidence.Robust (ByzantineEvidence.Hypothesis F fresh) legal a :=
  ByzantineEvidence.evidence_expands_safe_actions (ByzantineEvidence.Hypothesis F old) (ByzantineEvidence.Hypothesis F fresh) legal
    (fun x B h => ByzantineEvidence.added_evidence_refines F old fresh stronger x B h) a row

def refineView (K : Kernel I F X O A) (view : I → X → N) : Kernel I F X N A :=
  ⟨view, K.compliant, K.next, K.edgeGood⟩

def pullback (forget : I → N → O) (p : Assignment (I × O) A) : Assignment (I × N) A :=
  fun v => p (v.1, forget v.1 v.2)

theorem passive_view_row_transport (K : Kernel I F X O A) (view : I → X → N)
    (forget : I → N → O) (commutes : ∀ i x, K.view i x = forget i (view i x))
    (Q : F → X → Prop) (f : F) (x : X) (p : Assignment (I × O) A)
    (row : robustRow K Q f x p) :
    robustRow (refineView K view) Q f x (pullback forget p) := by
  have follows : ∀ actions, Follows (refineView K view) f x (pullback forget p) actions →
      Follows K f x p actions := by
    intro actions h i hi
    have hlocal := h i hi
    simpa [Follows, pullback, refineView, commutes i x] using hlocal
  exact ⟨fun actions h => row.1 actions (follows actions h),
         fun actions y h next => row.2 actions y (follows actions h) next⟩

def PairSupport (Q : ByzantineControlDigital.Actor → Prop) : Prop :=
  ∃ i j, i ≠ j ∧ ∀ k, Q k ↔ k = i ∨ k = j

def TerminalHistory (b : ByzantineControlDigital.Fault) (round : ByzantineControlDigital.RoundData) (h : ByzantineQuorumAlignment.History ByzantineControlDigital.Actor Bool) : Prop :=
  ∀ i v, ByzantineQuorumAlignment.Seen h i v → ByzantineControlDigital.Terminal b round i v

theorem terminal_history_exclusive (b : ByzantineControlDigital.Fault) (round : ByzantineControlDigital.RoundData)
    (h : ByzantineQuorumAlignment.History ByzantineControlDigital.Actor Bool) (terminal : TerminalHistory b round h) :
    ByzantineQuorumAlignment.Exclusive (fun i => ¬ ByzantineControlDigital.correct b i) h := by
  classical
  intro i hi v w hv hw
  have correct : ByzantineControlDigital.correct b i := by simpa using hi
  exact (terminal i v hv correct).symm.trans (terminal i w hw correct)

theorem pair_certificate_to_digital (b : ByzantineControlDigital.Fault) (round : ByzantineControlDigital.RoundData)
    (h : ByzantineQuorumAlignment.History ByzantineControlDigital.Actor Bool) (terminal : TerminalHistory b round h)
    (value : Bool) (cert : ByzantineQuorumAlignment.Certificate PairSupport h value) :
    ByzantineControlDigital.Certificate b round value := by
  obtain ⟨Q, ⟨i,j,neq,support⟩, shares⟩ := cert
  exact ⟨i,j,neq,terminal i value (shares i ((support i).mpr (Or.inl rfl))),
    terminal j value (shares j ((support j).mpr (Or.inr rfl)))⟩

theorem digital_receipt_row_sound (b : ByzantineControlDigital.Fault) (round : ByzantineControlDigital.RoundData)
    (legal : ByzantineControlDigital.Legal b round) (issued received : ByzantineQuorumAlignment.History ByzantineControlDigital.Actor Bool)
    (terminal : TerminalHistory b round issued) (sound : ByzantineQuorumAlignment.ReceiptSound issued received)
    (value : Bool) (cert : ByzantineQuorumAlignment.Certificate PairSupport received value) :
    ∀ i, ByzantineControlDigital.correct b i → ByzantineControlDigital.decision round i = value := by
  have actual := ByzantineQuorumAlignment.receipt_certificate_issued PairSupport issued received sound value cert
  exact ByzantineControlDigital.certificate_sound b round legal value
    (pair_certificate_to_digital b round issued terminal value actual)

theorem digital_cutoff_available (b : ByzantineControlDigital.Fault) (round : ByzantineControlDigital.RoundData)
    (legal : ByzantineControlDigital.Legal b round) (received : ByzantineQuorumAlignment.History ByzantineControlDigital.Actor Bool)
    (delivered : ∀ i, ByzantineControlDigital.correct b i → ByzantineQuorumAlignment.Seen received i (ByzantineControlDigital.decision round i)) :
    ∃ value, ByzantineQuorumAlignment.Certificate PairSupport received value := by
  obtain ⟨value,i,j,neq,hi,hj,di,dj⟩ := ByzantineControlDigital.certificate_available b round legal
  refine ⟨value, (fun k => k = i ∨ k = j), ⟨i,j,neq,fun _ => Iff.rfl⟩, ?_⟩
  intro k hk
  rcases hk with h | h
  · subst k
    simpa [di] using delivered i hi
  · subst k
    simpa [dj] using delivered j hj

end ByzantineAlignment

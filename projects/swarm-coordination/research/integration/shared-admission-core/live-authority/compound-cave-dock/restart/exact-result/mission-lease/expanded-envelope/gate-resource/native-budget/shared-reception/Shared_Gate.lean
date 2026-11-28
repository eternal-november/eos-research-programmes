import Mathlib

namespace SharedGate

/-- Scope is separate from the producer's observation and from the radio receipt. -/
def acceptable (qualified recipient hold : Prop) (issueEpoch liveEpoch : Nat) : Prop :=
  qualified ∧ recipient ∧ hold ∧ issueEpoch = liveEpoch

theorem safe_use
    {qualified recipient hold : Prop}
    {issueEpoch liveEpoch issue useAt : Nat}
    {clear : Nat → Prop}
    (hread : qualified → issueEpoch = liveEpoch → clear issue)
    (hframe : hold → clear issue → issue ≤ useAt → clear useAt)
    (time : issue ≤ useAt)
    (accepted : acceptable qualified recipient hold issueEpoch liveEpoch) :
    clear useAt :=
  hframe accepted.2.2.1 (hread accepted.1 accepted.2.2.2) time

/-- For a deterministic receiver restricted to this observation, opposite obligations
    on equal observations cannot both be met. -/
theorem same_report_cannot_decide
    {Tape : Type} {clearTape busyTape : Tape}
    (same : clearTape = busyTape) :
    ¬ ∃ decide : Tape → Bool, decide clearTape = true ∧ decide busyTape = false := by
  rintro ⟨f, go, stop⟩
  rw [same, stop] at go
  contradiction

/-- Native fan-out charges separately; app-local copying is not another radio attempt. -/
theorem budget_boundary (bytes cap : Nat) :
    (bytes ≤ cap ∧ cap < bytes + bytes) → bytes ≤ cap ∧ ¬ bytes + bytes ≤ cap := by
  omega

/-- A real qualification at issuance can become stale even in the same epoch
    when the use-time hold is absent. -/
theorem issuance_alone_not_enough :
    ∃ clear : Nat → Prop, clear 1 ∧ ¬ clear 2 := by
  exact ⟨fun t => t = 1, rfl, by decide⟩

end SharedGate

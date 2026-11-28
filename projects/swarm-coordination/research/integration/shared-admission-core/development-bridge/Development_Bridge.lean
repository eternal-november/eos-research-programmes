import Mathlib
namespace DevelopmentBridge

def Spend (cap occupied evidence req : Nat) : Prop :=
  occupied + evidence + req ≤ cap

theorem local_five_joint_not_five : Spend 5 0 1 4 ∧ Spend 5 0 1 4 ∧ ¬ Spend 5 0 2 4 := by
  unfold Spend
  decide

theorem two_evidence_bytes_cutoff (cap : Nat) : Spend cap 0 (1+1) 4 ↔ 6 ≤ cap := by
  rfl

-- Evaluator sees which row the old key names. A decision from the
-- retired public view alone must nominate the same row in both cases.
theorem missing_binding_cannot_be_resolved (resolve : Unit → Fin 2) :
    ¬ ∀ oldRow : Fin 2, resolve () = oldRow := by
  intro h
  have hc := (h 0).symm.trans (h 1)
  contradiction

-- A qualified ordinal, once reached, is sufficient at its exact scope.
theorem current_ordinal_reflects (a b : Fin 2) :
    (∀ q : Fin 2, (a = q) ↔ (b = q)) ↔ a = b := by
  constructor
  · intro h
    exact ((h a).mp rfl).symm
  · rintro rfl; simp

end DevelopmentBridge

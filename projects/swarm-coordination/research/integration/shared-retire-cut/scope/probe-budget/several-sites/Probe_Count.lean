import Mathlib
namespace ProbeCount

theorem extremal_recurrence (B k : ℕ) (hk : k.succ ≤ B) :
    (B.succ).choose k.succ-1 =
      1 + (B.choose k-1) + (B.choose k.succ-1) := by
  rw [Nat.choose_succ_succ]
  have h1 := Nat.choose_pos (show k ≤ B by omega)
  have h2 := Nat.choose_pos hk
  omega

theorem named_two_positive_bound :
    (3+1 : ℕ).choose 2 - 1 = 5 ∧ (9+1 : ℕ).choose 2 - 1 = 44 := by decide

#print axioms extremal_recurrence
#print axioms named_two_positive_bound
end ProbeCount

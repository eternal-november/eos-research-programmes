import Mathlib

namespace SwarmSelector

theorem normalized_ne_iff (left right : Bool) :
    left ≠ right ↔ left = !right := by
  cases left <;> cases right <;> decide

theorem half_crossing (p : ℕ → ℚ) (n : ℕ)
    (h0 : p 0 < (1/2 : ℚ)) (hn : (1/2 : ℚ) ≤ p n) :
    ∃ i < n, p i ≤ (1/2 : ℚ) ∧ (1/2 : ℚ) ≤ p (i+1) := by
  induction n with
  | zero => exact (not_le_of_gt h0 hn).elim
  | succ k ih =>
    by_cases H : p k < (1/2 : ℚ)
    · exact ⟨k, Nat.lt_succ_self k, le_of_lt H, hn⟩
    · obtain ⟨i, hi, ha, hb⟩ := ih (le_of_not_gt H)
      exact ⟨i, Nat.lt_trans hi (Nat.lt_succ_self k), ha, hb⟩

theorem independent_disagreement_ge_half {a b : ℚ}
    (ha : a ≤ (1/2 : ℚ)) (hb : (1/2 : ℚ) ≤ b) :
    (1/2 : ℚ) ≤ a * (1 - b) + (1 - a) * b := by
  have h := mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)
  nlinarith

theorem path_independent_obstruction (p : ℕ → ℚ) (n : ℕ)
    (h0 : p 0 = 0) (hn : p n = 1) :
    ∃ i < n, (1/2 : ℚ) ≤ p i * (1 - p (i+1)) + (1 - p i) * p (i+1) := by
  obtain ⟨i, hi, ha, hb⟩ := half_crossing p n (by rw [h0]; norm_num) (by rw [hn]; norm_num)
  exact ⟨i,hi, independent_disagreement_ge_half ha hb⟩

theorem threshold_unique {u v i j : ℕ}
    (h : v ≤ u+1) (hi : u ≤ i ∧ i < v) (hj : u ≤ j ∧ j < v) : i = j := by
  omega

#print axioms normalized_ne_iff
#print axioms path_independent_obstruction
#print axioms threshold_unique
end SwarmSelector

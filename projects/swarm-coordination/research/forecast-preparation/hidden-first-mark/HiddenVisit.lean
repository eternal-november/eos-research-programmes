import Mathlib

namespace HiddenVisit

theorem sharp_interval (r : ℚ) :
    (∃ hid : ℚ, 0 ≤ hid ∧ hid ≤ 1 ∧ r = 1/4 + hid/2) ↔
      (1/4 ≤ r ∧ r ≤ 3/4) := by
  constructor
  · rintro ⟨h, hl, hu, rfl⟩
    constructor <;> linarith
  · rintro ⟨lo, hi⟩
    refine ⟨2*r-1/2, ?_, ?_, ?_⟩ <;> linarith

theorem no_positive_robust_mix (prep0 prep1 : ℚ) :
    min ((prep0-prep1)/8) ((prep1-prep0)/8) ≤ 0 := by
  by_cases h : prep0 ≤ prep1
  · exact le_trans (min_le_left _ _) (by linarith)
  · exact le_trans (min_le_right _ _) (by linarith)

theorem stop_after_one_cost :
    (1/40 : ℚ) < 1/32 ∧
    (1/16 : ℚ) < 1/32 + 5/8*(1/40) + 3/8*(3/32) ∧
    (3/32 : ℚ) = 1/32 + 1/16 := by norm_num

#print axioms sharp_interval
#print axioms no_positive_robust_mix
#print axioms stop_after_one_cost
end HiddenVisit

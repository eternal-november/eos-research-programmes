import Mathlib
namespace Pooling

theorem allocated_bound (x a b : ℚ) (h0 : 0 ≤ x) (h1 : x ≤ 1 / 4) :
    a * x + b * (1 / 4 - x) ≤ max a b / 4 := by
  have ha := mul_le_mul_of_nonneg_right (le_max_left a b) h0
  have hb := mul_le_mul_of_nonneg_right (le_max_right a b)
    (show 0 ≤ 1 / 4 - x by linarith)
  linarith

theorem allocated_attained (a b : ℚ) :
    ∃ x : ℚ, 0 ≤ x ∧ x ≤ 1 / 4 ∧
      a * x + b * (1 / 4 - x) = max a b / 4 := by
  by_cases h : b ≤ a
  · refine ⟨1 / 4, by norm_num, le_rfl, ?_⟩
    rw [max_eq_left h]
    ring
  · have h' : a ≤ b := le_of_not_ge h
    refine ⟨0, le_rfl, by norm_num, ?_⟩
    rw [max_eq_right h']
    ring

theorem pooled_fraction_cap (a b : ℚ) (h : max a b / 4 ≤ 1 / 10) :
    (a + b) / 2 ≤ 2 / 5 := by
  linarith [le_max_left a b, le_max_right a b]

theorem linked_fraction_cap (a b : ℚ) (ha : a ≤ 1) (h : b / 4 ≤ 1 / 10) :
    (a + b) / 2 ≤ 7 / 10 := by linarith

#print axioms allocated_bound
#print axioms allocated_attained
#print axioms pooled_fraction_cap
#print axioms linked_fraction_cap
end Pooling

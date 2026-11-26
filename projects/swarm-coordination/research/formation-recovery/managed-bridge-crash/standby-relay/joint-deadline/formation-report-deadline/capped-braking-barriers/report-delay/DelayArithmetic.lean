import Mathlib
namespace BrakeNotice

theorem convex_tail_lower (r k : ℝ) (hr : 0 ≤ r) :
    2 * r ^ 2 ≤ (max 0 (r-k))^2 + (max 0 (r+k))^2 := by
  by_cases hl : 0 ≤ r-k
  · rw [max_eq_right hl]
    by_cases hh : 0 ≤ r+k
    · rw [max_eq_right hh]
      nlinarith [sq_nonneg k]
    · rw [max_eq_left (le_of_not_ge hh)]
      have hmul := mul_nonneg (show 0 ≤ -(r+k) by linarith) (show 0 ≤ r-k+2*r by linarith)
      nlinarith [sq_nonneg r]
  · rw [max_eq_left (le_of_not_ge hl)]
    have hh : 0 ≤ r+k := by linarith
    rw [max_eq_right hh]
    have hmul := mul_nonneg (show 0 ≤ -(r-k) by linarith) (show 0 ≤ r+k+2*r by linarith)
    nlinarith [sq_nonneg r]

theorem equal_clearance_expansion (a w t : ℝ) (ha : a ≠ 0) :
    w*t-a*t^2/2+(w-a*t)^2/(4*a) =
      w^2/(4*a)+w*t/2-a*t^2/4 := by field_simp; ring

theorem same_total_different_feasibility :
    (2:ℚ)*(23/64) = 1/4+15/32 ∧ (15:ℚ)/32 < 1/2 := by norm_num

#print axioms convex_tail_lower
#print axioms equal_clearance_expansion
#print axioms same_total_different_feasibility
end BrakeNotice

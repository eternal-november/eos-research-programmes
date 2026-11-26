import Mathlib
namespace BrakeAmendment

theorem square_hinge_upper (d h y : ℝ) (hh : 0 < h) (hy : 0 ≤ y) :
    y*d-h*y^2/2 ≤ (max 0 d)^2/(2*h) := by
  by_cases hd : 0 ≤ d
  · rw [max_eq_right hd]
    apply (le_div_iff₀ (show 0 < 2*h by positivity)).2
    nlinarith [sq_nonneg (d-h*y)]
  · rw [max_eq_left (le_of_not_ge hd)]
    simp only [zero_pow (by decide : 2 ≠ 0), zero_div]
    have p := mul_nonpos_of_nonneg_of_nonpos hy (le_of_not_ge hd)
    have q := mul_nonneg hh.le (sq_nonneg y)
    linarith

theorem square_hinge_reaches (d h : ℝ) (hh : 0 < h) :
    ∃ y : ℝ, 0 ≤ y ∧ y*d-h*y^2/2 = (max 0 d)^2/(2*h) := by
  by_cases hd : 0 ≤ d
  · rw [max_eq_right hd]
    refine ⟨d/h, div_nonneg hd hh.le, ?_⟩
    field_simp
    ring
  · rw [max_eq_left (le_of_not_ge hd)]
    exact ⟨0, le_rfl, by simp⟩

#print axioms square_hinge_upper
#print axioms square_hinge_reaches
end BrakeAmendment

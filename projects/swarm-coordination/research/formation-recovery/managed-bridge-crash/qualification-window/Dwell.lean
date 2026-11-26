import Mathlib

namespace Dwell

/-- Distance with immediate maximum braking, followed by waiting. -/
noncomputable def displacement (entry a duration : ℝ) : ℝ :=
  let b := min duration (entry / a)
  entry*b - a*b*b/2

theorem before_stop (u a h : ℝ) (hcut : h ≤ u / a) :
    displacement u a h = u*h-a*h*h/2 := by
  simp [displacement, min_eq_left hcut]

theorem cut (u : ℝ) (hu : 0 ≤ u) :
    displacement u 1 (1/4) ≤ 1/8 ↔ u ≤ 5/8 := by
  by_cases h : u ≤ 1/4
  · simp only [displacement, div_one, min_eq_right h]
    have hsq : u*u ≤ (1:ℝ)/16 := by nlinarith [mul_nonneg hu (sub_nonneg.mpr h)]
    constructor <;> intro he <;> nlinarith
  · have h1 : (1:ℝ)/4 ≤ u / 1 := by simpa using le_of_lt (lt_of_not_ge h)
    rw [before_stop _ _ _ h1]
    constructor <;> intro he <;> linarith

theorem braking_distance_from_unit :
    ((1:ℝ)^2 - (5/8)^2)/2 = 39/128 := by norm_num

end Dwell

#print axioms Dwell.before_stop
#print axioms Dwell.cut
#print axioms Dwell.braking_distance_from_unit

import Mathlib
namespace MovingZone

noncomputable def ceiling : ℝ := (7 + Real.sqrt 33) / 2

theorem peak_iff (h : ℝ) (hh : 2 ≤ h) :
    h + 4 / h ≤ 7 ↔ h ≤ ceiling := by
  have hp : 0 < h := by linarith
  have hd : h + 4 / h ≤ 7 ↔ h*h - 7*h + 4 ≤ 0 := by
    rw [show h + 4/h = (h*h+4)/h by field_simp]
    rw [div_le_iff₀ hp]
    constructor <;> intro a <;> linarith
  rw [hd]
  have hs : (Real.sqrt 33)^2 = (33:ℝ) := Real.sq_sqrt (by norm_num)
  have hsf : 5 < Real.sqrt (33:ℝ) := by
    by_contra! hc
    nlinarith [Real.sqrt_nonneg (33:ℝ)]
  have hlow : 0 < 2*h - 7 + Real.sqrt 33 := by linarith
  have f : (2*h - 7 - Real.sqrt 33)*(2*h - 7 + Real.sqrt 33) = 4*(h*h - 7*h + 4) := by nlinarith
  constructor
  · intro h0
    have hp' : (2*h-7-Real.sqrt 33)*(2*h-7+Real.sqrt 33) ≤ 0 := by rw [f]; linarith
    have hh' : 2*h - 7 - Real.sqrt 33 ≤ 0 := nonpos_of_mul_nonpos_left hp' hlow
    unfold ceiling; linarith
  · intro h0
    unfold ceiling at h0
    have h1 : 2*h - 7 - Real.sqrt 33 ≤ 0 := by linarith
    have h2 := mul_nonpos_of_nonpos_of_nonneg h1 (le_of_lt hlow)
    rw [f] at h2
    linarith

#print axioms peak_iff
end MovingZone

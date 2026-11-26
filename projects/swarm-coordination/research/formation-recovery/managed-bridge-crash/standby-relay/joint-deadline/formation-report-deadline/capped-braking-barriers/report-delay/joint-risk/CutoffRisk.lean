import Mathlib
namespace CutoffRisk

theorem binary_cost_lower (a b p : ℝ) (hp : 0 ≤ p) (hP : p ≤ 1) :
    min a b ≤ a*(1-p)+b*p := by
  by_cases h : a ≤ b
  · rw [min_eq_left h]
    nlinarith [mul_nonneg (sub_nonneg.mpr h) hp]
  · have h' : b ≤ a := le_of_not_ge h
    rw [min_eq_right h']
    nlinarith [mul_nonneg (sub_nonneg.mpr h') (sub_nonneg.mpr hP)]

theorem overlap_upper (a b A B : ℝ) (ha : a ≤ A) (hb : b ≤ B) :
    min a b ≤ min (min A B) ((a+b)/2) := by
  apply le_min (le_min
    (le_trans (min_le_left _ _) ha)
    (le_trans (min_le_right _ _) hb))
  have hl := min_le_left a b
  have hr := min_le_right a b
  linarith

theorem erasure_coupling_witness :
    min ((1:ℚ)/20) (1/20) = 1/20 ∧ min ((1:ℚ)/10) 0 = 0 := by norm_num

#print axioms binary_cost_lower
#print axioms overlap_upper
#print axioms erasure_coupling_witness
end CutoffRisk

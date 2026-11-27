import Mathlib
theorem paired_center_line_exact {a b r : ℝ} (ha : 0 ≤ a) :
    (∀ x y z : ℝ, -a ≤ x → x ≤ a → y^2 + z^2 ≤ b^2 →
        (x+a)^2+y^2+z^2 < r^2 ∨ (x-a)^2+y^2+z^2 < r^2) ↔
        a^2 + b^2 < r^2 := by
  constructor
  · intro h
    have hh := h 0 b 0 (by linarith) ha (by simp)
    rcases hh with hh | hh <;> nlinarith
  · intro h x y z hlo hhi hperp
    by_cases hx : 0 ≤ x
    · right
      have hxa := mul_nonneg hx (sub_nonneg.mpr hhi)
      have hpa := mul_nonneg ha hx
      nlinarith
    · left
      have hneg : 0 ≤ -x := by linarith
      have hax : 0 ≤ a + x := by linarith
      have h1 := mul_nonneg hneg hax
      have h2 := mul_nonneg ha hneg
      nlinarith

theorem endpoint_ball_inclusion {a b r d : ℝ}
    (h : a^2 + b^2 < r^2) (hd : d ≤ b^2) : d < r^2 := by
  nlinarith [sq_nonneg a]

theorem eroded_spheres_can_lose_valid_case :
    (10 : ℝ) ≤ 6+6 ∧ (6 : ℝ)^2+6^2 < 10^2 := by norm_num

#print axioms paired_center_line_exact
#print axioms endpoint_ball_inclusion
#print axioms eroded_spheres_can_lose_valid_case

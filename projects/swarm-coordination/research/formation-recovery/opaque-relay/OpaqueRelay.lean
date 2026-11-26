import Mathlib

namespace OpaqueRelay

theorem far_point (a x y t : ℝ) (ha : 0 ≤ a) (hx : 0 ≤ x)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (t*x - (1-t)*a)^2 + (t*y)^2 ≤ (t*x + (1-t)*a)^2 + (t*y)^2 := by
  have hh : 0 ≤ 4 * (t*x) * ((1-t)*a) := by positivity
  nlinarith only [hh]

theorem angular_test (a r x y : ℝ) (hp : 0 < a^2 - r^2) :
    r^2 * ((a+x)^2+y^2) ≤ a^2*y^2 ↔
    (r^2/(a^2-r^2))*(a+x)^2 ≤ y^2 := by
  rw [div_mul_eq_mul_div, div_le_iff₀ hp]
  constructor <;> intro h <;> nlinarith only [h]

def Feasible (a k q2 H2 R2 x z : ℝ) : Prop :=
  0 ≤ x ∧ 0 ≤ z ∧ z ≤ H2 ∧ q2 ≤ x^2+z ∧
  k*(a+x)^2 ≤ z ∧ (a+x)^2+z ≤ R2

def Cuts (a k q2 H2 R2 x : ℝ) : Prop :=
  0 ≤ x ∧ q2-x^2 ≤ H2 ∧ k*(a+x)^2 ≤ H2 ∧
  a^2+q2+2*a*x ≤ R2 ∧ (1+k)*(a+x)^2 ≤ R2

theorem vertical_elimination (a k q2 H2 R2 x : ℝ) (hk : 0 ≤ k) :
    (∃ z, Feasible a k q2 H2 R2 x z) ↔ Cuts a k q2 H2 R2 x := by
  constructor
  · rintro ⟨z, hx, _, hH, hq, ho, hR⟩
    exact ⟨hx, by linarith, le_trans ho hH, by nlinarith only [hq,hR],
      by nlinarith only [ho,hR]⟩
  · rintro ⟨hx, hq, ho, hc, hR⟩
    let z := max (q2-x^2) (k*(a+x)^2)
    have hl : q2-x^2 ≤ z := le_max_left _ _
    have hr : k*(a+x)^2 ≤ z := le_max_right _ _
    have hh : z ≤ H2 := max_le hq ho
    have hrr : z ≤ R2-(a+x)^2 := max_le
      (by nlinarith only [hc]) (by nlinarith only [hR])
    exact ⟨z, hx, le_trans (by positivity) hr, hh, by linarith, hr, by linarith⟩

theorem innermost (a k q2 H2 R2 x0 x : ℝ)
    (ha : 0 ≤ a) (hk : 0 ≤ k) (hz : 0 ≤ x0)
    (hmin : q2-x0^2 ≤ H2) (horder : x0 ≤ x)
    (h : Cuts a k q2 H2 R2 x) : Cuts a k q2 H2 R2 x0 := by
  obtain ⟨_,_,ho,hq,hR⟩ := h
  have hsq : (a+x0)^2 ≤ (a+x)^2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr horder) (show 0 ≤ 2*a+x+x0 by linarith)]
  have ho' := mul_le_mul_of_nonneg_left hsq hk
  have hR' := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 1+k by linarith)
  have hq' := mul_le_mul_of_nonneg_left horder (show 0 ≤ 2*a by positivity)
  exact ⟨hz,hmin,le_trans ho' ho,by linarith,le_trans hR' hR⟩

#print axioms far_point
#print axioms angular_test
#print axioms vertical_elimination
#print axioms innermost

end OpaqueRelay

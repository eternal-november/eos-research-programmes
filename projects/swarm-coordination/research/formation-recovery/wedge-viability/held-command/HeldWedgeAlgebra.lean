import Mathlib

namespace HeldWedge

theorem minus_face_slack_during_first_hold (g t : ℝ) (hg : 1 ≤ g) :
    -g + (g-1)*(t-1)^2/2 + ((g-1)*(t-1))^2/(2*(1+g)) =
      -g + (g*(g-1)/(1+g))*(t-1)^2 := by
  have h : 1+g ≠ 0 := by linarith
  field_simp
  ring

theorem safe_endpoint_with_no_viable_continuation :
    let t : ℝ := 29/10
    let q : ℝ := -2+(t-1)^2/2
    let p : ℝ := t-1
    q < 0 ∧ 0 < q+p^2/6 := by
  norm_num

theorem second_hold_positive_face_endpoint (h : ℝ) (hh : 3/2 ≤ h) :
    -3/2+6*h-4*h^2 ≤ -3/2 := by
  have ha : 0 ≤ 4*h-6 := by linarith
  have hb : 0 ≤ h := by linarith
  nlinarith [mul_nonneg ha hb]

#print axioms minus_face_slack_during_first_hold
#print axioms safe_endpoint_with_no_viable_continuation
#print axioms second_hold_positive_face_endpoint

end HeldWedge

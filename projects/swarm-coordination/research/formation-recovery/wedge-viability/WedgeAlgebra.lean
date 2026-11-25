import Mathlib

namespace WedgeRecovery

theorem incompatible_outer_faces_cannot_both_bind
    (g v z d : ℝ) (hg : 1 ≤ g) (hp : 0 < v+z) (hm : 0 < v-z)
    (haxis : v^2 ≤ 2*d) (hout : 2*(1+g)*d = v^2 + z^2) : False := by
  have hv : 0 < v := by linarith
  have hz : z^2 < v^2 := by
    have h := mul_pos hp hm
    nlinarith
  have hvd : 0 ≤ d := by nlinarith [sq_nonneg v]
  have hprod := mul_nonneg (show 0 ≤ g-1 by linarith) hvd
  nlinarith

theorem half_slope_scalar_limits_hold_without_joint_tangency :
    let g : ℝ := 1/2
    let x : ℝ := -25/48
    let y : ℝ := -1
    let v : ℝ := 1
    let w : ℝ := 3/2
    x+v^2/2 < 0 ∧
      x+g*y+(v+g*w)^2/(2*(1+g)) = 0 ∧
      x-g*y+(v-g*w)^2/(2*(1+g)) = 0 ∧
      ¬ ∃ a b : ℝ, -1 ≤ a ∧ a+g*b ≤ -(1+g) ∧ a-g*b ≤ -(1+g) := by
  dsimp
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  rintro ⟨a,b,ha,hp,hm⟩
  linarith

theorem delayed_facet_identity (A t g : ℝ) (hg : 0 ≤ g) :
    A*t-t^2/2+(A-t)^2/(2*(1+g)) =
      A^2/2-g*(A-t)^2/(2*(1+g)) := by
  have h : 1+g ≠ 0 := by linarith
  field_simp
  ring

#print axioms incompatible_outer_faces_cannot_both_bind
#print axioms half_slope_scalar_limits_hold_without_joint_tangency
#print axioms delayed_facet_identity

end WedgeRecovery

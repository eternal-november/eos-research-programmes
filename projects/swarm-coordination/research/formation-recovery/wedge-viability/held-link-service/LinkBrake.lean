import Mathlib

namespace LinkBrake

theorem simultaneous_zero_same {s t cx cy : ℝ} (ht : 0 < t)
    (hx : -s + cx*t = 0) (hy : -s + cy*t = 0) :
    cx = cy := by
  have h : (cx-cy)*t = 0 := by linarith [hx,hy]
  rcases mul_eq_zero.mp h with hzero|hzero
  · linarith
  · linarith

theorem near_far_disjoint (u : ℚ)
    (near : u ≤ 12/5) (far : 13/5 ≤ u) : False := by
  linarith

theorem far_loses_shorter_deadline (u : ℚ)
    (time : u ≤ 5/2) (far : 13/5 ≤ u) : False := by
  linarith

#print axioms simultaneous_zero_same
#print axioms near_far_disjoint
#print axioms far_loses_shorter_deadline

end LinkBrake

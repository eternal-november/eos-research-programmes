import Mathlib

namespace BrakingDwell

theorem barrier_compare (x y v w A L : ℝ)
    (hA : 0 < A) (hx : y < x) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (source : 2*A*x + v*v ≤ 2*A*L)
    (barrier : 2*A*y + w*w = 2*A*L) :
    v < w := by
  by_contra hn
  have vh : w ≤ v := le_of_not_gt hn
  have square : w*w ≤ v*v := mul_le_mul vh vh hw hv
  have hx' : 2*A*y < 2*A*x := mul_lt_mul_of_pos_left hx (by positivity)
  linarith

theorem joint_dwell_counterexample :
    let T : ℚ := 28/25
    let H : ℚ := 2/5
    let Q : ℚ := 1/4
    let s : ℚ := 71/100
    let c := T-H
    let gap (t : ℚ) := s*s/2+s*(t-s)-(t-s)^2/2
    (1 ≤ T) ∧ c ≥ s ∧ Q ≤ gap c ∧ gap T < 3/5 ∧
    0 < s-(T-s) ∧ T/2 < c ∧ T*T/4-H*H/2 < Q := by
  norm_num

#print axioms barrier_compare
#print axioms joint_dwell_counterexample
end BrakingDwell

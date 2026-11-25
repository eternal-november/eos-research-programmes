import Mathlib

theorem necessary_motion (gap a t : ℝ)
    (ha : 0 < a) (h : gap ≤ a * t^2 / 2) :
    2 * gap / a ≤ t^2 := by
  apply (div_le_iff₀ ha).2
  linarith

theorem equal_terminal_displacement (a t : ℝ) :
    a * (t/2)^2 / 2 +
      (a * (t/2)) * (t/2) - a * (t/2)^2 / 2 = a * t^2 / 4 := by
  ring

theorem robust_deadline (announce motion dwell deadline : ℚ)
    (h : announce + motion + dwell ≤ deadline) :
    announce ≤ deadline - motion - dwell := by
  linarith

#print axioms necessary_motion
#print axioms equal_terminal_displacement
#print axioms robust_deadline

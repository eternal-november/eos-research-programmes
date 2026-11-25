import Mathlib
theorem same_record_gap (a b offset error0 error1 : ℚ)
    (h0 : |a-offset| ≤ error0+error1) (h1 : |b-offset| ≤ error0+error1) :
    b-a ≤ 2*(error0+error1) := by
  have ha := (abs_le.mp h0).1
  have hb := (abs_le.mp h1).2
  linarith

theorem cover_by_midpoint (lo hi e x : ℚ)
    (hl : lo ≤ x) (hh : x ≤ hi) (h : hi-lo ≤ 4*e) :
    |x-(lo+hi)/2| ≤ 2*e := by
  apply abs_le.mpr
  constructor <;> linarith

#print axioms same_record_gap
#print axioms cover_by_midpoint

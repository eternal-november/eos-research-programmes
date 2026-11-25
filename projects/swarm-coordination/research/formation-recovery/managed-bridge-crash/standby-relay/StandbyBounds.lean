import Mathlib

theorem centered_pair_bound (x a b R : ℚ)
    (ha : (x-a)^2 ≤ R) (hb : (x-b)^2 ≤ R) :
    (a-b)^2/4 + (x-(a+b)/2)^2 ≤ R := by
  nlinarith

theorem weighted_radial_bound (x a b R w : ℚ)
    (h0 : 0 ≤ w) (h1 : w ≤ 1)
    (ha : (x-a)^2 ≤ R) (hb : (x-b)^2 ≤ R) :
    w*(x-a)^2 + (1-w)*(x-b)^2 ≤ R := by
  have hA := mul_le_mul_of_nonneg_left ha h0
  have hB := mul_le_mul_of_nonneg_left hb (sub_nonneg.mpr h1)
  nlinarith

#print axioms centered_pair_bound
#print axioms weighted_radial_bound

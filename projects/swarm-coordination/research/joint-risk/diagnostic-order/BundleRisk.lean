import Mathlib

theorem optional_probability_threshold (q : ℚ) :
    (3 : ℚ)/320 + q*((1 : ℚ)/10 - 3/320) ≤ 1/20 ↔ q ≤ 13/29 := by
  constructor <;> intro h <;> linarith

theorem dominant_complete_law (q old low high : ℚ) (h : 0 ≤ q) (h' : low ≤ high) :
    old + q*(low-old) ≤ old + q*(high-old) := by
  have hm := mul_le_mul_of_nonneg_left h' h
  linarith

#print axioms optional_probability_threshold
#print axioms dominant_complete_law

import Mathlib

namespace ShiftForecast

theorem noSingleRead (p : ℚ) : (p + (1-p))/2 = 1/2 := by ring

/-- Product of the two endpoint penalties divided by their sum is a
lower bound for every mixing rule. This avoids divide-by-zero pins. -/
theorem regretLower (a b x : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a*b ≤ (a+b)*max (a*x) (b*(1-x)) := by
  have h1 := mul_le_mul_of_nonneg_left (le_max_left (a*x) (b*(1-x))) hb
  have h2 := mul_le_mul_of_nonneg_left (le_max_right (a*x) (b*(1-x))) ha
  linarith [show b*(a*x)+a*(b*(1-x)) = a*b by ring,
    show (a+b)*max (a*x) (b*(1-x))
      = b*max (a*x) (b*(1-x)) + a*max (a*x) (b*(1-x)) by ring]

theorem regretAttained (a b : ℚ) (h : 0 < a+b) :
    max (a*(b/(a+b))) (b*(1-b/(a+b))) = a*b/(a+b) := by
  have hn : a+b ≠ 0 := ne_of_gt h
  have h1 : a*(b/(a+b)) = a*b/(a+b) := by ring
  have h2 : b*(1-b/(a+b)) = a*b/(a+b) := by
    field_simp
    ring
  rw [h1,h2,max_self]

/-- A calibrated symmetric bit read with independent erasure. -/
theorem protectedImprovement (a eps drop : ℚ) :
    2*a*(1/2 - (1/2 - a*(1-2*eps)*(1-drop))) =
        2*a^2*(1-2*eps)*(1-drop) := by ring

end ShiftForecast

#print axioms ShiftForecast.noSingleRead
#print axioms ShiftForecast.regretLower
#print axioms ShiftForecast.regretAttained
#print axioms ShiftForecast.protectedImprovement

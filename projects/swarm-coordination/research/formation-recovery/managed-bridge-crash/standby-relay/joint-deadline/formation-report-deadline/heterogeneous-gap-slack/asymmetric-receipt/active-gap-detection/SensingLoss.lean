import Mathlib

namespace ActiveGap

theorem sharp_lower (d q : ℝ) (hd : 0 < d) (hq : 0 ≤ q)
    (hadmissible : 2*d ≤ q^2) :
    Real.sqrt (3*d/2) ≤ q - Real.sqrt (q^2 - 2*d)/2 := by
  let k := Real.sqrt (3*d/2)
  let s := Real.sqrt (q^2 - 2*d)
  change k ≤ q - s/2
  have hk : 0 ≤ k := Real.sqrt_nonneg _
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hk2 : k^2 = 3*d/2 := Real.sq_sqrt (by linarith)
  have hs2 : s^2 = q^2 - 2*d := Real.sq_sqrt (by linarith)
  have hqk : k < q := by
    by_contra! hh
    have := mul_nonneg (sub_nonneg.mpr hh) (add_nonneg hk hq)
    nlinarith
  have hsq : s^2 ≤ (2*(q-k))^2 := by
    nlinarith [sq_nonneg (q-4*k/3)]
  by_contra! hh
  have h1 : 0 < s - 2*(q-k) := by linarith
  have h2 : 0 < s + 2*(q-k) := by linarith
  nlinarith [mul_pos h1 h2]

theorem probe_example :
    (1 : ℝ)/10 - Real.sqrt (((1 : ℝ)/10)^2 - 2*(3/800))/2 =
    Real.sqrt ((3 : ℝ)*(3/800)/2) := by
  have h1 : ((1 : ℝ)/10)^2 - 2*(3/800) = ((1 : ℝ)/20)^2 := by norm_num
  have h2 : (3 : ℝ)*(3/800)/2 = ((3 : ℝ)/40)^2 := by norm_num
  rw [h1, h2, Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs]
  norm_num

#print axioms sharp_lower
#print axioms probe_example
end ActiveGap

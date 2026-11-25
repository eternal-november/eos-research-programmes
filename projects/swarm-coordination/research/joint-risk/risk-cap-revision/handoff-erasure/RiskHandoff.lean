import Mathlib

namespace RiskHandoff

theorem low_cap_upper (r d q m : ℚ)
    (hq : r*q/2 ≤ d) (hm : r*m ≤ d) :
    1 - 2*r + r*q/2 + r*m ≤ 1 - 2*r + 2*d := by
  linarith

theorem canonical_rates (r d : ℚ) (hr : 0 < r)
    (hd : 0 ≤ d) (hlt : 2*d ≤ r) :
    let q := 2*d/r
    let m := d/r
    0 ≤ q ∧ q ≤ 1 ∧ 0 ≤ m ∧ m ≤ 1 ∧
      r*q/2 = d ∧ r*m = d := by
  dsimp
  refine ⟨div_nonneg (by linarith) hr.le, (div_le_one hr).2 hlt,
    div_nonneg hd hr.le, (div_le_one hr).2 (by linarith), ?_, ?_⟩
  · field_simp
  · field_simp

theorem thirds_corner (r d : ℚ) (hlt : 2*d ≤ r) :
    1 - 2*r + 2*d ≤ 1 - r := by
  linarith

end RiskHandoff

#print axioms RiskHandoff.low_cap_upper
#print axioms RiskHandoff.canonical_rates
#print axioms RiskHandoff.thirds_corner

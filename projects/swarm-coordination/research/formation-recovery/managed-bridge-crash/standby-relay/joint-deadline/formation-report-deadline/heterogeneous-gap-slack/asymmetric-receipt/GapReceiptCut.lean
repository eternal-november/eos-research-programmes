import Mathlib

namespace GapReceiptCut

noncomputable def mandatoryPeak (c : ℝ) : ℝ := 3 / 8 - (2 / 5) * (1-c)^2

noncomputable def critical : ℝ := 1 - Real.sqrt 7 / 4

theorem peak_complete (c : ℝ) :
    c - 1 / 8 - c^2/2 + (1-c)^2/10 = mandatoryPeak c := by
  unfold mandatoryPeak
  ring

theorem at_cut : mandatoryPeak critical = 1 / 5 := by
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 7)
  unfold mandatoryPeak critical
  nlinarith

theorem receipt_bound (c : ℝ) (h1 : c ≤ 1)
    (hsafe : mandatoryPeak c ≤ 1 / 5) :
    c ≤ critical := by
  by_contra! hlate
  unfold mandatoryPeak at hsafe
  unfold critical at hlate
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 7)
  have hn := Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 7)
  have hf : 0 < Real.sqrt 7 / 4 - (1-c) := by linarith
  have hg : 0 < Real.sqrt 7 / 4 + (1-c) := by linarith
  nlinarith [mul_pos hf hg]

#print axioms peak_complete
#print axioms at_cut
#print axioms receipt_bound

end GapReceiptCut

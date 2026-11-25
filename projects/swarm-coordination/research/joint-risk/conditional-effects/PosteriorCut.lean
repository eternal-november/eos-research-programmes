import Mathlib
namespace PosteriorCut

theorem spike_monotone (A B L M a w : ℝ)
    (ha : 0 < a) (hw : 0 ≤ w) (hB : 0 < B)
    (hA : A ≤ B) (hL : 0 ≤ L) (hM : L ≤ M) :
    (a*A+w*L)/(a*B+w*L) ≤ (a*A+w*M)/(a*B+w*M) := by
  have hM0 := le_trans hL hM
  have hdL : 0 < a*B+w*L := by positivity
  have hdM : 0 < a*B+w*M := by positivity
  rw [div_le_div_iff₀ hdL hdM]
  have h := mul_nonneg (mul_nonneg ha.le hw)
    (mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hM))
  nlinarith only [h]

theorem outside_spike (A B L a w : ℝ)
    (ha : 0 < a) (hw : 0 ≤ w) (hB : 0 < B) (hA : 0 ≤ A) (hL : 0 ≤ L) :
    (a*A)/(a*B+w*L) ≤ (a*A)/(a*B) := by
  have hd : 0 < a*B+w*L := by positivity
  rw [div_le_div_iff₀ hd (mul_pos ha hB)]
  have h := mul_nonneg (mul_nonneg ha.le hA) (mul_nonneg hw hL)
  nlinarith only [h]

theorem normalized_singletons_injective (a w x y : ℝ)
    (ha : 0 < a) (hw : 0 ≤ w) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : (a+w)*x/(a+w*x) = (a+w)*y/(a+w*y)) : x=y := by
  have hx' : a+w*x ≠ 0 := ne_of_gt (by positivity)
  have hy' : a+w*y ≠ 0 := ne_of_gt (by positivity)
  have e := (div_eq_div_iff hx' hy').mp h
  have h2 : a*(a+w)*x = a*(a+w)*y := by nlinarith only [e]
  exact mul_left_cancel₀ (ne_of_gt (by positivity)) h2

#print axioms spike_monotone
#print axioms outside_spike
#print axioms normalized_singletons_injective
end PosteriorCut

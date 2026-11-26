import Mathlib

namespace CapturedCurve

def f (a b c t : ℝ) := a*t^2 + b*t + c

theorem nonneg_test (a b c l r : ℝ) (hlr : l ≤ r) :
    (∀ t, l ≤ t → t ≤ r → 0 ≤ f a b c t) ↔
      0 ≤ f a b c l ∧ 0 ≤ f a b c r ∧
        (0 < a → l < -b/(2*a) → -b/(2*a) < r → 0 ≤ f a b c (-b/(2*a))) := by
  constructor
  · intro h
    refine ⟨h l le_rfl hlr, h r hlr le_rfl, ?_⟩
    intro _ h1 h2
    exact h _ h1.le h2.le
  · rintro ⟨hl, hr, hv⟩ t hlt htr
    by_cases hEq : l = r
    · have ht : t = l := le_antisymm (hEq ▸ htr) hlt
      simpa [ht] using hl
    · have hpos : 0 < r-l := sub_pos.mpr (lt_of_le_of_ne hlr hEq)
      by_cases ha : 0 < a
      · let v := -b/(2*a)
        have he : a * (2*v) = -b := by
          dsimp [v]
          field_simp
        have expansion (x y : ℝ) :
            f a b c x - f a b c y = a*(x-y)*(x+y-2*v) := by
          unfold f
          linear_combination (x-y) * he
        by_cases hvl : v ≤ l
        · have h := mul_nonneg (mul_nonneg ha.le (sub_nonneg.mpr hlt))
              (show 0 ≤ t+l-2*v by linarith)
          rw [← expansion] at h
          exact le_trans hl (sub_nonneg.mp h)
        · by_cases hrv : r ≤ v
          · have h := mul_nonneg_of_nonpos_of_nonpos
                (mul_nonpos_of_nonneg_of_nonpos ha.le (sub_nonpos.mpr htr))
                (show t+r-2*v ≤ 0 by linarith)
            rw [← expansion] at h
            exact le_trans hr (sub_nonneg.mp h)
          ·
            have hsq : 0 ≤ a*(t-v)*(t+v-2*v) := by
              have hh : a*(t-v)*(t+v-2*v) = a*(t-v)^2 := by ring
              rw [hh]
              positivity
            rw [← expansion] at hsq
            exact le_trans (hv ha (lt_of_not_ge hvl) (lt_of_not_ge hrv)) (sub_nonneg.mp hsq)
      · have hm : 0 ≤ -a := neg_nonneg.mpr (le_of_not_gt ha)
        have htl := sub_nonneg.mpr hlt
        have hrt := sub_nonneg.mpr htr
        have hsum : 0 ≤ (r-t)*f a b c l + (t-l)*f a b c r + (-a)*(r-l)*(t-l)*(r-t) :=
          add_nonneg (add_nonneg (mul_nonneg hrt hl) (mul_nonneg htl hr))
            (mul_nonneg (mul_nonneg (mul_nonneg hm hpos.le) htl) hrt)
        have eq : (r-t)*f a b c l + (t-l)*f a b c r + (-a)*(r-l)*(t-l)*(r-t)
            = (r-l)*f a b c t := by unfold f; ring
        rw [eq] at hsum
        by_contra! hneg
        exact (not_lt_of_ge hsum) (mul_neg_of_pos_of_neg hpos hneg)

theorem bernstein_den_pos (w0 w1 w2 t : ℝ) (h0 : 0 < w0) (h1 : 0 < w1) (h2 : 0 < w2)
    (hl : 0 ≤ t) (hr : t ≤ 1) :
    0 < w0*(1-t)^2 + w1*(2*t*(1-t)) + w2*t^2 := by
  have hrest : 0 ≤ w1*(2*t*(1-t)) := by positivity
  have hlast : 0 ≤ w2*t^2 := by positivity
  by_cases ht : t = 1
  · simpa [ht] using h2
  · have ht' : 0 < 1-t := sub_pos.mpr (lt_of_le_of_ne hr ht)
    have hfirst : 0 < w0*(1-t)^2 := by positivity
    linarith

theorem projected_clearance (K : Set ℝ) (m limit : ℝ)
    (D N : ℝ → ℝ) (l r : ℝ)
    (hm : m ∈ K) (hmax : ∀ z ∈ K, z ≤ m)
    (hD : ∀ t, l ≤ t → t ≤ r → 0 < D t) :
    (∀ t, l ≤ t → t ≤ r → ∀ z ∈ K, N t / D t + z ≤ limit) ↔
    (∀ t, l ≤ t → t ≤ r → 0 ≤ (limit-m)*D t - N t) := by
  constructor
  · intro h t htl htr
    have h' : N t / D t ≤ limit-m := by linarith [h t htl htr m hm]
    exact sub_nonneg.mpr ((div_le_iff₀ (hD t htl htr)).mp h')
  · intro h t htl htr z hz
    have h' : N t / D t ≤ limit-m :=
      (div_le_iff₀ (hD t htl htr)).mpr (sub_nonneg.mp (h t htl htr))
    linarith [hmax z hz]

end CapturedCurve

#print axioms CapturedCurve.nonneg_test
#print axioms CapturedCurve.bernstein_den_pos
#print axioms CapturedCurve.projected_clearance

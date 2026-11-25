import Mathlib
namespace ServiceRights

theorem everyLotteryBound (v a q x0 x1 u0 u1 : ℚ)
    (hv : 0 ≤ v) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hx0 : x0 ≤ 1)
    (ir : 0 ≤ u1) (ic : u1+a*x1 ≤ u0) :
    (1-q)*(v*x0-u0)+q*((v-a)*x1-u1) ≤ (1-q)*v+(q*v-a)*x1 := by
  have h := mul_le_mul_of_nonneg_left hx0 hv
  have h0 := mul_le_mul_of_nonneg_left h (sub_nonneg.mpr hq1)
  have h1 := mul_le_mul_of_nonneg_left ic (sub_nonneg.mpr hq1)
  have h2 := mul_nonneg hq0 ir
  nlinarith only [h0,h1,h2,ir]

theorem poolingCut (v a q m : ℚ) (hm : 0 < m) :
    a ≤ (q/m)*v ↔ a*m ≤ q*v := by
  rw [div_mul_eq_mul_div, le_div_iff₀ hm]

theorem noStrictBandAtSmallOption (v a q m c : ℚ)
    (qp : q*v ≤ c) (pool : a*m ≤ q*v) : ¬ c < a*m := by
  linarith

theorem discloseForfeitsRent (a lambda : ℚ) (ha : 0 < a) (hl : 0 < lambda) :
    0 < lambda*a := mul_pos hl ha

end ServiceRights
#print axioms ServiceRights.everyLotteryBound
#print axioms ServiceRights.poolingCut
#print axioms ServiceRights.noStrictBandAtSmallOption
#print axioms ServiceRights.discloseForfeitsRent

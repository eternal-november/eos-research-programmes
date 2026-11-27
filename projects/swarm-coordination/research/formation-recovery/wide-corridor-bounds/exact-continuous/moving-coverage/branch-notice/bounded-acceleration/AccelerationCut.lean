import Mathlib
namespace AccelerationCut

noncomputable def cost (a eta v : ℝ) : ℝ := (1-v)^2/(2*a) + eta*v

theorem seam_value_min (a eta k v : ℝ) (ap : 0<a)
    (hk : 1-k ≤ a*eta) (hv : k ≤ v) :
    cost a eta k ≤ cost a eta v := by
  have hd : 0 < 2*a := by linarith
  have hc : 0 ≤ eta-(2-v-k)/(2*a) := by
    have hf : (2-v-k)/(2*a) ≤ eta := (div_le_iff₀ hd).2 (by nlinarith)
    linarith
  have hf : cost a eta v - cost a eta k =
      (v-k)*(eta-(2-v-k)/(2*a)) := by
    unfold cost
    field_simp
    ring
  rw [← sub_nonneg, hf]
  exact mul_nonneg (sub_nonneg.mpr hv) hc

theorem combine (a eta k d x v : ℝ) (ap : 0<a)
    (hk : 1-k ≤ a*eta) (hv : k ≤ v)
    (far : 4 + cost a eta v - cost a eta k + k*eta ≤ x+v*eta)
    (late : x+v*eta ≤ 4+a*(d*d+2*d*eta+eta*eta/2)) :
    k*eta/a+eta^2/2 ≤ (d+eta)^2 := by
  have hc := seam_value_min a eta k v ap hk hv
  have hz : k*eta ≤ a*(d*d+2*d*eta+eta*eta/2) := by linarith
  have he : k*eta/a ≤ d*d+2*d*eta+eta*eta/2 := (div_le_iff₀ ap).2 (by nlinarith)
  nlinarith

#print axioms seam_value_min
#print axioms combine
end AccelerationCut

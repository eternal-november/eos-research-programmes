import Mathlib

namespace PairedRisk

theorem signed_cut (A B c l a w q : ℝ)
    (hd : 0<a*B+w*l) :
    (a*A+w*c)/(a*B+w*l) ≤ q ↔ a*(A-q*B)+w*(c-q*l) ≤ 0 := by
  rw [div_le_iff₀ hd]
  constructor <;> intro h <;> nlinarith only [h]

theorem witnessed_maximum {J : Type} (P : J → ℝ) (j : J) (h : ∀ i, P i ≤ P j)
    (v w : ℝ) (hw : 0 ≤ w) :
    (∀ i, v+w*P i ≤ 0) ↔ v+w*P j ≤ 0 := by
  constructor
  · exact fun hp => hp j
  · intro hv i
    have hx := mul_le_mul_of_nonneg_left (h i) hw
    linarith only [hv,hx]

theorem paired_corner (c l cp floor q : ℝ)
    (hcl : c ≤ l) (hcp : c ≤ cp) (hl : floor ≤ l)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    c-q*l ≤ cp-q*max floor cp := by
  by_cases e : floor ≤ cp
  · rw [max_eq_right e]
    have h₁ := mul_le_mul_of_nonneg_left hcl hq
    have h₂ := mul_le_mul_of_nonneg_right hcp (sub_nonneg.mpr hq1)
    nlinarith only [h₁,h₂]
  · rw [max_eq_left (le_of_not_ge e)]
    have h₁ := mul_le_mul_of_nonneg_left hl hq
    nlinarith only [h₁,hcp]

theorem overlap_mass_bounds (o a b : ℝ)
    (ha : a ≤ o) (hb : b ≤ o) (hab : 0 ≤ a+b-o) :
    max a b ≤ o ∧ o ≤ a+b := by exact ⟨max_le ha hb,by linarith⟩

#print axioms signed_cut
#print axioms witnessed_maximum
#print axioms paired_corner
#print axioms overlap_mass_bounds
end PairedRisk

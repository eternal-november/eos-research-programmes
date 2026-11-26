import Mathlib

namespace AmendmentScope

def outcome (p s x y : ℝ) (late : Bool) : ℝ :=
  p*x + (1-p)*y - s*(if late then y else x)

theorem outcome_mono (p s x y x' y' : ℝ) (hp : s ≤ p) (hq : s ≤ 1-p)
    (hs : 0 ≤ s) (hx : x ≤ x') (hy : y ≤ y') (late : Bool) :
    outcome p s x y late ≤ outcome p s x' y' late := by
  cases late
  · simp only [outcome, Bool.false_eq_true, ite_false]
    have h1 := mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr hp)
    have h2 := mul_le_mul_of_nonneg_left hy (show 0 ≤ 1-p by linarith)
    nlinarith only [h1,h2]
  · simp only [outcome, ite_true]
    have h1 := mul_le_mul_of_nonneg_left hx (show 0 ≤ p by linarith)
    have h2 := mul_le_mul_of_nonneg_left hy (sub_nonneg.mpr hq)
    nlinarith only [h1,h2]

theorem row_exact (cap s x : ℝ) (hs : 0 < s) (hx : x ≤ 1) :
    s*x ≤ cap ↔ x ≤ min 1 (cap/s) := by
  rw [le_min_iff, le_div_iff₀ hs, mul_comm x s]
  exact ⟨fun h => ⟨hx,h⟩, And.right⟩

/-- The residual cap can separate changes on histories masked in the old union. -/
theorem cohort_probe (s : ℝ) (hs : 0 < s) (late : Bool) :
    s * (if late then 0 else 1) ≤ s/2 ↔ late = true := by
  cases late <;> simp <;> linarith

#print axioms outcome_mono
#print axioms row_exact
#print axioms cohort_probe
end AmendmentScope
